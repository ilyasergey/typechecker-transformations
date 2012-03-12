use "syntax.sml";
use "hsyntax.sml";

structure TypeCheck_Reduct = 
struct

open HSyn TEnv

fun type_to_closure T_NUM
    = CLO_NUM
  | type_to_closure (v as T_ARR (t1, t2))
    = CLO_ARR_TYPE v

fun term_to_hterm (IDE s)
    = H_IDE s
  | term_to_hterm (LAM (x, t, e))
    = H_LAM (x, t, term_to_hterm(e))
  | term_to_hterm (LIT i)
    = H_LIT i
  | term_to_hterm (APP (e1, e2))
    = H_APP (term_to_hterm e1, term_to_hterm e2)


datatype potential_redex = PR_NUM
			 | PR_LAM of string * typ * hterm * bindings
			 | PR_APP of typ * typ
			 | PR_ARR of typ * typ
			 | PR_IDE of string * bindings
			 | PR_PROP of hterm * hterm * bindings

datatype contractum_or_error = CONTRACTUM of closure
			     | ERROR of string
(*  contract : potential_redex -> contractum_or_error  *)
fun contract PR_NUM
    = CONTRACTUM CLO_NUM
  | contract (PR_ARR (t1, t2))
    = CONTRACTUM (type_to_closure (T_ARR (t1, t2)))
  | contract (PR_IDE (x, bs)) 
    = (case TEnv.lookup (x, bs)
	of NONE => ERROR "undeclared identifier"
	 | (SOME v) => CONTRACTUM (type_to_closure v))
  | contract (PR_LAM (x, t, e, bs))
    = CONTRACTUM (CLO_GND (H_TARR (t, e), TEnv.extend (x, t, bs)))
  | contract (PR_APP (T_ARR (t1, t2), v))
    = if t1 = v
      then CONTRACTUM (type_to_closure t2)
      else ERROR "parameter type mismatch"
  | contract (PR_PROP (t0, t1, bs))
    = CONTRACTUM (CLO_APP (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (PR_APP (t1, t2)) 
    = ERROR "non-function application"

datatype type_or_decomposition = VAL of typ
			       | DEC of potential_redex * hctx

(*  decompose_closure : closure * hctx -> type_or_decomposition *)
fun decompose_closure (CLO_NUM, C)
    = decompose_context (C, T_NUM)
  | decompose_closure (CLO_ARR_TYPE v, C)
    = decompose_context (C, v)
  | decompose_closure (CLO_GND (H_LIT n, bs), C)
    = decompose_context (C, T_NUM)
  | decompose_closure (CLO_GND (H_IDE x, bs), C)
    = DEC (PR_IDE (x, bs), C)
  | decompose_closure (CLO_GND (H_LAM (x, t, e), bs), C)
    = DEC (PR_LAM (x, t, e, bs), C)
  | decompose_closure (CLO_GND (H_APP (t0, t1), bs), C)
    = DEC (PR_PROP (t0, t1, bs), C)
  | decompose_closure (CLO_GND (H_TNUM, bs), C)
    = decompose_context (C, T_NUM)
  | decompose_closure (CLO_GND (H_TARR (t, e), bs), C)
    = decompose_closure (CLO_GND (e, bs), 
			 CTX_ARR (t, C))      
  | decompose_closure (CLO_APP (c0, c1), C)
    = decompose_closure (c0, CTX_FUN (C, c1))
  | decompose_closure (CLO_ARR (v, c), C)
    = decompose_closure (c, CTX_ARR (v, C))
      
(*  decompose_context : hctx * typ -> type_or_decomposition *)
and decompose_context (CTX_MT, v)
    = VAL v
  | decompose_context (CTX_FUN (C, c1), v0)
    = decompose_closure (c1, CTX_ARG (v0, C))
  | decompose_context (CTX_ARG (v0, C), v1)
    = DEC (PR_APP (v0, v1), C)
  | decompose_context (CTX_ARR (v0, C), v1)
    = DEC (PR_ARR (v0, v1), C)

(*  decompose : closure -> type_or_decomposition *)
fun decompose c 
  = decompose_closure (c, CTX_MT)

(*  recompose : hctx * closure -> closure *)
fun recompose (CTX_MT, c)
    = c
  | recompose (CTX_FUN (C, c1), c0)
    = recompose (C, CLO_APP (c0, c1))
  | recompose (CTX_ARG (v0, C), c1)
    = recompose (C, CLO_APP (type_to_closure v0, c1))
  | recompose (CTX_ARR (v0, C), c1) 
    = recompose (C, CLO_ARR (v0, c1))

datatype result = RESULT of typ
		| WRONG of string

(*  iterate : type_or_decomposition -> result *)
fun iterate (VAL v)
    = RESULT v
  | iterate (DEC (pr, C))
    = (case contract pr 
	of (CONTRACTUM c')
	   => iterate (decompose (recompose (C, c')))
	 | (ERROR s)
	   => WRONG s)

(*  normalize : term -> result *)
fun normalize t
    = iterate (decompose (CLO_GND (term_to_hterm t, TEnv.empty)))

(*  type_check : term -> typ *)
fun type_check t 
    = case normalize t 
       of (RESULT v)
	  => v
	| WRONG s 
	  => T_ERROR s	       
end
