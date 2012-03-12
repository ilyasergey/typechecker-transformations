use "syntax.sml";
use "hsyntax.sml";

(* Lightweight Fusion *)
(* From small-step to big-step abstract machine *)
structure TypeCheck_Fusion = 
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


datatype type_or_decomposition = VAL of typ
			       | DEC of potential_redex * hctx

datatype result = RESULT of typ
		| WRONG of string

(*  refocus3_closure : closure * hctx -> resul t *)
fun refocus3_closure (CLO_NUM, C)
    = refocus3_context (C, T_NUM)
  | refocus3_closure (CLO_ARR_TYPE v, C)
    = refocus3_context (C, v)
  | refocus3_closure (CLO_GND (H_LIT n, bs), C)
    = refocus3_context (C, T_NUM)
  | refocus3_closure (CLO_GND (H_IDE x, bs), C)
    = iterate3 (DEC (PR_IDE (x, bs), C))
  | refocus3_closure (CLO_GND (H_LAM (x, t, e), bs), C)
    = iterate3 (DEC (PR_LAM (x, t, e, bs), C))
  | refocus3_closure (CLO_GND (H_APP (t0, t1), bs), C)
    = iterate3 (DEC (PR_PROP (t0, t1, bs), C))
  | refocus3_closure (CLO_GND (H_TNUM, bs), C)
    = refocus3_context (C, T_NUM)
  | refocus3_closure (CLO_GND (H_TARR (t, e), bs), C)
    = refocus3_closure (CLO_GND (e, bs), 
			CTX_ARR (t, C))      
  | refocus3_closure (CLO_APP (c0, c1), C)
    = refocus3_closure (c0, CTX_FUN (C, c1))
  | refocus3_closure (CLO_ARR (v, c), C)
    = refocus3_closure (c, CTX_ARR (v, C))


(*  refocus3_context : hctx * typ -> result  *)
and refocus3_context (CTX_MT, v)
    = iterate3 (VAL v)
  | refocus3_context (CTX_FUN (C, c1), v0)
    = refocus3_closure (c1, CTX_ARG (v0, C))
  | refocus3_context (CTX_ARG (v0, C), v1)
    = iterate3 (DEC (PR_APP (v0, v1), C))
  | refocus3_context (CTX_ARR (v0, C), v1)
    = iterate3 (DEC (PR_ARR (v0, v1), C))

(*  iterate3 : type_or_decomposition -> result  *)
and iterate3 (VAL v)
    = RESULT v
  | iterate3 (DEC (PR_NUM, C))
    = refocus3_closure (CLO_NUM, C)
  | iterate3 (DEC (PR_ARR (t1, t3), C))
    = refocus3_closure (type_to_closure 
		(T_ARR (t1, t3)), C)
  | iterate3 (DEC (PR_IDE (x, bs), C))
    = (case TEnv.lookup (x, bs)
	of NONE
	   => WRONG "undeclared identifier"
	 | (SOME v) =>
	   refocus3_closure (type_to_closure v, C))
  | iterate3 (DEC (PR_LAM (x, t, e, bs), C))
    = refocus3_closure (CLO_GND (H_TARR (t, e),
		  TEnv.extend (x, t, bs)), C)
  | iterate3 (DEC (PR_APP (T_ARR (t1, t3), v), C))
    = if t1 = v
      then refocus3_closure ((type_to_closure t3), C)
      else WRONG "parameter type mismatch"
  | iterate3 (DEC (PR_PROP (t0, t1, bs), C))
    = refocus3_closure (CLO_APP (CLO_GND (t0, bs), 
				 CLO_GND (t1, bs)), C)
  | iterate3 (DEC (PR_APP (t1, t2), C))
    = WRONG "non-function application"


(*  normalize3 : term -> result  *)
fun normalize3 t
    = refocus3_closure (CLO_GND (term_to_hterm t, 
				 TEnv.empty), CTX_MT)

fun type_check t 
    = case normalize3 t 
       of (RESULT v)
	  => v
	| WRONG s 
	  => T_ERROR s
		       
end
