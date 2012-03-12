use "syntax.sml";
use "hsyntax.sml";

(* Renaming transition functions and flattening configurations *)
structure TypeCheck_Renamed = 
struct

open HSyn TEnv

fun term_to_hterm (IDE s)
    = H_IDE s
  | term_to_hterm (LAM (x, t, e))
    = H_LAM (x, t, term_to_hterm(e))
  | term_to_hterm (LIT i)
    = H_LIT i
  | term_to_hterm (APP (e1, e2))
    = H_APP (term_to_hterm e1, term_to_hterm e2)


datatype context = CTX_MT 
		 | CTX_FUN of context * hterm * bindings
		 | CTX_ARG of typ * context
		 | CTX_ARR of typ * context

datatype result = RESULT of typ
		| WRONG of string

(*  eval5 : hterm * (string * typ) list * context -> result  *)
fun eval5 (H_LIT n, gamma, C)
    = continue5 (C, T_NUM)
  | eval5 (H_IDE x, gamma, C)
    = (case TEnv.lookup (x, gamma)
	of NONE
	   => WRONG "undeclared identifier"
	 | (SOME v) =>
	   continue5 (C, v))
  | eval5 (H_LAM (x, t, e), gamma, C)
    = eval5 (H_TARR (t, e), TEnv.extend (x, t, gamma), C)
  | eval5 (H_APP (t0, t1), gamma, C)
    = eval5 (t0, gamma, CTX_FUN (C, t1, gamma))
  | eval5 (H_TNUM, gamma, C)
    = continue5 (C, T_NUM)
  | eval5 (H_TARR (t, e), gamma, C)
    = eval5 (e, gamma, CTX_ARR (t, C))      

(*  continue5 : context * typ -> result  *)
and continue5 (CTX_MT, v)
    = RESULT v
  | continue5 (CTX_FUN (C, c1, gamma), v0)
    = eval5 (c1, gamma, CTX_ARG (v0, C))
  | continue5 (CTX_ARG (v0, C), v1)
    = apply5 (v0, v1, C)
  | continue5 (CTX_ARR (v0, C), v1)
    = continue5 (C, (T_ARR (v0, v1)))

(*  apply5 : typ * typ * context -> result  *)
and apply5 (T_ARR (t1, t4), v, C)
    = if t1 = v
      then continue5 (C, t4)
      else WRONG "parameter type mismatch"
  | apply5 (t, v, C)
    = WRONG "non-function application"


(*  normalize5 : term -> result  *)
fun normalize5 t
    = eval5 (term_to_hterm t, TEnv.empty, CTX_MT)

(*  type_check : term -> typ  *)
fun type_check t 
    = case normalize5 t 
       of (RESULT v)
	  => v
	| WRONG s 
	  => T_ERROR s
		       
end
