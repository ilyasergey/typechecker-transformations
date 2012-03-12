use "syntax.sml";
use "hsyntax.sml";

(*  Compressing hybrid syntax elements and switching domains  *)
structure TypeCheck_HybridCompress = 
struct

open HSyn TEnv

datatype result = RESULT of typ
		| WRONG of string

datatype context = CTX_MT 
		 | CTX_FUN of context * term * bindings
		 | CTX_ARG of typ * context
		 | CTX_ARR of typ * context
withtype bindings = typ gamma

(*  term * (string * typ) list * context -> typ  *)
fun eval6 (LIT n, gamma, C)
    = continue6 (C, T_NUM)
  | eval6 (IDE x, gamma, C)
    = (case TEnv.lookup (x, gamma)
	of NONE
	   => T_ERROR "undeclared identifier"
	 | (SOME v) =>
	   continue6 (C, v))
  | eval6 (LAM (x, t, e), gamma, C)
    = eval6 (e, TEnv.extend (x, t, gamma), 
	      CTX_ARR (t, C))      
  | eval6 (APP (t0, t1), gamma, C)
    = eval6 (t0, gamma, CTX_FUN (C, t1, gamma))

(*  continue6 : context * typ -> typ  *)
and continue6 (CTX_MT, v)
    = v
  | continue6 (CTX_FUN (C, c1, gamma), v0)
    = eval6 (c1, gamma, CTX_ARG (v0, C))
  | continue6 (CTX_ARG (v0, C), v1)
    = apply6 (v0, v1, C)
  | continue6 (CTX_ARR (v0, C), v1)
    = continue6 (C, (T_ARR (v0, v1)))

(*  apply6 : typ * typ * context -> typ  *)
and apply6 (T_ARR (t1, t4), v, C)
    = if t1 = v
      then continue6 (C, t4)
      else T_ERROR "parameter type mismatch"
  | apply6 (t, v, C)
    = T_ERROR "non-function application"

(*  term -> typ  *)
fun normalize6 t
    = eval6 (t, TEnv.empty, CTX_MT)

fun type_check t 
    = normalize6 t 
		       
end
