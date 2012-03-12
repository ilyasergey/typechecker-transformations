use "syntax.sml";
use "hsyntax.sml";

(* Compressing Corridor transitions *)
structure TypeCheck_Compress = 
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


datatype result = RESULT of typ
		| WRONG of string

fun refocus4_closure (CLO_GND (H_LIT n, bs), C)
    = refocus4_context (C, T_NUM)
  | refocus4_closure (CLO_GND (H_IDE x, bs), C)
    = (case TEnv.lookup (x, bs)
	of NONE
	   => WRONG "undeclared identifier"
	 | (SOME v) =>
	   refocus4_context (C, v))
  | refocus4_closure (CLO_GND (H_LAM (x, t, e), bs), C)
    = refocus4_closure (CLO_GND (H_TARR (t, e),
				 TEnv.extend (x, t, bs)), C)
  | refocus4_closure (CLO_GND (H_APP (t0, t1), bs), C)
    = refocus4_closure (CLO_GND (t0, bs), CTX_FUN (C, CLO_GND (t1, bs)))
  | refocus4_closure (CLO_GND (H_TNUM, bs), C)
    = refocus4_context (C, T_NUM)
  | refocus4_closure (CLO_GND (H_TARR (t, e), bs), C)
    = refocus4_closure (CLO_GND (e, bs), CTX_ARR (t, C))

and refocus4_context (CTX_MT, v)
    = RESULT v
  | refocus4_context (CTX_FUN (C, c1), v0)
    = refocus4_closure (c1, CTX_ARG (v0, C))
  | refocus4_context (CTX_ARG (v0, C), v1)
    = iterate4 (v0, v1, C)
  | refocus4_context (CTX_ARR (v0, C), v1)
    = refocus4_context (C, (T_ARR (v0, v1)))

and iterate4 (T_ARR (t1, t4), v, C)
    = if t1 = v
      then refocus4_context (C, t4)
      else WRONG "parameter type mismatch"
  | iterate4 (t, v, C)
    = WRONG "non-function application"


fun normalize1 t
    = refocus4_closure (CLO_GND (term_to_hterm t, TEnv.empty), CTX_MT)

fun type_check t 
    = case normalize1 t 
       of (RESULT v)
	  => v
	| WRONG s 
	  => T_ERROR s
		       
end
