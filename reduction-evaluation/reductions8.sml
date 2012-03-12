use "syntax.sml";
use "hsyntax.sml";

(* Back to direct style *)
structure TypeCheck_Direct = 
struct

open Syn TEnv

val callcc = SMLofNJ.Cont.callcc
val throw = SMLofNJ.Cont.throw

(*  normalize8 : term -> typ *)
fun normalize8 t
  = callcc (fn top => 
  let fun eval8 (LIT n, gamma)
        = T_NUM
     | eval8 (IDE x, gamma)
         = (case TEnv.lookup (x, gamma)
	     of NONE
		=> throw top (T_ERROR "undeclared identifier")
	      | (SOME v) =>
		v)
     | eval8 (LAM (x, t, e), gamma)
       = T_ARR (t, eval8 (e, TEnv.extend (x, t, gamma)))
     | eval8 (APP (e0, e1), gamma)
       = let val t = eval8 (e0, gamma)
	     val v1 = eval8 (e1, gamma)
	 in (case t 
	      of T_ARR (t1, t2) 
		 => if t1 = v1
		    then t2
		    else throw top (T_ERROR "parameter type mismatch")
	       | _ => throw top (T_ERROR "non-function application"))
	 end
  in eval8 (t, TEnv.empty)
  end) 

(*  type_check : term -> typ *)
fun type_check t 
    = normalize8 t 
		       
end
