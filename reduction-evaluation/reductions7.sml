use "syntax.sml";
use "hsyntax.sml";

(* Refunctionalization *)
structure TypeCheck_Refun = 
struct

open Syn TEnv

(*  eval7 : term * (string * typ) list * (typ -> typ) -> typ  *)
fun eval7 (LIT n, gamma, k)
    = k T_NUM
  | eval7 (IDE x, gamma, k)
    = (case TEnv.lookup (x, gamma)
	of NONE
	   => T_ERROR "undeclared identifier"
	 | (SOME v) =>
	   k v)
  | eval7 (LAM (x, t, e), gamma, k)
    = eval7 (e, TEnv.extend (x, t, gamma), 
	  fn v => k (T_ARR (t, v)))      

  | eval7 (APP (e0, e1), gamma, k)
    = eval7 (e0, gamma, 
	  fn t => case t 
		   of T_ARR (t1, t2) 
		      => eval7 (e1, gamma, 
			     fn v1 => 
				if t1 = v1
				then k t2
				else T_ERROR "parameter type mismatch") 
		    | _ => T_ERROR "non-function application")

(*  normalize7 : term -> typ  *)
fun normalize7 t
    = eval7 (t, TEnv.empty, fn x => x)

fun type_check t 
    = normalize7 t
		       
end
