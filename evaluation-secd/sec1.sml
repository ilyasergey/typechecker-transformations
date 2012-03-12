use "syntax.sml";

(* ------------------------------------------------------ *)
(* Refactor to stack-threading callee-save evaluator *)
(* There is a stack for types (data and result stack) *)
(* ------------------------------------------------------ *)

structure TypeCheck_CalleeSave =
struct

open Syn 

exception TYPING_ERROR of string

(* check1 : term * typ list * (string * typ) list -> typ list *)
fun check1 (LIT n, s, e) 
    = T_NUM :: s
  | check1 (IDE x, s, e)
    = (case TEnv.lookup(x, e) of (SOME t) => t :: s)
  | check1 (LAM (x, arg_type, body), s, e)
    = let val (body_type :: _) = 
	      check1 (body, nil, (TEnv.extend (x, arg_type, e)))
      in T_ARR (arg_type, body_type) :: s
      end
  | check1 (APP (e1, e2), s, e)
    = let val s0 as (T_ARR (t1, t2) :: _) = check1 (e1, nil, e) 
	  val (arg_type :: x :: _) = check1 (e2, s0, e) 
      in if arg_type = t1
	 then t2 :: s
	 else raise (TYPING_ERROR "parameter type mismatch")
      end
      
(* type_check : term -> typ *)
and type_check t 
  = let val (v :: s) =  check1 (t, nil, TEnv.empty)
    in v end
    
end
