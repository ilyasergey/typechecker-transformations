use "syntax.sml";

structure TypeCheck =
struct
open Syn 

exception TYPING_ERROR of string

(* check0 : term * (string * typ) list -> typ *)
fun check0 (LIT n, gamma)
    = T_NUM
  | check0 (IDE x, gamma)
    = (case TEnv.lookup(x, gamma)
         of (SOME t) => t
          | NONE     => raise (TYPING_ERROR "undeclared identifier"))
  | check0 (LAM (x, arg_type, body), gamma)
    = let val body_type = check0 (body, 
	  (TEnv.extend (x, arg_type, gamma)))
      in T_ARR (arg_type, body_type)
      end
  | check0 (APP (e1, e2), gamma)
    = case check0 (e1, gamma) 
        of T_ARR (t1, t2) => 
 	  let val arg_type = check0 (e2, gamma)
          in  if arg_type = t1
  	      then t2
  	      else raise (TYPING_ERROR "parameter type mismatch")
          end
        |  _ => raise (TYPING_ERROR "non-function application") 

(* type_check : term -> typ *)
and type_check t = check0 (t, TEnv.empty)

end




