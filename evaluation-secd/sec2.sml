use "syntax.sml";

(* CPS transform *)
structure TypeCheck_CPS =
struct
open Syn 

(* check2 : term * typ list * typ gamma * 
                 (typ list -> typ list)
                 -> typ list 
*)
fun check2 (LIT n, s, e, k)
    = k (T_NUM :: s)
  | check2 (IDE x, s, e, k)
    = k (case TEnv.lookup(x, e)
           of (SOME t) => t :: s
            | NONE     => (T_ERROR "undeclared identifier") :: nil)
  | check2 (LAM (x, arg_type, body), s, e, k)
    = check2 (body, nil, (TEnv.extend (x, arg_type, e)),
	   fn (body_type :: s0) =>
	      k (T_ARR (arg_type, body_type) :: s))
  | check2 (APP (e1, e2), s, e, k)
    = check2 (e1, nil, e,
	fn s0 => 
           case s0 
             of (T_ARR (t1, t2) :: _) =>       	   
	        check2 (e2, s0, e, 
	          fn (arg_type :: x :: _) =>
		     if arg_type = t1
		     then k (t2 :: s)
		     else (T_ERROR "parameter type mismatch") :: nil)
              | _ => (T_ERROR "non-function application") :: nil)

(* type_check : term -> typ *)
and type_check t
  = let val (v :: s) =  check2 (t, nil, TEnv.empty, fn x => x)
    in v end
    
end
