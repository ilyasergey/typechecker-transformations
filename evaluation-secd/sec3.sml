use "syntax.sml";

(* Defunctionalization *)

structure TypeCheck_Defun =
struct 

open Syn

datatype cont = CONT_MT
	      | CONT_LAM of typ * cont *  typ list       (* arg_type cont, data stack *)
	      | CONT_FUN of cont * term * typ TEnv.gamma (* cont, argument, environment *)
	      | CONT_ARG of Syn.typ * Syn.typ * cont	 (* arg_type, result_type, cont *)


(* check3 : term * typ list * (string * typ) list * cont -> typ list *)
fun check3 (LIT n, s, e, C)
    = continue3 (C, (T_NUM :: s))
  | check3 (IDE x, s, e, C)
    = continue3 (C, 
        (case TEnv.lookup(x, e)
           of (SOME t) => t :: s
            | NONE     => (T_ERROR "undeclared identifier") :: nil))
  | check3 (LAM (x, arg_type, body), s, e, C)
    = check3 (body, nil, (TEnv.extend (x, arg_type, e)), 
	      CONT_LAM (arg_type, C, s))
  | check3 (APP (e1, e2), s, e, C)
    = check3 (e1, s, e, CONT_FUN (C, e2, e))

(* continue3 : cont * typ list -> typ list *)
and continue3 (CONT_MT, s)
    = s
  | continue3 (CONT_LAM (arg_type, C, s), (body_type :: s0))
    = continue3 (C, T_ARR (arg_type, body_type) :: s)
  | continue3 (CONT_FUN (C, e2, e), s0 as (T_ARR (t1, t2) :: _))
    = check3 (e2, s0, e, CONT_ARG (t1, t2, C))
  | continue3 (CONT_FUN (C, e2, e), _)
    = (T_ERROR "non-function application") :: nil
  | continue3 (CONT_ARG (t1, t2, C), (arg_type :: x :: s1))
    = if arg_type = t1
      then continue3 (C, t2 :: s1)
      else (T_ERROR "parameter type mismatch") :: nil
           
(* type_check : term -> typ *)
and type_check t
  = let val (v :: s) =  check3 (t, nil, TEnv.empty, CONT_MT)
    in v end
    
end
