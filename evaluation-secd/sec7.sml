(* ---------------------------------------------------------------------- *)
(* Refactoring into a small-step abstract machine *)

structure TypeCheck_SmallStep = 
struct

open Syn

exception TYPING_ERROR of string

(* elements of control stack *)
datatype control_element = C_ARG of typ * typ
			 | C_FUN of term 
			 | C_LAM of typ * typ list
			 | C_TERM of term			            	


type state = Syn.typ list * (string * Syn.typ) list * 
	     control_element list

(* step state -> state *)
fun step6 (s, e, C_TERM (LIT n) :: C)
    = (T_NUM :: s, e, C)
  | step6 (s, e, C_TERM (IDE x) :: C)
    = (case TEnv.lookup(x, e) 
         of (SOME t) => (t :: s, e, C)
          | _        => raise (TYPING_ERROR "undeclared identifier"))  
  | step6 (s, e, C_TERM (LAM (x, arg_type, body)) :: C)
    = (nil, TEnv.extend (x, arg_type, e), 
       C_TERM body :: C_LAM (arg_type, s) :: C)
  | step6 (s, e, C_TERM (APP (e1, e2)) :: C)
    = (s, e, C_TERM e1 :: C_FUN e2 :: C) 
  | step6 ((body_type :: s0), e, C_LAM (arg_type, s) :: C)
    = (T_ARR (arg_type, body_type) :: s, e, C)
  | step6 (s0 as (T_ARR (t1, t2) :: _), e, C_FUN e2 :: C)
    = (s0, e, C_TERM e2 :: C_ARG (t1, t2) :: C)
  | step6 (_, e, C_FUN e2 :: C)
    = raise (TYPING_ERROR "non-function application")
  | step6 (v2 :: x :: s1, e, C_ARG (arg_type, result_type) :: C)
    = if v2 = arg_type 
      then (result_type :: s1, e, C)
      else raise (TYPING_ERROR "parameter type mismatch")

(* iterate6: state -> typ *)
fun iterate6 (v :: s, _, nil)
    = v
  | iterate6 state
    = iterate6 (step6 state)

(* type_check : term -> typ *)
fun type_check term
  = iterate6  (nil, TEnv.empty, C_TERM term :: nil)
    
end
