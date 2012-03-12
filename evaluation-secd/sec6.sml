use "syntax.sml";

(* ------------------------------------------------------------------- *)
(* Merging check and continue functions *)
structure TypeCheck_BigStep =
struct
open Syn

datatype control_element = C_ARG of typ * typ 
			 | C_FUN of term 
			 | C_LAM of typ * typ list 
			 | C_TERM of term			            

(* check5 : typ list * (string * typ) list * control_element list
                 -> typ list *)
fun check5 (s, e, C_TERM (LIT n) :: C)
    = check5 (T_NUM :: s, e, C)
  | check5 (s, e, C_TERM (IDE x) :: C)
    = check5 (case TEnv.lookup(x, e) 
	       of (SOME t) => t :: s, e, C)
  | check5 (s, e, C_TERM (LAM (x, arg_type, body)) :: C)
    = check5 (nil, TEnv.extend (x, arg_type, e),
	      C_TERM body :: C_LAM (arg_type, s) :: C)
  | check5 (s, e, C_TERM (APP (e1, e2)) :: C)
    = check5 (s, e, C_TERM e1 :: C_FUN e2 :: C) 
  | check5 ((body_type :: s0), e, C_LAM (arg_type, s) :: C)
    = check5 (T_ARR (arg_type, body_type) :: s, e, C)
  | check5 (s0 as (T_ARR (t1, t2) :: _), e, C_FUN e2 :: C)
    = check5 (s0, e, C_TERM e2 :: C_ARG (t1, t2) :: C)
  | check5 (v2 :: x :: s1, e, 
	    C_ARG (arg_type, result_type) :: C)
    = if v2 = arg_type 
      then check5 (result_type :: s1, e, C)
      else T_ERROR "parameter type mismatch" :: nil
  | check5 (s, e, nil)
    = s

(* type_check : term -> typ *)
and type_check t
  = let val (v :: s) =  check5 (nil, TEnv.empty, C_TERM t :: nil)
    in v end
    
end
