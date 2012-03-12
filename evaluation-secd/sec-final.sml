(* Further steps in refactoring evaluation function for type checker into a SEC machine *)


(* -------------------------------------------------------------------- *)
(* Start from check 7 *)
(* Disentangle SEC machine into several transition funcitons 
   with different induction variables *)

local open Syn in

(* ------------------------------------------------------------------------------------ *)
(* now not need in it *)
fun check9 (s, e, C_TERM (LIT n) :: C) (* run_t *)
    = check9 (T_NUM :: s, e, C)
  | check9 (s, e, C_TERM (IDE x) :: C) (* run_t *)
    = check9 (case TEnv.lookup(x, e) of (SOME t) => t :: s, e, C) (* run_t *)
  | check9 (s, e, C_TERM (LAM (x, arg_type, body)) :: C)
    = check9 (nil, TEnv.extend (x, arg_type, e), C_TERM body :: C_LAM (arg_type, s) :: C)
  | check9 (s, e, C_TERM (APP (e1, e2)) :: C) (* run_t *)
    = check9 (s, e, C_TERM e1 :: C_FUN e2 :: C) 

  | check9 (body_type :: s0, e, C_LAM (arg_type, s) :: C) (* run_s *)
    = check9 (T_ARR (arg_type, body_type) :: s, e, C)
  | check9 (s0 as (T_ARR (t1, t2) :: _), e, C_FUN e2 :: C) (* run_S *)
    = check9 (s0, e, C_TERM e2 :: C_ARG :: C)
  | check9 (v2 :: T_ARR (arg_type, result_type) :: s1, e, C_ARG :: C) (* run_s *)
    = if v2 = arg_type 
      then check9 (result_type :: s1, e, C)
      else raise (TYPING_ERROR "Function parameter type does not match argument type")
  | check9 (s, e, nil)
    = s
(* ------------------------------------------------------------------------------------ *)
(* C_TERM is also removed since it's useless now *)

(* run_t : term * S * E * C -> value *)
fun run_t (s, e, LIT n, C)
    = run_c (T_NUM :: s, e, C)
  | run_t (s, e, IDE x, C)
    = run_c (case TEnv.lookup(x, e) of (SOME t) => t :: s, e, C)
  | run_t (s, e, LAM (x, arg_type, body), C)
    = run_t (nil, TEnv.extend (x, arg_type, e), body, C_LAM (arg_type, s) :: C)
  | run_t (s, e, APP (e1, e2), C)
    = run_t (s, e, e1, C_FUN e2 :: C) 

(* dispatches by the control stack *)
and run_c (s, e, C_LAM (arg_type, s1) :: C)
    = run_s_lam (s, e, C,   arg_type, s1) (* residual: arg_type, s1 *)
  | run_c (s, e, C_FUN e2 :: C)		  
    = run_s_fun (s, e, C,   e2)           (* residual: e2 *)
  | run_c (s, e, C_ARG :: C)
    = run_s_arg (s, e, C)
  | run_c (s, e, nil)
    = s

(* dispatch by s *)
and run_s_lam (body_type :: s0, e, C,     arg_type, s)
    = run_c (T_ARR (arg_type, body_type) :: s, e, C)
and run_s_fun (s0 as (T_ARR (t1, t2) :: _), e, C,    e2)
    = run_t (s0, e, e2, C_ARG :: C)
and run_s_arg (v2 :: T_ARR (arg_type, result_type) :: s1, e, C)
  = if v2 = arg_type 
    then run_c (result_type :: s1, e, C)
    else raise (TYPING_ERROR "Function parameter type does not match argument type")
            
and type_check9 t
  = let val (v :: s) =  run_t (nil, TEnv.empty, t, nil)
    in v end
    
end

(* Refunctionalization *)

local open Syn in

(* run_t1 : term * S * E * C -> value *)
fun run_t1 (s, e, LIT n, C)
    = C (T_NUM :: s, e)
  | run_t1 (s, e, IDE x, C)
    = C (case TEnv.lookup(x, e) of (SOME t) => t :: s, e)
  | run_t1 (s, e, LAM (x, arg_type, body), C)
    = run_t1 (nil, TEnv.extend (x, arg_type, e), body, 
	   fn (s', e) => run_s_lam1 (s', e, C, arg_type, s))
  | run_t1 (s, e, APP (e1, e2), C)
    = run_t1 (s, e, e1, fn (s, e) => run_s_fun1 (s, e, C, e2)) 

(* dispatch by s *)
and run_s_lam1 (body_type :: s0, e, C,     arg_type, s)
    = C (T_ARR (arg_type, body_type) :: s, e)
and run_s_fun1 (s0 as (T_ARR (t1, t2) :: _), e, C,    e2)
    = run_t1 (s0, e, e2, fn (s, e) => run_s_arg1 (s, e, C))
and run_s_arg1 (v2 :: T_ARR (arg_type, result_type) :: s1, e, C)
  = if v2 = arg_type 
    then C (result_type :: s1, e)
    else raise (TYPING_ERROR "Function parameter type does not match argument type")
            
and type_check9 t
  = let val (v :: s) =  run_t1 (nil, TEnv.empty, t, fn (s, e) => s)
    in v end
    
end
