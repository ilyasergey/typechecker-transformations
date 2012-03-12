use "syntax.sml";

(* Now embedded match exceptions are used *)
(* Examples: *)

(* 1. Non-arrow type *)
(*  type_check4 (Syn.APP (Syn.LIT 42, Syn.LAM ("x", Syn.T_NUM, Syn.IDE "x"))); *)

(* 2. Unbound identifier *)
(* type_check4 (Syn.LAM ("x", Syn.T_NUM, Syn.IDE "y")); *)

(* 3. Unmatched parameter and argument expressions type *)
(* type_check4 (Syn.APP (term3, term2)); *)

(* ----------------------------------------------------------- *)
(* Context parameters are rearranged *)
(* Environment is removed from contexts, now is a parameter *)

structure TypeCheck_Env =
struct 
open Syn

datatype cont = CONT_MT
	       | CONT_LAM of typ * typ list * cont
	       | CONT_FUN of term * cont
	       | CONT_ARG of typ * typ* cont

fun check4 (LIT n, s, e, C)
    = continue4 (C, (T_NUM :: s), e)
  | check4 (IDE x, s, e, C)
    = continue4 (C, case TEnv.lookup(x, e) of (SOME t) => t :: s, e)
  | check4 (LAM (x, arg_type, body), s, e, C)
    = check4 (body, nil, TEnv.extend (x, arg_type, e), CONT_LAM (arg_type, s, C))
  | check4 (APP (e1, e2), s, e, C)
    = check4 (e1, s, e, CONT_FUN (e2, C))


and continue4 (CONT_MT, s, e)
    = s
  | continue4 (CONT_LAM (arg_type, s, C), (body_type :: s0), e)
    = continue4 (C, T_ARR (arg_type, body_type) :: s, e)
  | continue4 (CONT_FUN (e2, C), s0 as (T_ARR (t1, t2) :: _), e)
    = check4 (e2, s0, e, CONT_ARG (t1, t2, C))
  | continue4 (CONT_ARG (arg_type, result_type, C), (v2 :: x :: s1), e)
    = if v2 = arg_type 
      then continue4 (C, result_type :: s1, e)
      else (T_ERROR "parameter type mismatch") :: nil
            
and type_check t
  = let val (v :: s) =  check4 (t, nil, TEnv.empty, CONT_MT)
    in v end
    
end
