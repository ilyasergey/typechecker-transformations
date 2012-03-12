structure Syn = 
struct 
datatype typ = T_NUM
	     | T_ARR of typ * typ
	     | T_ERROR of string

datatype term = LIT of int
	      | IDE of string
	      | LAM of string * typ * term
	      | APP of term * term

end

structure TEnv =
struct
type 'a gamma = (string * 'a) list

val empty = []

fun extend (x, t, gamma) = (x, t) :: gamma 

fun lookup (x, gamma) 
    = let fun search []
	      = NONE
	    | search ((x', t) :: gamma)
	      = if x = x' then SOME t else search gamma
      in search gamma
      end
end

local open Syn 
in 

(*  T_ARR (T_ARR (T_NUM,T_NUM),T_NUM)  *)
val term1 = LAM ("z", T_ARR(T_NUM, T_NUM), APP (IDE "z", LIT 42))

(*  T_ARR (T_ARR (T_NUM,T_NUM),T_ARR (T_NUM,T_NUM))  *)
val term2 = LAM ("y", T_ARR (T_NUM, T_NUM), IDE "y")

(*   T_ARR (T_NUM,T_NUM)  *)
val term3 = LAM("x", T_NUM, IDE "x")

(*  T_NUM  *)
val term4 = APP(term1, APP (term2, term3))
end
