(* Terms and Types*)
structure Syn = 
struct 
datatype typ = T_NUM
	     | T_ARR of typ * typ
	     | T_ERROR of string

datatype term = LIT of int
	      | IDE of string
	      | LAM of string * typ * term (* Lambda's variable is annotated with a type *)
	      | APP of term * term

end

(* Typing Environments *)
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

(* Test term *)
local open Syn 
in 
val term1 = LAM ("z", T_ARR(T_NUM, T_NUM), APP (IDE "z", LIT 42))
val term2 = LAM ("y", T_ARR (T_NUM, T_NUM), IDE "y")
val term3 = LAM("x", T_NUM, IDE "x")

val term4 = APP(term1, APP (term2, term3))
end
