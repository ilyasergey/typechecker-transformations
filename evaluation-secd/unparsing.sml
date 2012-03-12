(* Unparsing *)
fun println st = print (st ^ "\n")

local open Syn in
fun unparse_type T_NUM
    = "T_NUM" 
  | unparse_type (T_ARR (t0, t1))
    = "T_ARR (" ^ (unparse_type t0) ^ ", " ^ (unparse_type t1) ^ ")"
  | unparse_type (T_ERROR s)
    = "T_ERROR (" ^ s ^ ")"

and unparse_term (Syn.LIT n)
    = Int.toString n
  | unparse_term (Syn.IDE st)
    = st
  | unparse_term (Syn.LAM (st, t, body))
    = "LAM (" ^ st ^ ", " ^ (unparse_type t) ^ ", " ^ (unparse_term body) ^ ")"
  | unparse_term (Syn.APP (t0, t1))
    = "APP (" ^ (unparse_term t0) ^ ", " ^ (unparse_term t1) ^ ")"

and unparse_bindings bs 
  = "[" ^ (List.foldr 
	       (fn ((st, t), acc) => 
		   st ^ " -> " ^ (unparse_type t) ^ ", " ^ acc) 
	       "" bs) ^ "]"
end
