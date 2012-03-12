(* Hybrid syntax *)
structure HSyn =
struct
open Syn TEnv

datatype hterm = H_LIT of int
	       | H_IDE of string
	       | H_LAM of string * typ * hterm
	       | H_APP of hterm * hterm
	       | H_TARR of typ * hterm
	       | H_TNUM 

datatype closure = CLO_NUM
		 | CLO_GND of hterm * bindings
		 | CLO_APP of closure * closure
		 | CLO_ARR of typ * closure
		 | CLO_ARR_TYPE of typ
withtype bindings = typ TEnv.gamma

datatype hctx = CTX_MT 
	      | CTX_FUN of hctx * closure
	      | CTX_ARG of typ * hctx
	      | CTX_ARR of typ * hctx
end
