open Util.Naming
open Ast

type varctx

val empty : varctx
val get_type : varctx -> variable -> expr
val extend : varctx -> variable -> expr -> expr option -> varctx
val initial : varctx
