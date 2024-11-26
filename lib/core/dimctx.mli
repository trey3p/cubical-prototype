open Util.Naming
type dimctx

val empty : dimctx
val weaken : dimctx -> variable -> dimctx
val check : dimctx -> variable -> bool
val make : Util.Naming.variable list -> dimctx
val initial : dimctx
