module Cof = Logic.Cofibration
type cofctx

val add_param : cofctx -> Util.Naming.variable -> cofctx
val restrict : cofctx -> Cof.cofib -> cofctx
val valid : cofctx -> Cof.cofib -> bool
val equiv : cofctx -> Cof.cofib -> Cof.cofib -> bool
val make : Cof.cofib -> Util.Naming.variable list -> cofctx
val split : cofctx -> Cof.cofib * Util.Naming.variable list
val combine : cofctx -> cofctx -> cofctx
val initial : cofctx
