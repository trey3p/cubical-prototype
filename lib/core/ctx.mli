open Ast
open Util.Naming
module Cof = Logic.Cofibration
open Cof
open Cofibctx
open Dimctx
open Varctx
type ctx = dimctx * cofctx * varctx

val dims : ctx -> dimctx
val add_dim : ctx -> variable -> ctx
val valid_formula : ctx -> cofib -> bool
val cof_equiv : ctx -> cofib -> cofib -> bool
val quantify_cof : ctx -> variable -> ctx
val restrict_context : ctx -> cofib -> ctx
val extend_context : ctx -> variable -> expr -> expr option -> ctx
val var_type : ctx -> variable -> expr
val penv : 'a -> 'b list
val initial : ctx
