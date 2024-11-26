(* Data type for typing context and associated functions *)
open Ast
open Util.Naming
module Cof = Logic.Cofibration
open Cof
open Cofibctx
open Dimctx
open Varctx

type ctx = dimctx * cofctx * varctx

(* Dimension Context *)
let dims (context : ctx) : dimctx =
 let (dims, _, _) = context in dims

let add_dim (context : ctx) (v : variable) : ctx =
  let (dims, x, y) = context in
    ((weaken dims v), x, y)

(* Cofibration Formula Context *)

let valid_formula ((_, phi, _) : ctx) (alpha : cofib) : bool =
  (valid phi alpha)

let cof_equiv (context : ctx) (alpha : cofib) (beta : cofib) : bool =
  let (_, phi, _) = context in
  (equiv phi alpha beta)

let quantify_cof (context : ctx) (x : variable) : ctx =
  let (d, phi, v) = context in
  (d, (add_param phi x), v)

let restrict_context (context : ctx) (alpha : cofib): ctx =
  let (d, x, v) = context in
  (d, (restrict x alpha), v)

let extend_context (context : ctx) (v : variable) (ty : expr)  (def : expr option): ctx =
  let (d, x, vars) = context in
  (d, x, (extend vars v ty def))

let var_type (context : ctx) (v : variable) : expr =
  let (_, _, vars) = context in
  (get_type vars v)

let penv _ = []
let initial : dimctx * cofctx * varctx = (Dimctx.initial, Cofibctx.initial, Varctx.initial)
