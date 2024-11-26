module Cof = Logic.Cofibration
open Cof
open Util.Naming


type cofctx = Cof.cofib * variable list

let add_param ((phi, params) : cofctx) (x : variable) : cofctx =
    (phi, x::params)

let restrict ((phi, params) : cofctx) (alpha : Cof.cofib) : cofctx =
  (And(phi, alpha), params)


let valid ((phi, params) : cofctx) (alpha : Cof.cofib) : bool =
  (entailment (phi, params) alpha)

let equiv ((phi, params) : cofctx) (alpha : cofib) (beta : cofib) : bool =
  (entailment ((And(alpha, phi)),params) beta) && (entailment ((And(beta, phi)),params) alpha)

let make (phi : Cof.cofib) (params : variable list) : cofctx =
  (phi, params)

let split (c : cofctx) : Cof.cofib * variable list =
  let phi, params = c in (phi, params)

let combine (c1 : cofctx) (c2 : cofctx) : cofctx =
  let phi1, par1 = c1 in
  let phi2, par2 = c2 in
  (Or(phi1, phi2), par1 @ par2)

let initial : cofctx = (Top, [])
