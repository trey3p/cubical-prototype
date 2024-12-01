(* The syntax. *)
open Util.Naming
module Cof = Logic.Cofibration
open Cof


type expr = expr' t
and expr' =
  | IntType
  | Num of int
  (* universe at level i *)
  | Type of int
  | Var of variable
  | Lambda of abstraction
  | App of expr * expr
  (* Dep. function and pair *)
  | Pi of abstraction (* (x : T1) -> T2 *)
  | Sigma of abstraction (* bound var, type first component, type second component *)
  | Pair of  expr * expr * variable * expr
  | Fst of expr
  | Snd of expr
  | Ascribe of expr * expr
  | Sum of expr * expr
  | Inr of expr * expr
  | Inl of expr * expr
  | Case of expr * (variable * expr) * (variable * expr) * (variable * expr)
  | Eq of expr * expr * expr
  | Refl of expr
  | J of (variable * expr) * (variable * variable * variable * expr) * expr
  (* Interval Stuff *)
  | IMapT of Util.Naming.variable * expr (* (x : II ) -> A(x) *)
  | IMap of Util.Naming.variable * expr
  (* Cofib Types *)
  | Partial of Cof.cofib * expr (* [alpha] -> A *)
  | InP of Cof.cofib * expr (* In_alpha(e) : [alpha] -> A *)
  | OutB of expr
  | OutP of expr
  | Bound of expr * cofib * expr (* A type, phi : cofib , t : [alpha] -> A *) (* A[phi -> t] *)
  | InB of expr * cofib * expr * expr (* in_A_t(a) : A[phi -> t] *)
  | Branch of cofib * cofib * expr * expr
  | Uip of expr * expr * variable * expr
  | CMapT of variable * expr (* (x : Cof ) -> A(x) *)
  | CMap of variable * expr
  | CApp of expr * cofib
  | IApp of expr * interval
  and abstraction = (variable * expr * expr)
  and system =
  {
    cofibration : cofib;
    expression : expr;
  }

(* Constructors wrapped in nowhere positions*)

(* Parsed top-level command. *)
type toplevel = toplevel' t
and toplevel' =
  | TopLoad of string
  | TopDefinition of string * expr
  | TopSynth of expr
  | TopCheck of expr * expr
  | TopEval of expr
  | TopAxiom of string * expr

  (* Build nested lambdas *)
let make_lambda xus t =
  let rec fold = function
    | [] -> t
    | {loc; data=(xs, uopt)} :: xus ->
       let rec fold' = function
         | [] -> fold xus
         | x :: xs ->
           locate ~loc (Lambda ((x, uopt, fold' xs)))
       in
       fold' xs
  in
  (fold xus).data

  (* Build nested pis *)
let make_pi xus t =
  let rec fold = function
    | [] -> t
    | {loc; data=(xs, u)} :: xus ->
       let rec fold' = function
         | [] -> fold xus
         | x :: xs ->
            locate ~loc (Pi (x, u, fold' xs))
       in
       fold' xs
  in
  (fold xus).data

  (* Build nested sigmas*)
let make_sigma xus t =
  let rec fold = function
    | [] -> t
    | {loc; data=(xs, u)} :: xus ->
       let rec fold' = function
         | [] -> fold xus
         | x :: xs ->
            locate ~loc (Sigma (x, u, fold' xs))
       in
       fold' xs
  in
  (fold xus).data

let make_arrow u t =
  let x = Dummy in
    Pi (x, u, t)
