(* The syntax. *)
module Cof = Logic.Cofibration
open Cof
open Util.Naming
exception NOT_TYPE

type expr =
  (* Base Types *)
  | IntType
  | Num of int
  (* universe at level i *)
  | Type of int (* expr  = num *)
  | Var of variable
  | Lambda of abstraction
  | App of expr * expr
  (* Dep. function and pair *)
  | Pi of abstraction (* (x : T1) -> T2 *)
  | Sigma of abstraction (* bound var, type first component, type second component *)
  | Pair of expr * expr * variable * expr (* (e1, e2)_x; T(x) *)
  | Fst of expr
  | Snd of expr
  (* + type and the constructors *)
  | Sum of expr * expr
  | Inr of expr * expr (* Inr_A (e)*)
  | Inl of expr * expr    (* Inl_B (e) *)
  | Case of expr * (variable * expr) * (variable * expr) * (variable * expr)
  (* Case(p : A + B, [z.C], x.M, y.N) *)
  | Eq of expr * expr * expr (* Eq_A(M, N) *)
  | Refl of expr
  | J of (variable * expr) * (variable * variable * variable * expr) * expr
   (* (bound variable * base case M), type family (motive C), base case M, equality proof p *)
  (* Interval Types *)
  | IMapT of variable * expr (* (x : II ) -> A(x) *)
  | IMap of variable * expr
  | IApp of expr * interval
  (* Cofib Types *)
  | CMapT of variable * expr (* (x : Cof ) -> A(x) *)
  | CMap of variable * expr
  | CApp of expr * cofib
  | Partial of cofib * expr (* [alpha] -> A *)
  | InP of cofib * expr (* In_alpha(e) : [alpha] -> A *)
  | OutP of expr (* Out(e) : A *) (* e is either Partial or Boudary *)
  | Bound of expr * cofib * expr (* A type, phi : cofib , t : [alpha] -> A *) (* A[phi -> t] *)
  | OutB of expr
  | InB of expr * cofib * expr * expr (* A, psi, t, a*)
  | Branch of cofib * cofib * expr * expr
  (* Uniqueness of Identity Proofs *)
  | Uip of expr * expr * variable * expr (* Type i, A : Type i, x : A, p : Eq_A(x,x), *)
  and abstraction = (variable * expr * expr)


type obj =
  | Cof of cofib
  | I of interval
  | Ex of expr
type substitution = (variable * obj) list

let mk k = k
let mk_var k = (Var k)
let mk_universe u = (Type u)
let mk_subst s e = (s, e)
let mk_pi a = (Pi a)
let mk_arrow s t = mk_pi (Dummy, s, t)
let mk_lambda a = (Lambda a)
let mk_app e1 e2 = (App (e1, e2))
let mk_sigma a = (Sigma a)
let mk_pair e1 e2 e3 e4 = (Pair(e1, e2, e3, e4))
let mk_fst e1 e2 e3 e4 = (Fst(mk_pair e1 e2 e3 e4))
let mk_snd e1 e2 e3 e4 = (Snd(mk_pair e1 e2 e3 e4))
let max_uni u1 u2 = (match u1, u2 with | Type i, Type j -> Type (max i j) | _ -> raise NOT_TYPE)
