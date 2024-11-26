module Cof = Logic.Cofibration
open Ast
open Util.Naming

exception NOT_EXPR
exception NOT_COF
exception NOT_INTERVAL

(* let sbst_check (sbst : substitution) (x : variable) : variable = *)
(*   (match (List.assoc_opt x sbst) with *)
(*         | Some(Var y) ->  y *)
(*         | _ ->  x) *)

let rec subst_interval (s : substitution) (t : Cof.interval) : Cof.interval =
    match t with
    | Zero | One -> t
    | X x ->
        (match (List.assoc_opt x s) with
          | None -> X x
          | Some (I a) -> a
          | _ -> X x (* replace with error in error.ml requires a loc to be passed *)
        )
    | Join(t1, t2) -> Join(subst_interval s t1, subst_interval s t2)
    | Meet(t1, t2) -> Meet(subst_interval s t1, subst_interval s t2)


let rec subst_cofib (s : substitution) (phi : Cof.cofib)  : Cof.cofib =
    match phi with
    | Bot | Top -> phi
    | Eq(t1, t2) -> Eq(subst_interval s t1, subst_interval s t2)
    | Or(f1, f2) -> Or(subst_cofib s f1, subst_cofib s f2)
    | And(f1, f2) -> And(subst_cofib s f1, subst_cofib s f2)
    | Param x ->
      (match (List.assoc_opt x s) with
       | None -> Param x
       | Some (Cof a) -> a
       | _ -> Param x
      )

(* subst s e  = e[s], where s = [ x_1/e_1 ... x_n/en ] *)
let rec subst (s : substitution) (e : expr) : Ast.expr =
  match e with
  | IntType | Num _ | Type _ -> e
  | Var x ->
    (match (List.assoc_opt x s) with
    | None -> Var x
    | Some (Ex y) -> y
    | _ -> Var x
    )
  | Lambda abs -> Lambda (subst_abs s abs)
  | App(e1, e2) -> App(subst s e1, subst s e2)
  | CApp(e1, e2) -> CApp(subst s e1, subst_cofib s e2)
  | IApp(e1, e2) -> IApp(subst s e1, subst_interval s e2)
  | Pi abs -> Pi (subst_abs s abs)
  | Sigma abs -> Sigma (subst_abs s abs)
  | Pair(e1, e2, e3, e4) -> Pair(subst s e1, subst s e2, e3, e4)
  | Fst e -> Fst(subst s e)
  | Snd e -> Snd(subst s e)
  | Sum(e1, e2) -> Sum(subst s e1, subst s e2)
  | Inr(e1, e2) -> Inr(e1 ,subst s e2)
  | Inl(e1, e2) -> Inl(e1, subst s e2)
  | Case(e1, (x, e2), (y, e3), (z, e4)) ->
    let x' = fresh_var x in
    let y' = fresh_var y in
    let z' = fresh_var z in
    Case( subst s e1, (x', subst ((x, Ex(Var x'))::s) e2), (y, subst ((y, Ex(Var y'))::s) e3), (z', subst ((z, Ex(Var z'))::s) e4) )
  | Eq(e1, e2, e3) -> Eq( (subst s e1), (subst s e2), (subst s e3) )
  | Refl e -> subst s e
  | J((z, m), (j, y, q, c), p)->
    let z' = fresh_var z in
    let j', y', q' = fresh_var j, fresh_var y, fresh_var q in
    let s' = [(j, Ex(Var j')); (y, Ex(Var y')); (q, Ex(Var q'))] @ s in
    J((z', subst ((z, Ex(Var z'))::s) m), (j', y', q', subst s' c), subst s p)

  | IMapT(x, a) ->
    let x' = fresh_var x in
    let subs = (x, I(X x'))::s in
    IMap(x', subst subs a)

  | IMap(x, a) ->
    let x' = fresh_var x in
    let subs = (x, I(X x'))::s in
    IMapT(x', subst subs a)

  | CMapT(x, a) ->
    let x' = fresh_var x in
    let subs = (x, Cof(Param x'))::s in
    CMapT(x', subst subs a)
  | CMap(x, a) ->
    let x' = fresh_var x in
    let subs = (x, Cof(Param x'))::s in
    CMap(x', subst subs a)

  | Partial(phi, e) -> Partial(subst_cofib s phi, subst s e)
  | InP(alpha, e) -> InP(subst_cofib s alpha, subst s e)
  | OutP e -> OutP(subst s e)
  | OutB e -> OutB(subst s e)
  | Bound(a, systems) -> Bound(subst s a, subst_systems s systems)
  | InB(a_ty, sys,  a) -> InB(subst s a_ty, subst_systems s sys, subst s a)
  | Branch sys -> Branch (subst_systems  s sys)
  | Uip(uni, ty, x, eq) ->
    let x' = fresh_var x in
    Uip(uni, subst s ty, x', subst s eq)
and subst_abs (s : substitution) (e : abstraction) : abstraction =
  let v, e1, e2 = e in
  let v' = fresh_var v in
  (v', subst s e1, subst ((v, Ex(Var v'))::s) e2)
and subst_systems (s : substitution) (l : system list) : system list =
  match l with
  | [] -> []
  | m::ms ->
    let a, t = subst_cofib s m.cofibration, subst s m.expression in
    (Ast.mk_sys a t)::(subst_systems s ms)
