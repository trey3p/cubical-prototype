open Ast
open Util.Naming
open Substitution
module CSyntax = Parsing.Ast

let is_base (ty : expr) : bool * expr =
  match ty with
  | IntType -> (true, Type  0)
  | Type i -> (true, (Type (i + 1)))
  | Num _ -> (true, IntType)
  | _ -> (false, ty)

let is_dummy (x : Ast.expr) : bool =
  match x with
  | Ast.Var x ->
    x = Util.Naming.Dummy
  | _ -> false

let fresh_top (e : expr) : expr =
  match e with
  | Lambda (x, e1, e2) ->
       let x' = fresh_var x in
    let s = [(x, Ex(Var x'))] in
    Lambda(x', subst s e1, subst s e2)

  | Pi (x, e1, e2) ->
       let x' = fresh_var x in
    let s = [(x, Ex(Var x'))] in
    Pi(x', subst s e1, subst s e2)

  | Sigma (x, e1, e2) ->
    let x' = fresh_var x in
    let s = [(x, Ex(Var x'))] in
    Sigma(x', subst s e1, subst s e2)
  | Case(e1, (x, e2), (y, e3), (z, e4)) ->
    let x' = fresh_var x in
    let y' = fresh_var y in
    let z' = fresh_var z in
    Case(e1, (x', subst [(x, Ex(Var x'))] e2), (y, subst [(y, Ex(Var y'))] e3), (z', subst [(z, Ex(Var z'))] e4) )
  | J((z, m), (j, y, q, c), p)->
    let z', j', y', q' = fresh_var z, fresh_var j, fresh_var y, fresh_var q in
    let m', c' = subst [(z, Ex(Var z'))] m, subst [(j, Ex(Var j')); (y, Ex(Var y')); (q, Ex(Var q'))] c in
    J((z', m'), (j', y', q', c'), p)
  | IMapT(x, a) ->
    let x' = fresh_var x in
    let s = [(x, I(X x'))] in
    IMapT(x', subst s a)
  | IMap(x, a) ->
    let x' = fresh_var x in
    let s = [(x, I(X x'))] in
    IMap(x', subst s a)
  | CMapT(x, a) ->
    let x' = fresh_var x in
    let s = [(x, Cof(Param x'))] in
    CMapT(x', subst s a)
  | CMap(x, a) ->
    let x' = fresh_var x in
    let s = [(x, Cof(Param x'))] in
    CMap(x', subst s a)
  | _ -> e

let rec convert_parse_abstract (e : CSyntax.expr') : expr =
  let f e = convert_parse_abstract e.data in
  match e with
  | IntType -> IntType
  | Num i -> Num i
  | Type i -> Type i
  | Var s -> Var s
  | Lambda a -> Lambda (convert_abs a)
  | App(e1, e2) -> App(convert_parse_abstract e1.data, convert_parse_abstract e2.data)
  | Pi a -> Pi (convert_abs a)
  | Sigma a -> Sigma (convert_abs a)
  | Pair(e1, e2, x, e4) -> Pair(convert_parse_abstract e1.data, convert_parse_abstract e2.data, x, f e4)
  | Fst(e1) -> Fst(convert_parse_abstract e1.data)
  | Snd(e1) -> Snd(convert_parse_abstract e1.data)
  | Ascribe(e, _) -> convert_parse_abstract e.data
  | Sum(e1, e2) -> Sum(convert_parse_abstract e1.data, convert_parse_abstract e2.data)
  | Inr(e1, e2) -> Inr(f e1, f e2)
  | Inl(e1, e2) -> Inl(f e1, f e2)
  | Case(p, (z, c), (x, m), (y, n)) -> Case(f p, (z, f c), (x, f m), (y, f n))
  | Eq(e1, e2, e3) -> Eq( (convert_parse_abstract e1.data), (convert_parse_abstract e2.data), (convert_parse_abstract e3.data) )
  | Refl e -> Refl (convert_parse_abstract e.data)
  | J((z, m), (j, y, q, c), p) -> J((z, f m), (j, y, q,  f c), f p)
  | IMapT(x, t) -> IMapT(x, f t)
  | IMap(x, e1) -> IMap(x, f e1)
  | Partial(alpha, ty) -> Partial(alpha, f ty)
  | InP(alpha, a) -> InP(alpha, f a)
  | OutP(e1) -> OutP(f e1)
  | OutB(e1) -> OutB(f e1)
  | Bound(ty, sys) -> Bound(f ty, convert_sys sys)
  | InB(ty, sys, a) -> InB(f ty, convert_sys sys, f a)
  | Branch(sys) -> Branch (convert_sys sys)
  | Uip(uni, ty, x, eq) -> Uip(f uni, f ty, x, f eq)
  | IApp(e1, e2) -> IApp(f e1, e2)
  | CMap(x, e1) -> CMap(x, f e1)
  | CMapT(x, e1) -> CMapT(x, f e1)
  | CApp(e1, e2) -> CApp(f e1, e2)
  and convert_abs (a : CSyntax.abstraction) : abstraction =
    let (x, e1, e2) = a in
    (x, convert_parse_abstract e1.data, convert_parse_abstract e2.data)

  and convert_sys sys =
    match sys with
    | [] -> []
    | m::ms ->
      let a, t = m.cofibration, m.expression in
      { cofibration = a; expression = convert_parse_abstract t.data}::(convert_sys ms)


let make_nowhere (e : CSyntax.expr') =
  {Util.Naming.data = e; loc = Util.Naming.nowhere}

let rec convert_abstract_parse (e : Ast.expr ) : CSyntax.expr' =
  let f e = make_nowhere (convert_abstract_parse e) in
  match e with
  | IntType -> IntType
  | Num i -> Num i
  | Type i -> Type i
  | Var s -> Var s
  | Lambda a -> Lambda (convert_abs a)
  | App(e1, e2) -> App(make_nowhere (convert_abstract_parse e1), (make_nowhere (convert_abstract_parse e2)))
  | Pi a -> Pi (convert_abs a)
  | Sigma a -> Sigma (convert_abs a)
  | Pair(e1, e2, x, e4) -> Pair(f e1, f e2, x, f e4)
  | Fst(e1) -> Fst(make_nowhere (convert_abstract_parse e1))
  | Snd(e1) -> Snd(f e1)
  | Sum(e1, e2) -> Sum(make_nowhere (convert_abstract_parse e1), make_nowhere (convert_abstract_parse e2))
  | Inr(e1, e2) -> Inr(f e1, f e2)
  | Inl(e1, e2) -> Inl(f e1, f e2)
  | Case(p, (z, c), (x, m), (y, n)) -> Case(f p, (z, f c), (x, f m), (y, f n))
  | Eq(e1, e2, e3) -> Eq( (f e1), (f e2), (f e3) )
  | Refl e -> Refl (f e)
  | J((z, m), (j, y, q, c), p) -> J((z, f m), (j, y, q,  f c), f p)
  | IMapT(x, t) -> IMapT(x, f t)
  | IMap(x, e1) -> IMap(x, f e1)
  | Partial(alpha, ty) -> Partial(alpha, f ty)
  | InP(alpha, a) -> InP(alpha, f a)
  | OutP(e1) -> OutP(f e1)
  | OutB(e1) -> OutB(f e1)
  | Bound(ty, sys) -> Bound(f ty, convert_sys sys)
  | InB(ty, sys, a) -> InB(f ty, convert_sys sys, f a)
  | Branch(sys) -> Branch (convert_sys sys)
  | Uip(uni, ty, x, eq) -> Uip(f uni, f ty, x, f eq)
  | IApp(e1, e2) -> IApp(f e1, e2)
  | CMap(x, e1) -> CMap(x, f e1)
  | CMapT(x, e1) -> CMapT(x, f e1)
  | CApp(e1, e2) -> CApp(f e1, e2)
  and convert_abs (a : Ast.abstraction) : CSyntax.abstraction =
      let x, e1, e2 = a in
      (x, make_nowhere (convert_abstract_parse e1), make_nowhere (convert_abstract_parse e2))

  and convert_sys sys =
    match sys with
    | [] -> []
    | m::ms ->
      let a, t = m.cofibration, m.expression in
      { cofibration = a; expression = make_nowhere (convert_abstract_parse t)}::(convert_sys ms)
