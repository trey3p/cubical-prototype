(** Renaming of bound variables for pretty printing. *)
open Ast
open Util.Naming
open Substitution

(** Split a variable name into base and numerical postfix, e.g.,
   ["x42"] is split into [("x", 42)]. *)
let split s =
  let n = String.length s in
  let i = ref (n - 1) in
    while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
    if !i < 0 || !i = n - 1
    then (s, None)
    else
      let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
        (String.sub s 0 (!i+1), Some k)

(** Given a variable [x] and substitution of variables to variables, does [x] appear
    in the codomain of the substitution? *)
let rec used (x : variable) (sbst : substitution) : bool =
  let x' = (match x with Name x | Fresh (x, _) -> x | Dummy -> "_") in
  match sbst with
  | [] -> false
  | ((Name y | Fresh (y, _)), _) :: lst -> x' = y || used x lst
  | (Dummy, _) :: lst -> used x lst

(** Given a variable [x] and a substitution of variables to variables, find a variant of
    [x] which does not appear in the codomain of the substitution. *)
let find_available x sbst : string =
  let x' = (match x with Name x | Fresh (x, _) -> x | Dummy -> "_") in
    if not (used x sbst)
    then x'
    else
      let (y, k) = split x' in
      let k = ref (match k with Some k -> k | None -> 0) in
        while used (Fresh(y, !k)) sbst do incr k done ;
        "y" ^ string_of_int !k

(** Does [x] occur freely in the given expression? *)
let rec occurs (x : variable) (e : expr) =
  match e with
    | Var y -> x = y
    | IntType | Num _ | Type _ -> false
    | Pi (y, e1, e2) | Lambda (y, e1, e2) | Sigma(y, e1, e2) -> occurs x e1 || (x <> y && occurs x e2)
    | App (e1, e2) | Pair (e1, e2, _, _) | Sum(e1, e2) -> occurs x e1 || occurs x e2
    | IApp(e1, e2) -> occurs x e1 || occurs_interval x e2
    | CApp(e1, e2) -> occurs x e1 || occurs_cofib x e2
    | Fst(e) | Snd(e) | Inl(_ ,e) | Inr(_ ,e) -> occurs x e
    | Case(p, (z, e1), (y, e2), (w, e3)) ->
      occurs x p || (x <> z && occurs x e1)  || (x <> y && occurs x e2) || (x <> w && occurs x e3)
    | Refl e1 -> occurs x e1
    | Eq(_, e1, e2) -> occurs x e1 || occurs x e2
    | J((z, m), (j, y, q, c), p)->   (x <> z && occurs x m) || (x <> j && x <> y && x <> q && occurs x c)|| occurs x p
    | IMapT(y, e1) | IMap(y, e1) -> (x <> y && occurs x e1)
    | CMapT(y, e1) | CMap(y, e1) -> (x <> y && occurs x e1)
    | Partial(alpha, e1) | InP(alpha, e1) ->
      occurs_cofib x alpha || occurs x e1
    | OutP(e1) | OutB(e1) -> occurs x e1
    | Bound(ty, cof, t) -> occurs x ty || occurs_cofib x cof || occurs x t
    | InB(_, _ , _, e3) -> occurs x e3
    | Branch(a, b, t, u) -> occurs_cofib x a || occurs_cofib x b || occurs x t || occurs x u
    | Uip(_, ty, p, eq) -> occurs x ty || occurs x (Var p) || occurs x eq
and occurs_cofib (x : variable) (alpha : Cof.cofib) : bool =
    List.mem (x) (Cof.interval_variables(alpha)) || List.mem (x) (Cof.formula_params alpha)
and occurs_interval (x : variable) (t : Cof.interval) : bool =
    List.mem (x) (Cof.term_variables t [])
let sbst_check (sbst : substitution) (x : variable) : variable =
  (match (List.assoc_opt x sbst) with
        | Some(Ex (Var y)) ->  y
        | _ ->  x)

 (** Rename bound variables in the given expression for the purposes of
    pretty printing. *)

let beautify_cofib (s : substitution) (x : variable ) (f : Cof.cofib) : variable * Cof.cofib =
  let y =
  if occurs_cofib x f
  then Name ( find_available x s)
  else Dummy
  in
    y, subst_cofib [(x, Ex (Var y))] f

let beautify_interval (s : substitution) (x : variable) (i : Cof.interval) : variable * Cof.interval =
  let y =
  if occurs_interval x i
  then Name ( find_available x s)
  else Dummy
  in
    y, subst_interval [(x, Ex (Var y))] i


let beautify =
  let rec beautify (sbst : substitution) (e : expr) =
    (match e with
      | Var x ->
        Var(sbst_check sbst x)
      | IntType -> IntType
      | Num k -> Num k
      | Type k -> Type k
      | Pi a -> Pi (beautify_abstraction sbst a)
      | Lambda a -> Lambda (beautify_abstraction sbst a)
      | Sigma a -> Sigma (beautify_abstraction sbst a )
      | App (e1, e2) -> App (beautify sbst e1, beautify sbst e2)
      | Pair(e1, e2, x, e4) ->
        let v = sbst_check sbst x in
        Pair(beautify sbst e1, beautify sbst e2, v, beautify sbst e4)
      | Fst(e) -> Fst(beautify sbst e)
      | Snd(e) -> Snd(beautify sbst e)
      | Sum(e1, e2) -> Sum(beautify sbst e1, beautify sbst e2)
      | Inr(e1, e2) -> Inr(beautify sbst e1, beautify sbst e2)
      | Inl(e1, e2) -> Inl(beautify sbst e1, beautify sbst e2)
      | Case(p, (z, e1), (x, e2), (y, e3)) ->
        let v1 = sbst_check sbst z in
        let v2 = sbst_check sbst x in
        let v3 = sbst_check sbst y in
        Case(beautify sbst p, (v1, beautify sbst e1), (v2, beautify sbst e2), (v3 , beautify sbst e3))
      | Refl e -> Refl(beautify sbst e)
      | Eq(ty, e1, e2) -> Eq(ty, beautify sbst e1, beautify sbst e2)
      | J((z, m), (x, y, q, c), p) ->
        J((sbst_check sbst z, beautify sbst m), (sbst_check sbst x, sbst_check sbst y, sbst_check sbst q, beautify sbst c), beautify sbst p)
      | IMapT(x, e1) ->
        let x' = match (beautify sbst (Var x)) with | Var y -> y | _ -> x in
        IMapT(x', beautify sbst e1)
      | IMap(x, e1) ->
        let x' = match (beautify sbst (Var x)) with| Var y -> y | _ -> x in
        IMap(x', beautify sbst e1)
      | Partial(alpha, e1) ->
        Partial(alpha, beautify sbst e1)
      | InP(alpha, e1) -> InP(alpha, beautify sbst e1)
      | OutP(e1) -> OutP(beautify sbst e1)
      | OutB(e1) -> OutB(beautify sbst e1)
      | Bound(e1, cof, t) -> Bound(beautify sbst e1, cof, beautify sbst t)
      | InB(ty, cof, t, a) -> InB(beautify sbst ty, cof, beautify sbst t,  beautify sbst a)
      | Branch(a, b, t, u) -> Branch (a, b, beautify sbst t, beautify sbst u)
      | Uip(uni, ty, p, eq) -> Uip(beautify sbst uni, beautify sbst ty, sbst_check sbst p, beautify sbst eq)
      | IApp(e1, e2) -> IApp(beautify sbst e1, e2)
      | CApp(e1, e2) -> CApp(beautify sbst e1, e2)
      | CMapT(x, e1) ->
        let x' = match (beautify sbst (Var x)) with | Var y -> y | _ -> x in
        CMapT(x', beautify sbst e1)
      | CMap(x, e1) ->
        let x' = match (beautify sbst (Var x)) with | Var y -> y | _ -> x in
        CMap(x', beautify sbst e1)
    )
    and beautify_abstraction sbst (x, e1, e2) =
    let e1 = beautify sbst e1 in
    let y =
      if occurs x e2
      then Name (find_available x sbst)
      else Dummy
    in
      (y, e1, beautify ((x, Ex(Var y)) :: sbst) e2)
 in
    beautify []


