open Ast
open Ctx
open Substitution
open Help


exception EVAL_ERROR (* all of these should be replaced *)
exception NOT_NEUTRAL
exception NOT_TYPE
exception EMPTY_SYSTEM

(* this edit is wrong rn. *)
let rec head_red (context : Ctx.ctx) (e : expr) : expr =
    match e with
    | App(e1, e2) -> (* e2 ->* e2' and then e1[e2/v]*)
      (match e1 with
       | Lambda(v, _, e1') -> (subst [(v, (Ex(e2)))] e1')
       |  e1' -> App(head_red context e1', e2)
      )
    | IApp(e1, e2) ->
      (match e1 with
       | IMap(x, e1') ->  (subst [(x, (I e2))] e1')
       | e1' ->  IApp(head_red context e1', e2)
      )
    | CApp(e1, e2) ->
      (match e1 with
       | CMap(x, e1') -> (subst [(x, (Cof e2))] e1')
       | e1' ->  CApp(head_red context e1', e2)
      )
    | Fst e ->
    (match e with
     | Pair (e1, _, _, _) -> e1
     | _ -> Fst (head_red context e)
    )
    | Snd e ->
    (match e with
     | Pair (_, e2, _, _) -> e2
     | _ -> Snd (head_red context e)
    )
    | Case(p, (z, c), (x, m), (y, n)) ->
      (match p with
       | Inl(_) -> (subst [(x, Ex p)] m)
       | Inr(_) -> (subst [(y, Ex p)] n)
       | _ -> Case(head_red context p, (z, c), (x, m), (y, n))
      )
    |  J((z, m), (x,y,q,c) , p) ->
      (
        match p with
        | Refl n ->
           (subst [(z, Ex n)] m) (* J[x.y.q.C](z.M, refl N) == M[z -> N]*)
        | _ -> J((z,m),(x,y,q,c), (head_red context p))
      )
    | OutB e' ->
        (match e' with
        | InB(_, _, _, a) -> a
        | Var x ->
          (match (Ctx.var_type context x) with
           | Bound(_, psi, t) -> if Ctx.valid_formula context psi then t else e
           | _ -> raise EVAL_ERROR
           )
        | _ -> OutB (head_red context e')
        )

    | OutP e' ->
      (match e' with
       | InP(_, a) -> a
       | _ -> OutP (head_red context e')
      )
    | Branch(alpha, beta, e1, e2) ->
     (match (Ctx.valid_formula context alpha), (Ctx.valid_formula context alpha) with
      | true, _ -> head_red (restrict_context context alpha) e1
      | _, true -> head_red (restrict_context context beta) e2
      | _, _ -> e)

    | _ -> e

let rec head_norm (context : ctx) (e : expr) : expr =
  head_norm context (head_red context e)



let rec term_norm (context : ctx) (ty : expr) (e : expr) : expr =
  (* ty is normalized and is typable *)
  (* e is typable *)
  let ty' = fresh_top ty in
  match ty' with

  | Pi(x, t1, t2) ->
    let e' = term_norm (extend_context context x t1 None) t2 (App(e, (Var x))) in
    Lambda(x, t1, e')

  | Sigma(x, t1, t2) ->
    let p1 = (term_norm context t1 (Fst e)) in
    (* let t2' = term_norm context (Type max_int) (subst [(x, Ex p1)] t2) in *)
    let p2 = (term_norm context t2 (Snd e)) in
    Pair(p1, p2, x, t2)


  | Partial(alpha, a) ->
    let e' = term_norm (restrict_context context alpha) a (OutP e) in
    InP(alpha ,e')

  | IMapT(x, t) ->
    let e' = term_norm (add_dim context x) t (IApp(e, (X x))) in
    IMap(x, e')

  | CMapT(x, t) ->
    let e' = term_norm (quantify_cof context x) t (CApp(e, (Param x))) in
    CMap(x, e')
  | _ ->
    let e' = head_red context e in
    let e'',_ = neutral_norm context e' in
    e''
(* add IApp, CApp *)
and neutral_norm (context : ctx) (p : expr) : expr * expr =
  (* let (base, b) = is_base(p) in *)
  let p' = fresh_top p in
  match p' with
  (* | _ when base -> (p, b) *)
  | Var(x) -> (p, (var_type context x))
  | App(p', m) ->
    let p'', t = neutral_norm context p' in
    (match t with
     | Pi(x, t1, t2) ->
        let m' = term_norm context t1 m in
        (App(p'', m'), subst [(x, Ex m')] t2) (* norm type *)
     | _ -> raise NOT_NEUTRAL)
  | Fst e ->
    let (e', t) = neutral_norm context e in
    (match t with
     | Sigma(_, t1, _) -> (Fst e', t1)
     | _ -> raise NOT_NEUTRAL)

  | Snd e ->
    let (e', t) = neutral_norm context e in
    (match t with
     | Sigma(x, _, t2) -> (Snd e', subst [(x, Ex(Fst e'))] t2) (* norm type *)
     | _ -> raise NOT_NEUTRAL)

  | OutB p' ->
    let (p'', t) = neutral_norm context p' in
    (match t with
     | Bound(ty, _, _) -> ((OutB p''), ty)
     | _ -> raise NOT_NEUTRAL
    )

  | OutP p' ->
     let (p'', t) = neutral_norm context p' in
    (match t with
     | Partial(_, ty) -> ((OutP p''), ty)
     | _ -> raise NOT_NEUTRAL
    )

  | Case(p', (z, c), (x, m), (y, n)) ->
    let p'', t = neutral_norm context p' in
    (match t with
     | Sum(a, b) ->
       let m' = (term_norm (extend_context context x a None)  (subst [(z, Ex (Inl(b,(Var x))))]  c) m) in
       let n' = (term_norm (extend_context context y b None) (subst [(z, Ex (Inr(a,(Var y))))]  c) n) in
       let c' =  (term_norm (extend_context context z t None) (Type max_int) c) in
       let ctx_xy = extend_context (extend_context context x a None) y b None in
       let c_p = (subst [(z, Ex p'')] c) in
       let c_p' = (term_norm ctx_xy (Type max_int) c_p) in
       (Case(p'', (z , c'), (x , m'), (y, n')), c_p')
     | _ -> raise NOT_NEUTRAL
    )
  |  J((z, k), (x, y, q, c), p') ->
       let p'', t = neutral_norm context p' in
        (match t with
          | Eq(a,m,n) ->
            let ctx_z = extend_context context z a None in
            let c' = (term_norm context (Type max_int) c) in
            let c_refl = (subst [(x, Ex(Var z)); (y, Ex(Var z)); (q, Ex(Refl (Var z)))] c') in
            let c_refl' = term_norm context (Type max_int) c_refl in
            let c_p = (subst [(x, Ex(m)); (y, Ex(n)); (q, Ex(p''))] c') in
            let c_p' = (term_norm context (Type max_int) c_p) in
            let k' = (term_norm ctx_z c_refl' k) in
            J((z, k'), (x, y, q, c'), p''), c_p'
          | _ -> raise NOT_NEUTRAL
        )
  | Bound(a, cof, t) ->
    let a', ty = neutral_norm context a in
    let t', _ = neutral_norm context t in
    Bound(a', cof, t'), ty (* apply term_norm instead? *)

  | Pi(x, t1, t2) ->
    let t1', u1 = neutral_norm context t1 in
    let t2', u2 = neutral_norm (extend_context context x t1' None) t2 in
    let u = (match u1, u2 with | Type i, Type j -> Type (max i j) | _ -> raise NOT_TYPE) in
    Pi(x, t1', t2'), u

  | Sigma(x, t1, t2) ->
     let t1', u1 = neutral_norm context t1 in
     let t2', u2 = neutral_norm (extend_context context x t1' None) t2 in
     let u = (match u1, u2 with | Type i, Type j -> Type (max i j) | _ -> raise NOT_TYPE) in
     Sigma(x, t1', t2'), u

  | Partial(alpha, ty) ->
    let ty', u = neutral_norm context ty in
    Partial(alpha, ty'), u

  | Sum(a, b) ->
    let a', u1 = neutral_norm context a in
    let b', u2 = neutral_norm context b in
    let u = (match u1, u2 with | Type i, Type j -> Type (max i j) | _ -> raise NOT_TYPE) in
    Sum(a', b'), u

  | IMapT(x, t) ->
    let t', u = neutral_norm (add_dim context x) t in IMapT(x, t'), u

  | CMapT(x, t) ->
    let t', u = neutral_norm (quantify_cof context x) t in CMapT(x, t'), u

  | _ -> (p, Type (max_int)) (* q here *)
