(* Definition of reduction rules for terms *)
open Ast
open Ctx
open Util.Naming
open Substitution
open Help
open Eval
open Error
module Cof = Logic.Cofibration
module CSyntax = Parsing.Ast

exception TYPE_ERROR_PI_SIGMA
exception TYPE_ERROR_PAIR
exception TYPE_ERROR_IMAP
exception TYPE_ERROR_CMAP
exception TYPE_ERROR_SUM
exception TYPE_ERROR_PARTIAL
exception TYPE_ERROR_SYS
exception EVAL_ERROR
exception NOT_VAR
exception NOT_NEUTRAL
exception EXPECTED_PI
exception TYPE_EXPECTED
exception APP_SYNTH_ERROR

let renaming_bound (context: ctx) (ty : expr) (x, e1) (y, e2) : ctx * expr * expr =
    let fx = fresh_var x in
    let z = Var(fx) in
   ( (extend_context context fx ty None), (subst [(x, Ex z)] e1), (subst [(y, Ex z)] e2) )

(* term_equiv Gamma T e1 e2 := *)
(* true iff Gamma |- e1 = e2 : T *)
(* false o/w *)
(* ty is assumed to be normalized *)
(* Assumes e1 : ty e2 : ty *)
let rec term_equiv (context : ctx) (ty : Ast.expr) (e1 : Ast.expr) (e2 : Ast.expr) : bool =
   (match ty with
    | Pi (x, t1, t2) -> (term_equiv (extend_context context x t1 None) t2 (App (e1, Var(x))) (App(e2, Var(x)))) (* check types *)
    | Sigma (x, t1, t2) -> (term_equiv context t1 (Fst(e1)) (Fst(e2))) && (term_equiv context (subst [( x, Ex(Fst e1))] t2) (Snd e1) (Snd e2))
    | Bound(a, _, _) -> (term_equiv context a (OutB e1) (OutB e2))
    | Partial(alpha, t) -> (term_equiv (restrict_context context alpha) t (OutP e1) (OutP e2))
    | IMapT(x, t) ->  (term_equiv (add_dim context x) t (IApp(e1, X x)) (IApp(e2, X x)))
    | CMapT(x, t) -> (term_equiv (quantify_cof context x) t (CApp(e1, Param x)) (CApp(e2, Param x)))
    | _ ->  if Option.is_some(neutral_equiv context (head_red context e1) (head_red context e2)) then true else false (* shouldn't we head normalize before passing to neutral_equiv? *)
   )

(* [neutral_equiv gamma n1 n2 := Gamma |- n1 = n2] *)
(* neutral_equiv takes a context and two expressions. *)
(* The expressions are assumed to be neutral terms. *)
(* The function returns an expr option which either contains the normalized type *)
(* of the expressions (if they are equal) or None. *)
and neutral_equiv (context : ctx) (p1 : expr)  (p2 : expr) : expr option =
    (match p1, p2 with
    | IntType, IntType -> Some(Type 0)

    | Type u1, Type u2 ->
      if u1 = u2 then Some(Type u1) else None

    | Pi (x, t1, t2), Pi (y, t3, t4) | Sigma (x, t1, t2), Sigma (y, t3, t4) ->
      let ty1 = neutral_equiv context t1 t3 in
      let nctx, p1', p2' = (renaming_bound context t1 (x, t2) (y, t4)) in
      let ty2 = neutral_equiv nctx p1' p2' in
      (
        match ty1, ty2 with
        | Some(Type i), Some(Type j) -> Some(Type (max i j))
        | _ -> None
      )

    | Sum(a,b), Sum(c,d) ->
      let ty1 = (neutral_equiv context a c) in
      let ty2 = (neutral_equiv context b d) in
      (
        match ty1, ty2 with
        | Some(Type i), Some(Type j) -> Some(Type (max i j))
        | _ -> None
      )

    | Eq(a, m, n), Eq(a', m', n') ->
      if Option.is_some(neutral_equiv context m m') && Option.is_some(neutral_equiv context n n')
      then (neutral_equiv context a a') else None

    | Bound(a1, cof1, t1), Bound(a2, cof2, t2) ->
     if (Ctx.cof_equiv context cof1 cof2) && Option.is_some(neutral_equiv context t1 t2)
     then (neutral_equiv context a1 a2) else None

    | Partial(phi1, t1), Partial(phi2, t2) ->
     if (cof_equiv context phi1 phi2) then (neutral_equiv context t1 t2) else None

    | IMapT(x, t1), IMapT(y, t2) ->
      let x'  = fresh_var x in
      let t1', t2' = (subst [(x, Ex(Var x'))] t1), (subst [(y, Ex(Var x'))] t2) in
      let nctx = (add_dim context x') in
      (neutral_equiv nctx t1' t2')

    | CMapT(x, t1), CMapT(y, t2) ->
      let x'  = fresh_var x in
      let t1', t2' = (subst [(x, Ex(Var x'))] t1), (subst [(y, Ex(Var x'))] t2) in
      let nctx = (quantify_cof context x') in
      (neutral_equiv nctx t1' t2')

    | Var x , Var y -> if x = y then Some(var_type context x) else None

    | Num i, Num j -> if i = j then Some(IntType) else None

    | App(p1', m1), App(p2', m2) ->
      let ty = neutral_equiv context p1' p2' in
      (match ty with
       | Some(Pi(x, _, t2)) -> if (term_equiv context t2 m1 m2) then Some(term_norm context (Type max_int) (subst [(x,Ex m1)] t2)) else None
       | _ -> None
       )
    | Fst(p1'), Fst(p2') ->
      let ty = neutral_equiv context p1' p2' in
      (match ty with
       | Some(Sigma(_, a', _)) -> Some(a')
       | _ -> None
      )
    | Snd(p1'), Snd(p2') ->
      let ty = neutral_equiv context p1' p2' in
    (
      match ty with
       | Some(Sigma(x, _, a'')) -> Some(term_norm context (Type max_int) (subst [(x, Ex(Fst p1))] a''))
       | _ -> None
    )
    | OutB(p1'), OutB(p2') ->
      let ty = neutral_equiv context p1' p2' in
      (
        match ty with
        | Some(Bound(a, _, _)) -> Some(a)
        | _ -> None
      )
    | OutP(p1'), OutP(p2') ->
      let ty = neutral_equiv context p1' p2' in
      (match ty with
       | Some(Partial(_, a)) -> Some(a)
       | _ -> None
      )
    | Inl(_, p1'), Inl(_, p2') ->
      let ty = neutral_equiv context p1' p2' in
      (match ty with
       | Some(Sum(a, _)) -> Some(a)
       | _ -> None
      )

    | Inr(_, p1'), Inr(_, p2') ->
      let ty = neutral_equiv context p1' p2' in
      (match ty with
       | Some(Sum(_, b)) -> Some(b)
       | _ -> None
      )

    | Case(p, (z, c), (x1, e1), (y1, e2)), Case(o, _, (x2, e3), (y2, e4)) ->
      let ty = neutral_equiv context p o in
      (
        match ty with
        |Some( Sum(q, r) ) ->
          let nctx1, e3 = (extend_context context x1 q None), (subst [(x2, Ex(Var x1))] e3) in
          let nctx2, e4 = (extend_context context y1 r None), (subst [(y2, Ex(Var y1))] e4) in
          let c_l = term_norm context (Type max_int) (subst [(z, Ex (Inl(r ,Var x1)))] c) in
          let c_r = term_norm context (Type max_int) (subst [(z, Ex (Inr(q, Var y1)))] c) in
          if (term_equiv nctx1 c_l e1 e3) &&  (term_equiv nctx2 c_r e2 e4)
          then Some(term_norm context (Type max_int) (subst [(z, Ex p)] c))
          else None
        | _ -> None

      )

    | Pair(a, b, x, ty1), Pair(c, d, _, _) ->
      let t1 = (neutral_equiv context a c) in
      let t2 = (neutral_equiv context b d) in
      let ty1' = (term_norm context (Type max_int) ty1) in
      (match t1, t2 with
       | Some(t1'), Some(_) -> Some(Sigma(x, t1', ty1'))
       | _ -> None
      )

    | Branch(a, b, t, u), Branch(c, d, e, f)->
      let ty1 = neutral_equiv (Ctx.restrict_context context a) t e in
      let ty2 = neutral_equiv (Ctx.restrict_context context b) u f in
      if (Option.is_some ty1) && (Option.is_some ty2) && (Ctx.cof_equiv context a c) && (Ctx.cof_equiv context b d)
      then ty1
      else None

    | J((z1, m1), (x1, y1, q1, c1), p1),  J((z2, m2), (x2, y2, q2, c2), p2) ->
      let ty = neutral_equiv context p1 p2 in
      (match ty with
       | Some(Eq(a, n, o)) ->
         let ctx_z = (extend_context context z1 a None) in
         let m2 = (subst [(z1, Ex(Var z2))] m2) in
         let c1_z = term_norm context (Type max_int) (subst [( x1, Ex(Var z1));( y1, Ex(Var z1));( q1, Ex(Refl (Var z1)))] c1) in
         let c2_z = term_norm context (Type max_int) (subst [(x2, Ex(Var z2));(y2, Ex(Var z2));(q2,  Ex(Refl (Var z1)))] c2) in (* c1_z and c2_z question abt being term_normed *)
         if (term_equiv ctx_z c1_z m1 m2) && (term_equiv context (Eq(a, n, o)) p1 p2)
         then (neutral_equiv context c1_z c2_z) else None
       | _ -> None
      )
    | _ -> if p1 = p2 then Some(Type max_int) else None
    )


and check_type (context : ctx) (e : expr) (ty : expr) (l : position) : bool =
    let ty_e = (synth ~l:l context e) in
    (match ty_e,ty with
     | Type i, Type j ->  i <= j
     | _ ->  (term_equiv context (Type max_int) ty_e ty)
    )


(* synth c e = T, where c |- e : T *)
(* synth takes e and gives the normalized type of e *)
and synth ?(l = Nowhere) (context : ctx) (e : expr) : expr =
  let e' = fresh_top e in
  match e' with
  | IntType -> Type 0
  | Num _ -> IntType
  | Type x -> Type (x + 1)
  | Var x -> (var_type context x)
  | Lambda (x, t1, e) ->
    let u1 = (infer_universe context t1 l) in
    let t1' = (term_norm context u1 t1) in
    let nctx = (extend_context context x t1' None) in
    let t2 = (synth ~l:l nctx e) in
    Pi(x, t1', t2)

  | App(e1, e2) ->
    (* Print.print_expr (App(e1, e2)) Format.std_formatter; *)
    let (x, t1, t2) = (infer_pi context e1 l) in
    let t3 = (synth ~l:l context e2) in
    (* Print.print_expr t3 Format.std_formatter; *)
    (* let uni = (infer_universe context t1 l) in *)
    if (check_type context t1 t3 l) then (term_norm context t3 (subst [(x, Ex e2)] t2)) else raise APP_SYNTH_ERROR

  | Pi (x, t1, t2)  | Sigma (x, t1, t2) ->
    let u1 = (infer_universe context t1 l) in
    let u2 = (infer_universe (extend_context context x (term_norm context u1 t1) None) t2 l) in
    (match u1, u2 with
     | Type i, Type j ->
       let u = max i j in Type u
     | _ -> raise TYPE_ERROR_PI_SIGMA
    )

  | Pair(e1, e2, var, t2) ->
    Print.print_expr e Format.std_formatter;
    Format.print_space ();
    let t1 = synth ~l:l context e1 in
    let ty = Sigma(var , t1, t2) in (* put together to get universe *)
    let uni = infer_universe context ty l in (* get universe for normalization *)
        Print.print_expr e2 Format.std_formatter;
        Format.print_space ();
        Print.print_expr t2 Format.std_formatter;
        Format.print_newline ();
    if check_type context e2 t2 l then
    term_norm context uni ty else raise TYPE_ERROR_PAIR (* normalize bc t2 could be unnormalzied *)

  | Fst e ->
    let t = (synth ~l:l context e) in
    (match t with
     | Sigma(_, t1, _) -> t1
     | _ -> (error ~loc:l (TypeErr(SigmaExpected t)))
    )

  | Snd e ->
    let t = (synth ~l:l context e) in
    (match t with
     | Sigma(x, _, t2) -> term_norm context (Type max_int) (subst [(x, Ex(Fst e))] t2)
     | _ -> (error ~loc:l (TypeErr(SigmaExpected t))))

  | Sum(e1, e2) ->
    let u1 = (infer_universe context e1 l) in
    let u2 = (infer_universe context e2 l) in
    (match u1, u2 with
     | Type i, Type j -> let u = max i j in Type u
     | _ -> raise TYPE_ERROR_SUM
    )
  | Inr(b,le) ->
    let r = (synth ~l:l context b) in
    let uni = (synth ~l:l context le) in
    let le' = (term_norm context uni le) in
    Sum(le', r)

  | Inl(a, r) ->
    let le = (synth ~l:l context a) in
    let uni = (synth ~l:l context r) in
    let r' = (term_norm context uni r) in
    Sum(le, r')

  | Case(e1, (z, c), (x, e2), (y, e3)) ->
    (* check e2 C(inl) check e3 C(inr) return c(e1) *)
    let t = (synth ~l:l context e1) in
   (match t with
     | Sum(t1, t2) ->
       let ctx_x = (extend_context context x t1 None) in
       let ctx_y = (extend_context context y t1 None) in
       let c_z = (subst [(z, Ex e1)] c) in
       let c_z_ty = (synth ~l:l context c_z) in
       if (check_type ctx_x e2 (subst [(z, Ex(Inl(t2, Var x)))] c) l) && (check_type ctx_y e3 (subst [(z, Ex(Inr(t1, (Var y))))] c) l) then
       (term_norm context c_z_ty c_z) else error ~loc:l (TypeErr(TypeBranchMismatch (c_z_ty, e2, e3)))
     | _ -> error ~loc:l (TypeErr(SumExpected t))
     )

  | Eq(ty, e2, e3) ->
    let tA = (infer_universe context ty l) in
    let tM = (synth ~l:l context e2) in
    let tN = (synth ~l:l context e3) in
    if (term_equiv context tA tM ty) && (term_equiv context tA tN ty)
    then tA else error ~loc:l (TypeErr(TypeBranchMismatch (tA, tM, tN)))

  | Refl e ->
    let ty = (synth ~l:l context e) in
    let e' = (term_norm context ty e) in Eq(ty, e', e')

  | J((z, m), (x, y, q, c), p) ->

     let ptype = synth ~l:l context p in (* p |- Eq_A(n, o) *)
     let a, n, o = match ptype with
        | Eq(a, n, o) -> a, n, o
        | _ -> error ~loc:l (TypeErr (EqualityTypeExpected(ptype)))
     in
     let ctx_z = extend_context context z a None in
     let ctx_xyq = extend_context (extend_context (extend_context context x a None)  y a None) q (Eq(a, Var(x), Var(y))) None in
     (* Check that C is a valid motive *)
     let c_ty = infer_universe ctx_xyq c l in (* x, y : A, q : Eq(x,y) |- C type *)
     let c' = (term_norm context c_ty c) in
     let c_refl = (subst [(x, Ex(Var z)); (y, Ex(Var z)); (q, Ex(Refl (Var z)))] c') in
     let p' = (term_norm context ptype p) in
     if (check_type ctx_z m c_refl l) then (* z : A |- M : C[x -> z, y -> z, q -> refl z] *)
      (term_norm context c_ty (subst [(x, Ex n); (y, Ex o); (q, Ex p')] c')) (* C[x -> N, y -> O, q -> p], p = Eq_A(N, O) *)
     else
       error ~loc:l (TypeErr(TypeExpected(m, c_refl)))

  | IMapT(x, t1) ->
    (synth ~l:l (add_dim context x) t1)

  | IMap(x, e1) ->
    let t1 = (synth ~l:l (add_dim context x) e1) in
    IMapT(x, t1)

  | IApp(e1, e2) ->
    let x, t1 = infer_imap context e1 l in
    let u_t1 = (synth ~l:l context t1) in
    (term_norm context u_t1 (subst [(x, I e2)] t1))


  | Partial(alpha, ty) -> (infer_universe (restrict_context context alpha) ty l)

  | InP(alpha, e1) ->
      let t1 = (synth ~l:l (restrict_context context alpha) e1) in
      Partial(alpha, t1)

  | OutP(e1) ->
    let t1 = (synth ~l:l context e1) in
    (match t1 with
     | Partial(alpha, ty) -> if (valid_formula context alpha) then ty else raise TYPE_ERROR_PARTIAL (* outp ensure alpha is true *)
       (* give better error *)
     | _ -> error ~loc:l (TypeErr(CannotInferArgument("Out doesn't taken an argument of this type")))
    )
  | OutB(e1) ->
    let t1 = (synth ~l:l context e1) in
    (match t1 with
    | Bound(ty, _, _) -> ty
    | _ -> error ~loc:l (TypeErr(CannotInferArgument("Out doesn't taken an argument of this type")))
  )

  | Bound(ty, _, _) ->
    (synth ~l:l context ty)

  | InB(ty, cof, t, a) ->
    let ty' = (term_norm context (Type max_int) ty) in
    if (term_equiv (restrict_context context cof) ty t a) then
    Bound(ty', cof, t) else raise (error ~loc:l (TypeErr(BoundaryDisagreement(a))))

  | Branch(a, b, t, u) ->
    let ty_t = (synth (restrict_context context a) t) in
    let ty_u = (synth (restrict_context context b) u) in
    if (term_equiv (restrict_context (restrict_context context a) b) (Type max_int) ty_t ty_u)
    then ty_t
    else raise (error ~loc:l (TypeErr(BoundaryDisagreement(t))))

  | CMapT(x, t1) ->
    let nctx = (quantify_cof context x) in (synth ~l:l nctx t1)

  | CMap(x, e1) ->
    let nctx = (quantify_cof context x) in
    let t1 = synth ~l:l nctx e1 in CMapT(x, t1)

  | CApp(e1, e2) ->
    let x, t1 = infer_cmap context e1 l in
    let u_t1 = synth ~l:l context t1 in
    (term_norm context u_t1 (subst [(x, Cof e2)] t1))


  | Uip(universe, ty, x, eq) ->
    let freshx = fresh_var x in
    let p = fresh_var freshx in
    let uni = synth ~l:l context universe in
    let universe' = term_norm context uni universe in
    let ty' = term_norm context universe' ty in
    let eq' = term_norm context ty' eq in
       Pi(freshx, universe',
          Pi(x, ty',
            Pi(p, eq', Eq(eq', Var(p), Refl(Var x)))) )

  and infer_universe (context : ctx) (t : expr) (l : position) : expr =
    let u = (synth ~l:l context t) in
    match u with
    | Type _ -> u
    | IntType -> Type 0 (* check on this later *)
    | _ -> raise TYPE_EXPECTED

  and infer_pi (context : ctx) (t : expr) (l : position) : abstraction =
    let t = (synth ~l:l context t) in
    (match t with
    | Pi abs -> abs
    | _ -> raise EXPECTED_PI)
  and infer_imap (context : ctx) (t : expr) (l : position) : variable * expr =
    let ty = (synth ~l:l context t) in
    (match ty with
     | IMapT(x, t1) -> (x, t1)
     | _ -> raise TYPE_ERROR_IMAP
    )

  and infer_cmap (context : ctx) (t : expr) (l : position) : variable * expr =
    let ty = (synth ~l:l context t) in
    (match ty with
     | CMapT(x, t1) -> (x, t1)
     | _ -> raise TYPE_ERROR_CMAP
    )


let check_type_exists (context : ctx) (ty : expr) (l : position) : bool =
  match ty with
  | Type _ -> true
  | IntType -> true
  | _ ->
    let ty' = (synth ~l:l context ty) in
    (check_type context ty ty' l)

let rec toplevel ~quiet ctx {Util.Naming.data=tc; _} =
  let ctx = toplevel' ~quiet ctx tc in
  ctx

and toplevel' ~quiet ctx = function

  | CSyntax.TopLoad file ->
     topfile ~quiet ctx file

  | CSyntax.TopDefinition (x, e) ->
     let e' = (convert_parse_abstract e.data) in
     let ty = (synth ~l:e.loc ctx e') in
     Format.printf "%s of type %t@ \n" x (Print.print_expr e');
     let ctx = extend_context ctx (Util.Naming.Name x) ty (Some e') in
     if not quiet then Format.printf "%s is defined.@. \n" x ;
     ctx

  | CSyntax.TopSynth e ->
     let e' = (convert_parse_abstract e.data) in
     let ty = (synth ~l:e.loc ctx e') in
     Format.printf "@[<hov>%t@] : @[<hov>%t@]@. \n"
    (Print.print_expr (convert_parse_abstract e.data)) (Print.print_expr ty) ;
     ctx


  | CSyntax.TopCheck(e,ty) ->
    let e' = (convert_parse_abstract e.data) in
    let ty' = (convert_parse_abstract ty.data) in
    Format.printf " Checking type\n";
    let result = (check_type ctx e' ty' e.loc) in
    Format.printf "check_type result: %b\n" result;
    let synth_type = (synth ~l:e.loc ctx e') in
    Format.printf "synth result: %t\n" (Print.print_expr synth_type);
    if result
    then
    Format.printf "@[<hov>%t@] : @[<hov>%t@]@. \n"     (Print.print_expr (convert_parse_abstract e.data)) (Print.print_expr (convert_parse_abstract ty.data) )
    else
    Format.printf "%t has type %t \n" (Print.print_expr (convert_parse_abstract e.data)) (Print.print_expr synth_type)
    ; ctx

  | CSyntax.TopEval e ->
    let e' = (convert_parse_abstract e.data) in
     let ty = (synth ~l:e.loc ctx e') in
     let e'' = (term_norm ctx ty e') in
     Format.printf "@[<hov>%t@]@ : @[<hov>%t@]@. \n"
       (Print.print_expr e'')
       (Print.print_expr ty) ;
     ctx

  | CSyntax.TopAxiom (x, ty) ->
     let ty' = (convert_parse_abstract ty.data) in
     let _ = (check_type_exists ctx ty' ty.loc) in
     let ctx = extend_context ctx (Util.Naming.Name x) (convert_parse_abstract ty.data) None in
     if not quiet then Format.printf "%s is assumed.@. \n" x ;
     ctx

and topfile ~quiet ctx file =
  let rec fold ctx = function
    | [] -> ctx
    | top_cmd :: lst ->
       let ctx = toplevel ~quiet ctx top_cmd in
       fold ctx lst
  in
  let cmds = Parsing.Lexer.read_file Parsing.Parser.file file in
  fold ctx cmds
