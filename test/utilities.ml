(* Utility functions for testing *)
open Core.Ast
open OUnit2
open Core.Print
open Core.Precondition
open Format
open Core.Substitution
open Logic.Cofibration

let rec alpha_rename_interval (i1 : interval) (i2 : interval) : interval * interval =
  match (i1, i2) with
  | (Zero, Zero) -> (Zero, Zero)
  | (One, One) -> (One, One)
  | (X x1, X _) -> (X x1, X x1)  (* Rename x2 to x1 *)
  | (Join (i11, i12), Join (i21, i22)) ->
      let (i11', i21') = alpha_rename_interval i11 i21 in
      let (i12', i22') = alpha_rename_interval i12 i22 in
      (Join (i11', i12'), Join (i21', i22'))
  | (Meet (i11, i12), Meet (i21, i22)) ->
      let (i11', i21') = alpha_rename_interval i11 i21 in
      let (i12', i22') = alpha_rename_interval i12 i22 in
      (Meet (i11', i12'), Meet (i21', i22'))
  | _ -> failwith "Intervals are not equal"

let rec alpha_rename_cofib (c1 : cofib) (c2 : cofib) : cofib * cofib =
  match (c1, c2) with
  | (Bot, Bot) -> (Bot, Bot)
  | (Top, Top) -> (Top, Top)
  | (Eq (i11, i12), Eq (i21, i22)) ->
      let (i11', i21') = alpha_rename_interval i11 i21 in
      let (i12', i22') = alpha_rename_interval i12 i22 in
      (Eq (i11', i12'), Eq (i21', i22'))
  | (Or (c11, c12), Or (c21, c22)) ->
      let (c11', c21') = alpha_rename_cofib c11 c21 in
      let (c12', c22') = alpha_rename_cofib c12 c22 in
      (Or (c11', c12'), Or (c21', c22'))
  | (And (c11, c12), And (c21, c22)) ->
      let (c11', c21') = alpha_rename_cofib c11 c21 in
      let (c12', c22') = alpha_rename_cofib c12 c22 in
      (And (c11', c12'), And (c21', c22'))
  | (Param x1, Param _) -> (Param x1, Param x1)  (* Rename x2 to x1 *)
  | _ -> failwith "Cofibrations are not equal"

let rec alpha_rename_system (s1 : system) (s2 : system) : system * system =
  let (cof1, cof2) = alpha_rename_cofib s1.cofibration s2.cofibration in
  let (expr1, expr2) = alpha_rename s1.expression s2.expression in
  ({ cofibration = cof1; expression = expr1 }, { cofibration = cof2; expression = expr2 })

and alpha_rename_system_list (sl1 : system list) (sl2 : system list) : system list * system list =
  List.split (List.map2 alpha_rename_system sl1 sl2)


and alpha_rename (e1 : expr) (e2 : expr) : expr * expr =
  match (e1, e2) with
  | (IntType, IntType) -> (IntType, IntType)
  | (Num i, Num j) when i = j -> (Num i, Num j)
  | (Type _, Type _) -> (e1, e2)
  | (Var x, Var _) -> (Var x, Var x)  (* Rename y to x *)
  | (Lambda (x, t1, e1'), Lambda (y, t2, e2')) ->
      let (t1', t2') = alpha_rename t1 t2 in
      let (e1'', e2'') = alpha_rename e1' (subst [(y, Ex (Var x))] e2') in
      (Lambda (x, t1', e1''), Lambda (x, t2', e2''))
  | (Pi (x, t1, e1'), Pi (y, t2, e2')) ->
      let (t1', t2') = alpha_rename t1 t2 in
      let (e1'', e2'') = alpha_rename e1' (subst [(y, Ex (Var x))] e2') in
      (Pi (x, t1', e1''), Pi (x, t2', e2''))
  | (Sigma (x, t1, e1'), Sigma (y, t2, e2')) ->
      let (t1', t2') = alpha_rename t1 t2 in
      let (e1'', e2'') = alpha_rename e1' (subst [(y, Ex (Var x))] e2') in
      (Sigma (x, t1', e1''), Sigma (x, t2', e2''))
  | (App (e11, e12), App (e21, e22)) ->
      let (e11', e21') = alpha_rename e11 e21 in
      let (e12', e22') = alpha_rename e12 e22 in
      (App (e11', e12'), App (e21', e22'))
  | (Pair (e11, e12, x , t), Pair (e21, e22, y, t2)) ->
      let (e11', e21') = alpha_rename e11 e21 in
      let (e12', e22') = alpha_rename e12 e22 in
      let (t1', t2') =  alpha_rename t (subst [(y, Ex (Var x))] t2) in
      (Pair (e11', e12', x, t1'), Pair (e21', e22', x, t2'))
  | (Fst e1', Fst e2') ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Fst e1'', Fst e2'')
  | (Snd e1', Snd e2') ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Snd e1'', Snd e2'')
  | (Sum (e11, e12), Sum (e21, e22)) ->
      let (e11', e21') = alpha_rename e11 e21 in
      let (e12', e22') = alpha_rename e12 e22 in
      (Sum (e11', e12'), Sum (e21', e22'))
  | (Inr (a1, e1'), Inr (a2, e2')) ->
      let (a1', a2') = alpha_rename a1 a2 in
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Inr (a1', e1''), Inr (a2', e2''))
  | (Inl (b1, e1'), Inl (b2, e2')) ->
      let (b1', b2') = alpha_rename b1 b2 in
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Inl (b1', e1''), Inl (b2', e2''))
  | (Case (e1', (z1, c1), (x1, m1), (y1, n1)), Case (e2', (z2, c2), (x2, m2), (y2, n2))) ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      let (c1', c2') = alpha_rename c1 (subst [(z2, Ex (Var z1))] c2) in
      let (m1', m2') = alpha_rename m1 (subst [(x2, Ex (Var x1))] m2) in
      let (n1', n2') = alpha_rename n1 (subst [(y2, Ex (Var y1))] n2) in
      (Case (e1'', (z1, c1'), (x1, m1'), (y1, n1')), Case (e2'', (z1, c2'), (x1, m2'), (y1, n2')))
  | (Eq (e11, e12, e13), Eq (e21, e22, e23)) ->
      let (e11', e21') = alpha_rename e11 e21 in
      let (e12', e22') = alpha_rename e12 e22 in
      let (e13', e23') = alpha_rename e13 e23 in
      (Eq (e11', e12', e13'), Eq (e21', e22', e23'))
  | (Refl e1', Refl e2') ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Refl e1'', Refl e2'')
  | (J ((z1, c1), (x1, y1, w1, d1), p1), J ((z2, c2), (x2, y2, w2, d2), p2)) ->
      let (c1', c2') = alpha_rename c1 (subst [(z2, Ex (Var z1))] c2) in
      let (d1', d2') = alpha_rename d1 (subst [(x2, Ex (Var x1)); (y2, Ex (Var y1)); (w2, Ex (Var w1))] d2) in
      let (p1', p2') = alpha_rename p1 p2 in
      (J ((z1, c1'), (x1, y1, w1, d1'), p1'), J ((z1, c2'), (x1, y1, w1, d2'), p2'))
    | (IMapT (x1, e1'), IMapT (x2, e2')) ->
      let (e1'', e2'') = alpha_rename e1' (subst [(x2, Ex (Var x1))] e2') in
      (IMapT (x1, e1''), IMapT (x1, e2''))
  | (IMap (x1, e1'), IMap (x2, e2')) ->
      let (e1'', e2'') = alpha_rename e1' (subst [(x2, Ex (Var x1))] e2') in
      (IMap (x1, e1''), IMap (x1, e2''))
  | (IApp (e1', i1), IApp (e2', i2)) ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      let (i1', i2') = alpha_rename_interval i1 i2 in
      (IApp (e1'', i1'), IApp (e2'', i2'))
  | (CMapT (x1, e1'), CMapT (x2, e2')) ->
      let (e1'', e2'') = alpha_rename e1' (subst [(x2, Ex (Var x1))] e2') in
      (CMapT (x1, e1''), CMapT (x1, e2''))
  | (CMap (x1, e1'), CMap (x2, e2')) ->
      let (e1'', e2'') = alpha_rename e1' (subst [(x2, Ex (Var x1))] e2') in
      (CMap (x1, e1''), CMap (x1, e2''))
  | (CApp (e1', c1), CApp (e2', c2)) ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      let (c1', c2') = alpha_rename_cofib c1 c2 in
      (CApp (e1'', c1'), CApp (e2'', c2'))
  | (Partial (c1, e1'), Partial (c2, e2')) ->
      let (c1', c2') = alpha_rename_cofib c1 c2 in
      let (e1'', e2'') = alpha_rename e1' e2' in
      (Partial (c1', e1''), Partial (c2', e2''))
  | (InP (c1, e1'), InP (c2, e2')) ->
      let (c1', c2') = alpha_rename_cofib c1 c2 in
      let (e1'', e2'') = alpha_rename e1' e2' in
      (InP (c1', e1''), InP (c2', e2''))
  | (OutP e1', OutP e2') ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      (OutP e1'', OutP e2'')
  | (Bound (e1', sl1), Bound (e2', sl2)) ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      let (sl1', sl2') = alpha_rename_system_list sl1 sl2 in
      (Bound (e1'', sl1'), Bound (e2'', sl2'))
  | (OutB e1', OutB e2') ->
      let (e1'', e2'') = alpha_rename e1' e2' in
      (OutB e1'', OutB e2'')
  | (InB (e1', sl1, e1''), InB (e2', sl2, e2'')) ->
      let (e1''', e2''') = alpha_rename e1' e2' in
      let (sl1', sl2') = alpha_rename_system_list sl1 sl2 in
      let (e1'''', e2'''') = alpha_rename e1'' e2'' in
      (InB (e1''', sl1', e1''''), InB (e2''', sl2', e2''''))
  | (Branch sl1, Branch sl2) ->
      let (sl1', sl2') = alpha_rename_system_list sl1 sl2 in
      (Branch sl1', Branch sl2')
  | (Uip (e11, e12, x1, e13), Uip (e21, e22, x2, e23)) ->
      let (e11', e21') = alpha_rename e11 e21 in
      let (e12', e22') = alpha_rename e12 e22 in
      let (e13', e23') = alpha_rename e13 (subst [(x2, Ex (Var x1))] e23) in
      (Uip (e11', e12', x1, e13'), Uip (e21', e22', x1, e23'))
  | _ -> failwith "Expressions are not equal"


let check_equal_expression (e1 : expr) (e2 : expr) _ =
  try
    let e1', e2' = alpha_rename e1 e2 in
    assert_equal e1' e2' ~pp_diff:print2
  with _ ->
     assert_equal e1 e2 ~pp_diff:print2


let check_equal_bool a1 a2 _ =
  assert_equal a1 a2 ~printer:string_of_bool

(*---------------------------------------------------------------*)
(*                   Cofib Synthesis Testing Helpers             *)
(*---------------------------------------------------------------*)

let expr_to_string (e : expr) : string =
  let buffer = Buffer.create 100 in
  let formatter = formatter_of_buffer buffer in
  print_expr e formatter;
  pp_print_flush formatter ();
  Buffer.contents buffer

let rec string_of_term (t : Cof.interval) : string =
  match t with
  | Zero -> "Zero"
  | One -> "One"
  | X s -> Util.Naming.var_to_string s
  | Join(t1, t2) -> sprintf "%s ∨ %s"
                    (string_of_term t1)
                    (string_of_term t2)
  | Meet(t1, t2) -> sprintf "%s ∧ %s"
                    (string_of_term t1)
                    (string_of_term t2)

let rec string_of_cofib (f : Cof.cofib) : string =
  match f with
  | Bot -> "Bot"
  | Top -> "Top"
  | Eq(t1, t2) -> sprintf "%s = %s"
                  (string_of_term t1)
                  (string_of_term t2)

  | Or(f1, f2) -> sprintf "%s or %s"
                  (string_of_cofib f1)
                  (string_of_cofib f2)

  | And(f1, f2) -> sprintf "%s and %s"
                   (string_of_cofib f1)
                   (string_of_cofib f2)
  | Param s -> Util.Naming.var_to_string s

let check_equal_cofib a1 a2 _ =
  assert_equal a1 a2 ~printer:string_of_cofib

let rec string_of_precons (p : precon list) : string =
  match p with
  | [] -> ""
  | (ex, phi)::ps ->

    let ex_s = expr_to_string ex in
    let phi_s = string_of_cofib phi in
    "( " ^ ex_s ^ ", " ^ phi_s ^ "), " ^ string_of_precons ps

let check_equal_precons a1 a2 _ =
  try
    let f (e, p) (t, j) = let (e1', e2'), (t1', t2') = (alpha_rename e t, alpha_rename_cofib p j) in (e1', t1'), (e2', t2') in
    let a1, a2 =  List.split (List.map2 f a1 a2) in
    assert_equal a1 a2 ~printer:string_of_precons
  with _ ->
    assert_equal a1 a2 ~printer:string_of_precons
