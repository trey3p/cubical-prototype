type pl =
  | T
  | F
  | P of Util.Naming.variable
  | Not of pl
  | Conj of pl * pl
  | Disj of pl * pl
  | Implies of pl * pl
  | Iff of pl * pl


let rec arrow_elim (f : pl) : pl =
  (* [arrow_elim f] returns an equivalent formula without Implies or
     Iff constructors *)
  match f with
  | T | F | P _ -> f
  | Not f1 -> Not (arrow_elim f1)
  | Conj (f1, f2) -> Conj (arrow_elim f1, arrow_elim f2)
  | Disj (f1, f2) -> Disj (arrow_elim f1, arrow_elim f2)
  | Implies (f1, f2) -> Disj (Not (arrow_elim f1), arrow_elim f2)
  | Iff (f1, f2) ->
     let f3 = arrow_elim f1 in
     let f4 = arrow_elim f2 in
     Conj (Disj (Not f3, f4),
          Disj (Not f4, f3))


let formula_of_bool (b : bool) : pl =
  (* [formula_of_bool b] encodes bools as formulas *)
  match b with
  | false -> F
  | true -> T


let bool_of_formula (f : pl) : bool =
  (* [bool_of_formula f] encodes formulas Zero and One as bools *)
  match f with
  | T -> true
  | F -> false
  | _ -> invalid_arg "formula is neither Zero nor One"


(* The [simplify_con f] functions maintain the following invariant: if
   f is either 0, 1 or contains neither 0 nor 1, then the output is
   also of one of these three forms *)

let not_simplify (f : pl) : pl =
  (* [not_simplify f] computes the negation of f *)
  match f with
  | F -> T
  | T -> F
  | _ -> Not f

let and_simplify (f1, f2 : pl * pl) : pl =
  (* [and_simplify (f1, f2)] computes the conjunction of f1 and f2 *)
  match f1, f2 with
  | F, _ | _, F -> F
  | T, T -> T
  | _, _ -> Conj (f1, f2)

let or_simplify (f1, f2 : pl * pl) : pl =
  (* [or_simplify (f1, f2)] computes the disjunction of f1 and f2 *)
  match f1, f2 with
  | T, _ | _, T -> T
  | F, F -> F
  | _, _ -> Disj (f1, f2)


let implies_simplify (f1, f2 : pl * pl) : pl =
  (* [implies_simplify (f1, f2)] computes f1 implies f2 *)
  match f1, f2 with
  | F, _ -> T
  | T, _ -> f2
  | _, F -> Not f1
  | _, T -> T
  | _, _ -> Implies (f1, f2)


let iff_simplify (f1, f2 : pl * pl) : pl =
  (* [iff_simplify (f1, f2)] computes f1 iff f2 *)
  match f1, f2 with
  | F, F | T, T -> T
  | F, T | T, F -> F
  | F, _ -> Not f2
  | T, _ -> f2
  | _, F -> Not f1
  | _, T -> f1
  | _, _ -> Iff (f1, f2)


let rec apply (f : pl) (s : string) (b : bool) : pl =
  (* [apply f s b] applies the assignment { s = b } to f *)
  match f with
  | F | T -> f
  | P s1 when Util.Naming.var_to_string(s1) = s -> formula_of_bool b
  | P _ -> f
  | Not f1 -> not_simplify (apply f1 s b)
  | Conj (f1, f2) -> and_simplify (apply f1 s b, apply f2 s b)
  | Disj (f1, f2) -> or_simplify (apply f1 s b, apply f2 s b)
  | Implies (f1, f2) -> implies_simplify (apply f1 s b, apply f2 s b)
  | Iff (f1, f2) -> iff_simplify (apply f1 s b, apply f2 s b)


let rec apply_empty (f : pl) : pl =
  (* [apply f] applies the assignment {} to f *)
  match f with
  | F | T -> f
  | P _ -> f
  | Not f1 -> not_simplify (apply_empty f1)
  | Conj (f1, f2) -> and_simplify (apply_empty f1, apply_empty f2)
  | Disj (f1, f2) -> or_simplify (apply_empty f1, apply_empty f2)
  | Implies (f1, f2) -> implies_simplify (apply_empty f1, apply_empty f2)
  | Iff (f1, f2) -> iff_simplify (apply_empty f1, apply_empty f2)


let variables (f : pl) : Util.Naming.variable list =
  (* [variables f] returns the variables in f *)
  let rec aux (f : pl) (acc : Util.Naming.variable list) : Util.Naming.variable list =
    match f with
    | F | T -> acc
    | P s when List.mem s acc -> acc
    | P s -> s :: acc
    | Not f1 -> aux f1 acc
    | Conj (f1, f2) -> let acc1 = aux f1 acc in
                      aux f2 acc1
    | Disj (f1, f2) -> let acc1 = aux f1 acc in
                      aux f2 acc1
    | Implies (f1, f2) -> let acc1 = aux f1 acc in
                          aux f2 acc1
    | Iff (f1, f2) -> let acc1 = aux f1 acc in
                      aux f2 acc1
  in
  List.rev(aux f [])

let rec direct_sub (f : pl) (subs : (Util.Naming.variable * Util.Naming.variable) list) : pl =
  match f with
  | T -> T
  | F -> F
  | P s ->
    (match (List.assoc_opt s subs) with
    | None -> P s
    | Some v -> P v
    )
  | Not(f1) -> Not(direct_sub f1 subs)
  | Conj(f1, f2) -> Conj (direct_sub f1 subs, direct_sub f2 subs)
  | Disj(f1, f2) -> Disj (direct_sub f1 subs, direct_sub f2 subs)
  | Iff(f1, f2) ->  Iff (direct_sub f1 subs, direct_sub f2 subs)
  | Implies(f1, f2) -> Implies (direct_sub f1 subs, direct_sub f2 subs)


let naive_sat (f : pl) : bool =
  (* [naive_sat f] determines if f is satisfiable *)
  let rec aux (f : pl) (vars : Util.Naming.variable list) : pl =
    match vars with
    | [] -> apply_empty f
    | v :: vars1 -> or_simplify (aux (apply f (Util.Naming.var_to_string v) false) vars1,
                                 aux (apply f (Util.Naming.var_to_string v) true) vars1)
  in
  bool_of_formula (aux f (variables f))
