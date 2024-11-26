open Proplog
open Util.Naming

exception FORMULA_PARAMTER
exception UNBOUND_FORMULA_PARAMETER

type interval =
  | Zero
  | One
  | X of variable
  | Join of interval * interval
  | Meet of interval * interval

type cofib =
  | Bot
  | Top
  | Eq of interval * interval
  | Or of cofib * cofib
  | And of cofib * cofib
  | Param of variable

let rec term_to_pl(t : interval) : pl =
  match t with
  | Zero -> F
  | One -> T
  | X s -> P s
  | Join(t1, t2 )-> Disj(term_to_pl t1, term_to_pl t2)
  | Meet(t1, t2) -> Conj(term_to_pl t1, term_to_pl t2)

let term_to_negated_iff (t1 : interval) (t2 : interval) : pl =
  Not ( Iff(term_to_pl t1, term_to_pl t2))

let rec formula_to_pl (f: cofib) : pl =
  match f with
  | Bot -> F
  | Top -> T
  | Eq(t1, t2) -> term_to_negated_iff t1 t2
  | Or(f1, f2) -> Disj(formula_to_pl f1, formula_to_pl f2)
  | And(f1, f2) -> Conj(formula_to_pl f1, formula_to_pl f2)
  | Param(x) -> P x

let valid (f : cofib) : bool  =
  not (naive_sat (formula_to_pl f))

let rec term_variables (t : interval) (acc : Util.Naming.variable list) : Util.Naming.variable list =
    match t with
    | Zero -> acc
    | One -> acc
    | X s when List.mem s acc -> acc
    | X s -> s :: acc
    | Join(t1, t2) ->  let acc1 = term_variables t1 acc in
                      term_variables t2 acc1
    | Meet(t1, t2) -> let acc1 = term_variables t1 acc in
                      term_variables t2 acc1




let interval_variables (f : cofib) : Util.Naming.variable list =
  (* [interval_variables f] returns the interval variables in f, *)
  (* in order of occurence in the formula (reading left to right) *)
  let rec aux (f : cofib) (acc : Util.Naming.variable list) : Util.Naming.variable list =
    match f with
    | Param _ -> acc
    | Bot | Top -> acc
    | Eq(t1, t2) -> let acc1 = term_variables t1 acc in term_variables t2 acc1
    | And (f1, f2) -> let acc1 = aux f1 acc in aux f2 acc1
    | Or (f1, f2) -> let acc1 = aux f1 acc in aux f2 acc1

  in
  List.rev(aux f [])

let formula_params (f : cofib) : Util.Naming.variable list =
  (* [interval_variables f] returns the formual params in f, *)
  (* in order of occurence in the formula (reading left to right) *)
  let rec aux (f : cofib) (acc : Util.Naming.variable list) : Util.Naming.variable list =
    match f with
    | Param s when List.mem s acc -> acc
    | Param s -> s :: acc
    | Bot | Top -> acc
    | Eq(_, _) -> acc
    | And (f1, f2) -> let acc1 = aux f1 acc in aux f2 acc1
    | Or (f1, f2) -> let acc1 = aux f1 acc in aux f2 acc1

  in
  List.rev(aux f [])

let rec rename_vars_aux (vars : string list) : string list =
  match vars with
  | [] -> []
  | x::xs -> ( x ^ string_of_int 1)::(rename_vars_aux (xs))

let rename_vars (vars : string list) : string list =
  rename_vars_aux (vars)


let rec freshen (t : interval) (l : int) : pl =
  (* where vars(t) = [x1, ... , xn]. *)
  (* vars(freshen(t)) = [x1l, ..., xnl] *)
  match t with
  | Zero -> F
  | One -> T
  | X s -> P (Name(var_to_string(s) ^ string_of_int l))
  | Join(t1, t2) -> (Disj( (freshen t1 l), (freshen t2  l)))
  | Meet(t1, t2) -> (Conj( (freshen t1 l), (freshen t2  l)))

let add_row (vars : variable list) (m : ((variable * variable) list) list) (l : int) : ((variable * variable) list) list =
  let vars'' = List.map (fun x -> Name((var_to_string x) ^ string_of_int l)) vars in
  (List.combine vars vars'')::m


let rec c_aux (f : cofib) (params : variable list) (vars : variable list) (l : int) (m : ((variable * variable) list) list) : pl * ((variable * variable) list) list =
  match f with
  | Param s when (List.mem s params) -> ((Not (Iff (P (fresh_var s), F))), (add_row vars m (l+1)))
  | Param _ -> raise UNBOUND_FORMULA_PARAMETER
  | Bot -> (T, (add_row vars m (l+1)))
  | Top -> (F, (add_row vars m (l+1)))
  | Eq(t1, t2) -> (Not (Iff( (freshen t1 (l+1)), (freshen t2 (l+1)) )), (add_row vars m (l+1)))

  | Or(f1, f2) -> let (f, xs) = (c_aux f1 params vars l m) in
                  let (t, ys) = (c_aux f2 params vars (List.length(xs)) xs) in
                  ((Conj(f, t)), ys)
  | And(f1, f2) -> let (f, xs) = (c_aux f1 params vars l m) in
                   let (t, ys) = (c_aux f2 params vars (List.length(xs)) xs) in
                   ((Disj(f, t)), ys)

let consequent (f : cofib) (params : variable list) (vars : variable list) : pl * ((variable * variable) list) list =
  (*we are guaranteed a leaf in the formula so we can start with the empty list*)
  c_aux f params vars 0 []

(* Antecedent Implementation *)

(* Dn Implementation *)


let rec d_aux (f : cofib) (params : variable list) (or_num : int)  : pl * int =
  match f with
  | Param s when (List.mem s params) ->  ((Iff (P (fresh_var s), F)), or_num)
  | Param _ -> raise UNBOUND_FORMULA_PARAMETER
  | Bot -> (F, or_num)
  | Top -> (T, or_num)
  | Eq(t1, t2) -> (Iff((term_to_pl t1), (term_to_pl t2)), or_num)
  | And(f1, f2) -> let (f1', num') = (d_aux f1 params or_num) in
                   let (f2', num'') = (d_aux f2 params num') in
                    (
                      Conj( f1', f2'),
                      num''
                    )
  | Or(f1, f2) -> let control = P (Name("c" ^ string_of_int (or_num+1))) in
                  let (f1', num') = (d_aux f1 params (or_num + 1)) in
                  let (f2', num'') = (d_aux f2 params num') in
                    (
                      Disj(
                      (Conj(control, f1')),
                      (Conj(Not(control), f2'))
                    ),
                      num''
                    )

let d (f : cofib) (params : variable list) : pl =
  let (f', _) = (d_aux f params 0) in f'


(* A Implementation *)


let rec d_every_leaf (f : cofib) (params : variable list) (m : ((variable * variable) list) list) : pl =
  match m with
  | [] -> T
  | x::[] -> (direct_sub (d f params) x)
  | x::xs -> Conj( (direct_sub (d f params) x),
                   (d_every_leaf f params xs)
                 )

let rec var_list (str : string) (n : int) : variable list=
  match n with
  | 0 -> []
  | n' ->  (var_list str (n-1)) @ [Name(str ^ (string_of_int n'))]

let antecedent (f : cofib) (p : variable list) (m : ((variable * variable) list) list) : pl =
  let xi = List.hd(m) in
  let oX, _ = List.split(xi) in
  let b = List.combine (oX) (var_list "b" (List.length(xi))) in
  let t = List.combine (oX) (var_list "t" (List.length(xi))) in
    Conj(
      (direct_sub (d f p) b),
      Conj(
        (direct_sub (d f p) t), (d_every_leaf f p m)
      ))

(* Monotonicity *)

let rec gen_m_leaf_b (xi : variable list) (acc : int): pl =
  match xi with
  | [] -> T
  | y::[] -> Implies( (P (Name("b" ^ string_of_int acc))),(P y)  )
  | y :: ys -> Conj(Implies( (P (Name("b" ^ string_of_int acc))),(P y)  ), (gen_m_leaf_b ys (acc +1)))


let rec m_b (mat :((variable * variable) list) list) : pl =
  match mat with
  | [] -> T
  | x::[] -> let _,x' = List.split(x) in  (gen_m_leaf_b x' 1)
  | x::xs -> let _,x' = List.split(x) in Conj(gen_m_leaf_b x' 1, m_b xs)



let rec gen_m_leaf_t (xi : variable list) (acc : int): pl =
  match xi with
  | [] -> T
  | y::[] -> Implies( (P y), (P (Name("t" ^ string_of_int acc))) )
  | y :: ys -> Conj(Implies( (P y), (P (Name("t" ^ string_of_int acc)))), (gen_m_leaf_t ys (acc +1)))


let rec m_t (mat :((variable  * variable) list) list) : pl =
  match mat with
  | [] -> T
  | x::[] -> let _,x' = List.split(x) in
      (gen_m_leaf_t x' (1))
  | x::xs -> let _,x' = List.split(x) in Conj(gen_m_leaf_t x' 1, m_t xs)


let m (mat : ((variable * variable) list) list) : pl =
  Conj(m_b mat , m_t mat)

let entailment_to_sat ((ant, params) : cofib * variable list) (consq : cofib) : pl =

  let vars = interval_variables ( Or(ant, consq)) in
  let tconsq, mat =  ( consequent consq params vars ) in
  let tant = (antecedent ant params mat) in
  let mono = (m mat) in
  Conj(mono , Conj(tconsq, tant))

let entailment (phi : cofib * variable list) (consq : cofib) : bool =
  not (naive_sat (entailment_to_sat phi consq))
