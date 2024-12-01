module Level = Util.Level
module Cof = Logic.Cofibration
open Cof

(** Pretty-printing of expressions with the Ocaml [Format] library. *)

(** Print an expression, possibly placing parentheses around it. We always
    print things at a given "level" [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the expression should be parenthesized.

    Let us consider an example. When printing nested applications, we should print [App
    (App (e1, e2), e3)] as ["e1 e2 e3"] and [App(e1, App(e2, e3))] as ["e1 (e2 e3)"]. So
    if we assign level 1 to applications, then during printing of [App (e1, e2)] we should
    print [e1] at [max_level] 1 and [e2] at [max_level] 0.
*)
open Ast
open Util.Naming

(** Pretty-printing of expressions with the Ocaml [Format] library. *)

(** Print an expression, possibly placing parentheses around it. We always
    print things at a given "level" [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the expression should be parenthesized.

    Let us consider an example. When printing nested applications, we should print [App
    (App (e1, e2), e3)] as ["e1 e2 e3"] and [App(e1, App(e2, e3))] as ["e1 (e2 e3)"]. So
    if we assign level 1 to applications, then during printing of [App (e1, e2)] we should
    print [e1] at [max_level] 1 and [e2] at [max_level] 0.
*)
let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

(** Print the given source code position. *)
(* let position loc ppf = *)
(*   match loc with *)
(*   | Nowhere -> *)
(*       Format.fprintf ppf "unknown position" *)
(*   |   Position (begin_pos, end_pos) -> *)
(*       let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in *)
(*       let end_char = end_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in *)
(*       let begin_line = begin_pos.Lexing.pos_lnum in *)
(*       let filename = begin_pos.Lexing.pos_fname in *)

(*       if String.length filename != 0 then *)
(*         Format.fprintf ppf "file %S, line %d, charaters %d-%d" filename begin_line begin_char end_char *)
(*       else *)
(*         Format.fprintf ppf "line %d, characters %d-%d" (begin_line - 1) begin_char end_char *)

(** Print the name of a variable. *)
let variable x ppf =
  match x with
    | Dummy -> print ppf "_"
    | Name x -> print ppf "%s" x
    | Fresh (x, k) -> print ppf "%s_%d" x k

let print_interval e ppf =
      let rec print_interval ?max_level e ppf =  interval'?max_level e ppf
  and interval' ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match e with
      | Zero -> print "0"
      | One -> print "1"
      | X x -> variable x ppf
      | Join(t1, t2) -> print ~at_level:3 "%t ∨ %t" (print_interval ~max_level:4 t1) (print_interval ~max_level:4 t2)
      | Meet(t1, t2) -> print ~at_level:3 "%t ∧ %t" (print_interval ~max_level:4 t1) (print_interval ~max_level:4 t2)
    in
     print_interval e ppf

let print_cofib e ppf =
    let rec print_cofib ?max_level e ppf =  cofib'?max_level e ppf
  and cofib' ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
    match e with
    | Bot -> print "⊥"
    | Top -> print "⊤"
    | Param s -> variable s ppf
    | Eq(t1, t2) -> print ~at_level:3 "%t = %t" (print_interval t1) (print_interval t2)
    | Or(f1, f2) -> print ~at_level:3 "%t or %t" (print_cofib ~max_level:4 f1) (print_cofib ~max_level:4 f2)
    | And(f1, f2) -> print ~at_level:3 "%t and %t" (print_cofib ~max_level:4 f1) (print_cofib ~max_level:4 f2)
  in
    print_cofib e ppf



 (** [expr e ppf] prints (beautified) expression [e] using formatter [ppf]. *)
let print_expr e ppf =
  let rec print_expr ?max_level e ppf =  expr'?max_level e ppf
  and expr' ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match e with
        | Var x -> variable x ppf
        | IntType -> print "Int"
        | Num i -> print "%d" i
        | Type k -> print "Type %d" k
        | Pi (Dummy, t1, t2) -> print ~at_level:3 "%t ->@;%t" (print_expr ~max_level:2 t1) (print_expr t2)
        | Pi (x, t1, t2) -> print ~at_level:3 "Pi %t : %t,@;%t" (variable x) (print_expr ~max_level:4 t1) (print_expr t2)
        | Sigma(x, t1, t2) ->  print ~at_level:3 "Sigma %t : %t,@;%t" (variable x) (print_expr ~max_level:4 t1) (print_expr t2)
        | Lambda (x, t, e) -> print ~at_level:3 "fun %t : %t =>@;%t" (variable x) (print_expr t) (print_expr e)
        | App (e1, e2) -> print ~at_level:1 "%t@;%t" (print_expr ~max_level:1 e1) (print_expr ~max_level:0 e2)
        | IApp(e1, e2) -> print ~at_level:1 "%t@;%t" (print_expr ~max_level:1 e1) (print_interval e2)
        | CApp(e1, e2) -> print ~at_level:1 "%t@;%t" (print_expr ~max_level:1 e1) (print_cofib e2)
        | Pair(e1, e2, _, _) -> print "(%t,@;%t)" (print_expr e1) (print_expr e2)
        | Fst(e) -> print "fst(%t)" (print_expr e)
        | Snd(e) -> print "snd(%t)" (print_expr e)
        | Sum(e1, e2) -> print "Sum(%t, %t)" (print_expr e1) (print_expr e2)
        | Inr(_,e) -> print "inr(%t)" (print_expr e)
        | Inl(_,e) -> print "inl(%t)" (print_expr e)
        | Case(p, (z, c), (x, e2), (y, e3)) -> print "case[%t.%t] %t of %t.%t, %t.%t" (print_expr (Var z)) (print_expr c) (print_expr p) (print_expr (Var x)) (print_expr e2) (print_expr (Var y)) (print_expr e3)
        | Eq(a, n, o) -> print "Eq_%t (%t, %t)" (print_expr a) (print_expr n) (print_expr o)
        | Refl e -> print "refl %t" (print_expr e)
        | J((z, m), (x, y, q, c), p) ->  print "J[%t.%t.%t.%t](%t.%t, %t)" (variable x) (variable y) (variable q) (print_expr c) (variable z) (print_expr m) (print_expr p)
        | IMapT(x, t1) -> print ~at_level:3 "Pi %t : Interval,@;%t" (variable x) (print_expr ~max_level:4 t1)
        | IMap(x, t1) -> print ~at_level:3 "fun %t : Interval =>@;%t" (variable x) (print_expr t1)
        | CMapT(x, t1) -> print ~at_level:3 "Pi %t : Cof,@;%t" (variable x) (print_expr ~max_level:4 t1)
        | CMap(x, t1) -> print ~at_level:3 "fun %t : Cof =>@;%t" (variable x) (print_expr t1)
        | Partial(alpha, t) -> print ~at_level:3 "[%t] -> %t" (print_cofib alpha) (print_expr t)
        | InP(_, e) -> print ~at_level:3 "inp(%t)" (print_expr ~max_level:4 e)
        | OutP(e1) | OutB(e1) -> print ~at_level:3 "out(%t)" (print_expr ~max_level:4 e1)
        | Bound(t1, cof, t) -> print ~at_level:3 "%t[ %t -> %t ]" (print_expr t1) (print_cofib cof) (print_expr t)
        | InB(_, _, _, e3) -> print ~at_level:3 "inb(%t)" (print_expr e3)
        | Branch(a, b, t, u) -> print ~at_level:3 "[%t -> %t, %t -> %t]" (print_cofib a) (print_cofib b) (print_expr t) (print_expr u)
        | Uip(_, ty, x, eq) -> print ~at_level:3 "uip_%t(%t, %t)" (print_expr ty) (variable x) (print_expr eq)
  in
    print_expr (Beautify.beautify e) ppf

let expr' e ppf = print_expr e ppf
let print2 ppf (e1, e2) = print_expr e1 ppf; print_expr e2 ppf
(** Support for printing of errors, warning and debugging information. *)
