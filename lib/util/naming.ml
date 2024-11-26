(* Definitions for naming *)

type variable =
  | Name of string        (*name given by user*)
  | Fresh of string * int (*name * counter*)
  | Dummy

(* Generates a fresh variable *)

let fresh_var  =
  let k = ref 0 in
  fun x ->
  match x with
  | Name x | Fresh (x, _) -> (incr k; Fresh(x, !k))
  | Dummy ->  (incr k ; Fresh ("_", !k))

let var_to_string (x : variable) =
  match x with
  | Name s -> s
  | Fresh(s, i) -> s ^ string_of_int i
  | Dummy -> "_"

(*  Position in source code. For each type in the abstract syntax we define two versions
    [t] and [t']. The former is the latter with a position tag. For example, [expr = expr'
    * position] and [expr'] is the type of expressions (without positions).
*)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown position *)

(** [nowhere e] is the expression [e] without a source position. It is used when
    an expression is generated and there is not reasonable position that could be
    assigned to it. *)
 let nowherefn x = (x, Nowhere)

type 'a t = { data : 'a ; loc : position }

let nowhere = Nowhere

let make loc1 loc2 = Position (loc1, loc2)

let of_lex lex =
  Position (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)

let locate ?(loc=Nowhere) x = { data = x; loc = loc }

let print loc ppf =
  match loc with
  | Nowhere ->
      Format.fprintf ppf "unknown location"
  | Position (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let end_char = end_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, charaters %d-%d" filename begin_line begin_char end_char
      else
        Format.fprintf ppf "line %d, characters %d-%d" (begin_line - 1) begin_char end_char
