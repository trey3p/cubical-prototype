open Ast
open Util.Naming

exception Unbound_Var of string

type varctx = (variable * (expr * expr option)) list

let empty = []

(* Returns the type of var in context *)
let get_type (context : varctx) (var : variable) : expr =
  match (List.assoc_opt var context) with
  | Some (a, _) -> a
  | None -> raise (Unbound_Var("unbound " ^ var_to_string var))

let extend (context : varctx) (var : variable) (ty : expr) (d : expr option)  : varctx =
  (* Γ -> Γ, x : S *)
  (* context = Gamma, name : ty = x : S *)
  (var, (ty, d))::context

let initial : varctx = []
