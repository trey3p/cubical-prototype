open Ast
type type_error =
  | UnknownIdent of string
  | TypeExpected of expr * expr
  | TypeExpectedButFunction of expr
  | FunctionExpected of expr
  | CannotInferArgument of string
  | SigmaExpected of expr
  | SumExpected of expr
  | NumeralExpected of expr
  | TypeBranchMismatch of expr * expr * expr
  | EqualityTypeExpected of expr
  | BoundaryDisagreement of expr


type substitution_error =
  | NotVar of expr * expr

type eval_error =
  | TermNormTypeError of expr * expr


type check_error =
  | TypeErr of type_error
  | SubErr of substitution_error
  | EvalErr of eval_error

exception Error of check_error Util.Naming.t

(** [error ~loc err] raises the given type-checking error. *)
let error ~loc err = Stdlib.raise (Error (Util.Naming.locate ~loc err))

let print_type_error err ppf =
  match err with

  | UnknownIdent x -> Format.fprintf ppf "unknown identifier %s" x

  | TypeExpected (ty_expected, ty_actual) ->
     Format.fprintf ppf "this expression should have type %t but has type %t"
                        (Print.print_expr ty_expected)
                        (Print.print_expr ty_actual)

  | TypeExpectedButFunction ty ->
     Format.fprintf ppf "this expression is a function but should have type %t"
                        (Print.print_expr ty)

  | FunctionExpected ty ->
     Format.fprintf ppf "this expression should be a function but has type %t"
                        (Print.print_expr ty)
  | SigmaExpected ty ->
      Format.fprintf ppf "this expression should be a sigma but has type %t"
                        (Print.print_expr ty)
  | CannotInferArgument x ->
     Format.fprintf ppf "cannot infer the type of %s" x

  | SumExpected ty ->
    Format.fprintf ppf "this expression should be a coproduct type but has type %t"
                        (Print.print_expr ty)

  | NumeralExpected ty ->
    Format.fprintf ppf "this expression should be a numeral but has type %t"
                        (Print.print_expr ty)

  | TypeBranchMismatch (t1, t2, t3) ->
    Format.fprintf ppf "the branches should be type %t but are %t and %t"
                        (Print.print_expr t1)
                        (Print.print_expr t2)
                        (Print.print_expr t3)

  | EqualityTypeExpected (ty) ->
     Format.fprintf ppf "Expected equality type but got %t"
                         (Print.print_expr ty)

  | BoundaryDisagreement e -> Format.fprintf ppf "The expression %t disagrees on the system"
                                              (* (Print.print_cofib alpha) *)
                                              (Print.print_expr e)
                                              (* (Print.print_expr e2) *)
 let print_sub_error err ppf =
  match err with
  | NotVar (e1, e2) ->
       Format.fprintf ppf "The expression associated with variable %t is expected to be a variable but is %t"
        (Print.print_expr e1) (Print.print_expr e2)

let print_eval_error err ppf =
  match err with
   | TermNormTypeError (ty, e) ->
      Format.fprintf ppf "Expected a term of type %t but was given %t"
        (Print.print_expr ty) (Print.print_expr e)


let print_error err ppf =
  match err with
  | TypeErr(e) -> print_type_error e ppf
  | SubErr(e) -> print_sub_error e ppf
  | EvalErr(e) -> print_eval_error e ppf
