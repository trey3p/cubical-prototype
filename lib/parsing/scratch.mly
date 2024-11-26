%{
  open Ast
  open Naming
  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_lambda e lst in
        List.fold_left (fun e x -> (Lambda (x, t, e), loc)) e xs

  (* Build nested pis *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_left (fun e x -> (Pi (x, t, e), loc)) e xs

  (* Build nested sigmas*)
  let rec make_sigma e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_sigma e lst in
        List.fold_left (fun e x -> (Sigma (x, t, e), loc)) e xs
%}

%token PI SIGMA FUN TYPE
%token <int> NUMERAL
%token <string> NAME
%token LPAREN RPAREN
%token COLON COMMA PERIOD COLONEQUAL
%token ARROW DARROW
%token QUIT HELP PARAMETER CHECK EVAL CONTEXT DEFINITION
%token EOF

%start <Ast.directive list> directives

%%

(* Toplevel syntax *)

directives:
  | dir = directive PERIOD EOF
     { [dir] }
  | dir = directive PERIOD lst = directives
     { dir :: lst }

directive: mark_position(plain_directive) { $1 }
plain_directive:
  | QUIT
    { Quit }
  | HELP
    { Help }
  | PARAMETER x = NAME COLON e = expr
    { Parameter (Name x, e) }
  | CHECK e1 = expr e2 = expr
    { Check (e1, e2) }
  | EVAL e = expr
    { Eval e}
  | DEFINITION x = NAME COLONEQUAL e = expr
    { Definition (Name x, e) }
  | CONTEXT
    { Context }

(* Main syntax tree *)
expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e = plain_app_expr
    { e }
  | PI lst = abstraction COMMA e = expr
    { fst (make_pi e lst) }
  | FUN lst = abstraction DARROW e = expr
    { fst (make_lambda e lst) }
  /* | SIGMA lst = abstraction COMMA e = expr */
  /*   { fst (make_sigma e lst)} */
  | t1 = app_expr ARROW t2 = expr
    { Pi (Dummy, t1, t2) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e = plain_simple_expr
    { e }
  | e1 = app_expr e2 = simple_expr
    { App (e1, e2) }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | n = NAME
    { Var (Name n) }
  | TYPE k = NUMERAL
    { Type k }
  | LPAREN e = plain_expr RPAREN
    { e }
  | LPAREN e1 = expr COMMA e2 = expr RPAREN
    { Pair (e1, e2) }

abstraction:
  | b = bind1
    { [b] }
  | bs = binds
    { bs }

bind1: mark_position(plain_bind1) { $1 }
plain_bind1:
  | xs = nonempty_list(NAME) COLON t = expr
    { (List.map (fun x -> Name x) xs, t) }

binds:
  | LPAREN b = bind1 RPAREN
    { [b] }
  | LPAREN b = bind1 RPAREN lst = binds
    { b :: lst }

mark_position(X):
  x = X
  { x, Position ($startpos, $endpos) }

%%
