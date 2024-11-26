%{
    open Util
%}

(* Infix operations a la OCaml *)

%token <Util.Naming.variable Util.Naming.t> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Names *)
%token <int> NUMERAL
%token <string> NAME
%token UNDERSCORE

(* Parentheses & punctuations *)
%token LPAREN RPAREN LBRACKET RBRACKET
%token COLONEQ
%token COMMA COLON DARROW ARROW DOT

(* Expressions *)
%token TYPE
%token PI
%token LAMBDA
%token SIGMA
%token FST
%token SND


%token SUM
%token INR
%token INL
%token CASE
%token OF

%token EQ REFL

%token INT
(* Toplevel commands *)
%token <string> QUOTED_STRING
%token LOAD
%token DEF
%token CHECK
%token EVAL
%token AXIOM
%token SYNTH

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2
%left     INFIXOP3
%right    INFIXOP4

%start <Ast.toplevel list> file
%start <Ast.toplevel> commandline

%%

file:
  | f=filecontents EOF
    { f }


filecontents:
  |
    { [] }

  | d=topcomp ds=filecontents
    { d :: ds }


commandline:
  | topcomp EOF
    { $1 }


(* Things that can be defined on toplevel. *)
topcomp: mark_location(topcomp_) { $1 }
topcomp_:
  | LOAD fn=QUOTED_STRING
    { Ast.TopLoad fn }

  | DEF x=var_name COLONEQ e=term
    { Ast.TopDefinition (Naming.var_to_string x, e) }

  | CHECK e1=term COLON e2=term
    { Ast.TopCheck(e1, e2) }

  | SYNTH e = term
    { Ast.TopSynth e }

  | EVAL e=term
    { Ast.TopEval e }

  | AXIOM x=var_name COLON e=term
    { Ast.TopAxiom (Naming.var_to_string x, e) }


term : mark_location(term_) { $1 }
term_:
  | e=infix_term_
    { e }

  | PI a=prod_abstraction COMMA e=term
    { Ast.make_pi a e }

  | SIGMA a=sigma_abstraction COMMA e=term
    {Ast.make_sigma a e}

  | e1=infix_term ARROW e2=term
    { Ast.make_arrow e1 e2 }

  | LAMBDA a=lambda_abstraction DARROW e=term
    { Ast.make_lambda a e }

  | e1=term COLON e2=term
    { Ast.Ascribe (e1, e2) }

  | LPAREN e1 = term COMMA e2 = term RPAREN UNDERSCORE e3 = var_name COMMA e4 = term
    { Ast.Pair(e1, e2, e3, e4) }

  | FST e = term
    { Ast.Fst(e) }

  | SND e = term
    { Ast.Snd(e) }

  | SUM LPAREN e1 = term COMMA e2 = term RPAREN
    { Ast.Sum(e1, e2) }

  | INR UNDERSCORE e1 = term LPAREN e2 = term RPAREN
    { Ast.Inr(e1, e2) }

  | INL UNDERSCORE e1 = term LPAREN e2 = term RPAREN
    { Ast.Inl(e1, e2) }

  | CASE LBRACKET z=var_name DOT c = term RBRACKET LPAREN e1=term COMMA x=var_name DOT e2 = term COMMA y = var_name DOT e3=term RPAREN
    { Ast.Case(e1, (z, c), (x, e2), (y, e3))}

  | INT
    { Ast.IntType }

  | EQ LPAREN e1=term COMMA e2=term COMMA e3=term RPAREN
    { Ast.Eq(e1, e2, e3) }

  | REFL LPAREN e=term RPAREN
    { Ast.Refl(e) }

  | TYPE e = NUMERAL
    {Ast.Type e}



infix_term: mark_location(infix_term_) { $1 }
infix_term_:
  | e=app_term_
    { e }

  | e2=infix_term oploc=infix e3=infix_term
    { let {Naming.data=op; loc} = oploc in
      let op = Naming.locate ~loc (Ast.Var op) in
      let e1 = Naming.locate ~loc (Ast.App (op, e2)) in
      Ast.App (e1, e3)
    }

app_term: mark_location(app_term_) { $1 }
app_term_:
  | e=prefix_term_
    { e }

  | e1=app_term e2=prefix_term
    { Ast.App (e1, e2) }

prefix_term: mark_location(prefix_term_) { $1 }
prefix_term_:
  | e=simple_term_
    { e }

  | oploc=PREFIXOP e2=prefix_term
    { let {Naming.data=op; loc} = oploc in
      let op = Naming.locate ~loc (Ast.Var op) in
      Ast.App (op, e2)
    }


simple_term : mark_location(simple_term_) { $1 }
simple_term_:
  | LPAREN e=term_ RPAREN
    { e }

  | x=var_name
    { Ast.Var(x) }

  | i = NUMERAL
    { Ast.Num(i) }


var_name:
  | NAME
    { Naming.Name($1) }

  | LPAREN op=infix RPAREN
    { op.Naming.data }

  | LPAREN op=prefix RPAREN
    { op.Naming.data }

  | UNDERSCORE
    { Naming.Dummy }


%inline infix:
  | op=INFIXOP0
    { op }

  | op=INFIXOP1
    { op }

  | op=INFIXOP2
    { op }

  | op=INFIXOP3
    { op }

  | op=INFIXOP4
    { op }


%inline prefix:
  | op=PREFIXOP
    { op }

lambda_abstraction:
  | lst=nonempty_list(typed_binder)
    { lst }

prod_abstraction:
  | lst=nonempty_list(typed_binder)
    { lst }

sigma_abstraction:
  | lst=nonempty_list(typed_binder)
    { lst }

typed_binder: mark_location(typed_binder_) { $1 }
typed_binder_:
  | LPAREN xs=nonempty_list(var_name) COLON t=term RPAREN
    { (xs, t) }

/* bind1: mark_location(plain_bind1) { $1 } */
/* plain_bind1: */
/*   | xs = nonempty_list(NAME) COLON t = term */
/*     { (List.map (fun x -> Util.Naming.Name x) xs, t) } */

/* /\* binds: *\/ */
/*   | LPAREN b = bind1 RPAREN */
/*     { [b] } */
/*   | LPAREN b = bind1 RPAREN lst = binds */
/*     { b :: lst } */


/* binder: mark_location(binder_) { $1 } */
/* binder_: */
/*   | LPAREN xs=nonempty_list(var_name) COLON t=term RPAREN */
/*     { (xs, t) } */

/*   | x=var_name */
/*     { ([x], {Util.Naming.data = Ast.Type 1; loc = Util.Naming.nowhere}) } */

mark_location(X):
  | x=X
    { Naming.locate ~loc:(Naming.make $startpos $endpos) x }
