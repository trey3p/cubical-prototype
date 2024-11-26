open Core.Precondition
open Core.Ast
open Core.Eval
open Util.Naming
open Utilities
open OUnit2
open Core.Error
let empty =  (Core.Dimctx.empty, Core.Cofibctx.initial, Core.Varctx.empty)
let empty_partial =  (Core.Dimctx.empty, Cofib.make Top [], Core.Varctx.empty)
let partial_x_0 =  (Core.Dimctx.empty, Cofib.make Top [(Name "p")],(Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None) )
let partial_x_1 =  (Core.Dimctx.empty, Cofib.make Top [(Name "p")],(Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 1) None) )

let sys = [
        { cofibration = Eq(X (Name "x"), Zero); expression = Num 1 };
        { cofibration = Eq(X (Name "x"), One);  expression = Num 1};
      ]

let sys_var = [
        { cofibration = Eq(X (Name "x"), Zero); expression = Var (Name "x") };
        { cofibration = Eq(X (Name "x"), One);  expression = Var (Name "x")};
      ]

let sys_to_type0 =
   [
        { cofibration = Eq(X (Name "x"), Zero); expression = (Type 0)};
        { cofibration = Eq(X (Name "x"), One);  expression = (Type 0)};
      ]


let sys_to_type1 =
   [
        { cofibration = Eq(X (Name "y"), Zero); expression = (Type 1)};
        { cofibration = Eq(X (Name "y"), One);  expression = (Type 1)};
      ]


let example_system_list : system list =
  [
    {
      cofibration = Eq (X (Name "x"), Zero);
      expression = Num 1
    };
    {
      cofibration = Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero));
      expression = InP(Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero)), (Num 1))
    };
    {
      cofibration = And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero));
      expression = InP( And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero)), (Num 1))
    };
    {
      cofibration = Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One));
      expression = InP(Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One)), (Num 1))
    };
    {
      cofibration = Top;
      expression = InP(Top, (Num 1))
    }
  ]

let example_ident_sys : system list =
  [
    {
      cofibration = Eq (X (Name "x"), Zero);
      expression = Num 1
    };
    {
      cofibration = Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero));
      expression = (Num 1)
    };
    {
      cofibration = And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero));
      expression = (Num 1)
    };
    {
      cofibration = Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One));
      expression = (Num 1)
    };
    {
      cofibration = Top;
      expression = (Num 1)
    }
  ]



let in_int = InB(IntType, example_system_list, (Num 1))

let ctx_x_0 = (Core.Ctx.extend_context empty (Name "x") (Type 0) None)
let loop_term =
  InB(Type 0,
     sys_var, Var (Name "x"))

let loop_term_int =
  InB(IntType,
     sys_var, Var (Name "x"))

let loop_term_num =
  InB((IntType),
     sys, Num 1)

let loop =
  IMap((Name "x"), loop_term)

let loop_app = IApp(loop, X(Name "x"))

let precon_synth_test_suite =
  "precon_synth_test_suite">:::
  [
    "base_neutral_synth">::
    check_equal_precons
    (
      let p, _ = neutral_norm_synth empty_partial (Num 1) [] in
      let p', _ = List.split p in p'
    )
    (
      [(Num 1, Top)]
    )
    ;
    "base_neutral_synth_on_precon1">::
    check_equal_precons
    (
      let p, _ = List.split (neutral_synth_on_precon empty_partial [(Num 1, Top)]) in
      p
    )
    (
       [(Num 1, Top)]
    )
    ;
    "base_neutral_synth_on_precon2">::
    check_equal_precons
    (
      let p, _ = List.split (neutral_synth_on_precon empty_partial  [(Num 1, Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)))]) in
      p
    )
    (
       [(Num 1, Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)))]
    )
    ;
    "loop_synth_cofib_sys">::
    check_equal_precons
    (
      systems_to_precon sys
    )
    (
      [(Num 1, Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)))]
    )
    ;
    "loop_synth_cofib_hd">::
    check_equal_precons
    (

      head_red_synth (Core.Dimctx.empty, Core.Cofibctx.initial, (Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None)) loop_term
    )
    (
      [(Var(Name "x"), Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)))]
    );
    "variable_hd">::
    check_equal_precons
    (
      head_red_synth (Core.Dimctx.empty, Cofib.make Top [],(Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None)) (Var (Name "x"))
    )
    (
      [( Var (Name "x"), Top)]
    );
    "term_norm_loop_map">::
    check_equal_expression
    (
      term_norm (Core.Ctx.extend_context empty (Name "x") (IntType) None)  (IMapT(Name "x", Bound(Type 0, sys))) loop
    )
    (
      loop
    );
    "synth_loop_int_num">::
    check_equal_expression
    (
      Core.Typecheck.synth empty loop_term_num
    )
    (
      Bound( IntType, sys)
    );
    "synth_loop_int_var">::
    check_equal_expression
    (
      Core.Typecheck.synth (Core.Ctx.extend_context empty (Name "x") (IntType) None)  loop_term_int
    )
    (
      Bound(IntType, sys_var)
    );
    "synth_loop_map">::
    check_equal_expression
    (
      Core.Typecheck.synth (Core.Ctx.extend_context empty (Name "x") (Type 0) None) loop
    )
    (
      IMapT(Name "x", Bound(Type 0, sys_var))
    );
    "norm_precon_loop_map">::
    check_equal_precons
    (
      norm_precon partial_x_0 [(pre_mk loop Logic.Cofibration.Top)]
    )
    (
      [(loop, Top)]
    );
    "loop_map_tm_norm">::
    check_equal_expression
    (
      term_norm ctx_x_0 (IMapT(Name "x", Bound(Type 0, sys_var))) loop
    )
    (
     loop
    );
    "term_norm_app_loop">::
    check_equal_expression
    (
      term_norm ctx_x_0 (Bound(Type 0, sys_var)) (IApp(loop, (X (Name "x"))))
    )
    (
      loop_term
    );
    "loop_map_tm_synth">::
    check_equal_precons
    (
      term_norm_synth (partial_x_0) (IMapT(Name "x", Bound(Type 0, sys_var))) loop
    )
    (
      [(loop, Top)]
    );
    "loop_app_hd">::
    check_equal_precons
    (

        try
          head_red_synth (Core.Dimctx.empty, Cofib.make Top [], (Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None)) loop_app
        with
        | Error err ->

            (* (Util.Naming.print err.Util.Naming.loc formatter); *)
            Util.Print.error "Error: %t" (Core.Error.print_error err.Util.Naming.data);  Format.eprintf "\n"; []

    )
    (
      [(loop_term, Logic.Cofibration.Top)]
    );
    "loop_app_hdmulti1">::
    check_equal_precons
    (

     multi_stephd_synth (Core.Dimctx.empty, Cofib.make Top [], (Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None)) [(loop_term, Logic.Cofibration.Top)]

    )
    (
      [(Var(Name "x"), Or(Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)), Top))]
    );

    "loop_synth_cofib_term">::
    check_equal_precons
    (
     term_norm_synth (Core.Dimctx.empty, Cofib.make Top [],(Core.Varctx.extend Core.Varctx.empty (Name "x") (Type 0) None) ) (Bound(Type 0, sys)) loop_term
    )
    (

      [(Var(Name "x"), Or(Eq(X (Name "x"), Zero),  Eq(X (Name "x"), One)))]

    );
    "loop_app_tm_nm_possible">::
    check_equal_precons
    (
      possible_precons (partial_x_0) (Bound(Type 0, sys_var)) loop_app
    )
    (
      [(loop_term, Top); (loop_app, Top)]
    );
    "loop_app_all_possible">::
    check_equal_precons
    (
      possible_precons (partial_x_0) (Bound(Type 0, sys_var)) loop_app
    )
    (
        [(loop_term, Top); (loop_app, Top)]
    );
    "loop_term_all_possible">::
    check_equal_precons
    (
      possible_precons (partial_x_0) (Bound(Type 0, sys_var)) loop_term
    )
    (
           [ (Var(Name "x"),  Or (Eq (X (Name "x"), Zero), Eq (X (Name "x"), One))); (loop_term, Top)]
    );
    "norm_precon_inp">::
    check_equal_precons
    (
      norm_precon empty [(OutP(InP(Top, Num 1)), Top)]
    )
    (
      [(Num 1, Top)]
    );
    "term_synth_inp">::
    check_equal_precons
    (
      term_norm_synth empty (Bound(IntType, example_system_list)) (OutP(InP(Top, Num 1)))
    )
    (
      [(Num 1, Top)]
    );
    "sys_precons">::
    check_equal_precons
    (
      systems_to_precon example_system_list
    )
    (

      [
    (
      Num 1, Logic.Cofibration.Eq (X (Name "x"), Zero)

    );
    (
        InP(Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero)), (Num 1)),
       Logic.Cofibration.Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero))

      );
    (
      InP( And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero)), (Num 1)),
       Logic.Cofibration.And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero))
    );
    (
     InP(Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One)), (Num 1)), Logic.Cofibration.Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One))

    );
    (
       InP(Top, (Num 1)), Logic.Cofibration.Top
     )
      ]
    );
    "inb_test">::
    check_equal_precons
    (
      let f (e', cof) = (term_norm partial_x_0 (Core.Typecheck.synth partial_x_0 e') e', cof) in
     fst(List.split ( neutral_synth_on_precon partial_x_0 (norm_precon partial_x_0 (List.map f (systems_to_precon example_system_list)))))

      (* ( 1, x = Zero), ( inp(1), y = One or z = Zero), ( inp(1), p and a ∧ b = Zero), ( inp(1), Bot or c ∨ d = One), ( inp(1), Top), *)
    )
    (

  [
    (
      Num 1, Logic.Cofibration.Eq (X (Name "x"), Zero)

    );
    (
        InP(Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero)), (Num 1)),
       Logic.Cofibration.Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero))

      );
    (
      InP( And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero)), (Num 1)),
       Logic.Cofibration.And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero))
    );
    (
     InP(Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One)), (Num 1)), Logic.Cofibration.Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One))

    );
    (
       InP(Top, (Num 1)), Logic.Cofibration.Top
     )
  ]
    );
    "in_int_tm_synth">::
    check_equal_precons
    (
       term_norm_synth (partial_x_0)  (Bound(IntType, example_system_list)) in_int
    )
    (

  [
    (
      Num 1, Logic.Cofibration.Eq (X (Name "x"), Zero)

    );
    (
        InP(Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero)), (Num 1)),
       Logic.Cofibration.Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero))

      );
    (
      InP( And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero)), (Num 1)),
       Logic.Cofibration.And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero))
    );
    (
     InP(Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One)), (Num 1)), Logic.Cofibration.Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One))

    );
    (
       InP(Top, (Num 1)), Logic.Cofibration.Top
     )
  ]
    );
    "in_int_all_possible">::
    check_equal_precons
    (
      possible_precons (partial_x_0) (Bound(IntType, example_system_list)) in_int
    )
    (

  [
    (
      Num 1, Logic.Cofibration.Eq (X (Name "x"), Zero)

    );
    (
        InP(Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero)), (Num 1)),
       Logic.Cofibration.Or (Eq (X (Name "y"), One), Eq (X (Name "z"), Zero))

      );
    (
      InP( And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero)), (Num 1)),
       Logic.Cofibration.And (Param (Name "p"), Eq (Meet (X (Name "a"), X (Name "b")), Zero))
    );
    (
     InP(Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One)), (Num 1)), Logic.Cofibration.Or (Bot, Eq (Join (X (Name "c"), X (Name "d")), One))

    );
    (
       InP(Top, (Num 1)), Logic.Cofibration.Top
     );
     (
       in_int, Logic.Cofibration.Top
     )
  ]
    );
    "sys_shrink">::
    check_equal_precons
    (
      systems_to_precon example_ident_sys
    )
    (
      []
    );
    "tm_nm_app_lam">::
    check_equal_precons
    (
      term_norm_synth partial_x_1 (Type 2) (App((Lambda(Name "x", Branch(sys_to_type0),  Branch(sys_to_type1))), Var(Name "x")))
    )
    (
      []
    );
    "tm_nm_lam">::
    check_equal_precons
    (
      term_norm_synth empty (Pi(Name "x", Type 1, Type 2)) (Lambda(Name "x", Branch(sys_to_type0),  Branch(sys_to_type1)))
    )
    (
      []
    );
    "tm_nm_pi">::
    check_equal_precons
    (
      term_norm_synth empty (Type 1) (Pi(Name "x", Branch(sys_to_type0), Branch(sys_to_type1)))
    )
    (
      []
    );
    "sub_precon_into_ex1">::
    check_equal_precons
    (
     sub_precon_into_ex (Name "x") (term_norm_synth partial_x_0 (Type 0) (Fst (Pair(Var(Name "x"), Branch(sys_to_type0), Name "x", Type 2)))) (Type 1)
    )
    (
      []
    );
    "head_red_synth_snd">::
    check_equal_precons
    (
     head_red_synth partial_x_0 (Snd (Pair(Var(Name "x"), Branch(sys_to_type0), Name "x", Type 1)))
    )
    (
      []
    );
    "norm_synth_preconty1">::
    check_equal_precons
    (
      norm_synth_preconty partial_x_0 [(Type 1, Top)] (Snd (Pair(Var(Name "x"), Branch(sys_to_type0), Name "x", Type 1)))
    )
    (
      []
    );
    "tm_nm_pair">::
    check_equal_precons
    (
      term_norm_synth partial_x_0 (Sigma(Name "x", (Type 0), Type 1))
        (Pair(Var(Name "x"), Branch(sys_to_type0), Name "x", Type 1))
    )
    (
      []
    );
    "tm_nm_sigma">::
    check_equal_precons
    (
      term_norm_synth empty (Type 1)  (Sigma(Name "x", Branch(sys_to_type0), Branch(sys_to_type1)))
    )
    (
      []
    );

  ]

let () =
  run_test_tt_main precon_synth_test_suite
