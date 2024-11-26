(* open Core.Typecheck *)
(* open Core.Ast *)
(* open Core.Context *)
(* open Core.Evaluation *)
(* open Util.Naming *)
(* open OUnit2 *)
(* open Utilities *)
(* let context3 : ctx = (create_context_0 3) *)
(* let x : variable = Fresh("x", 1) *)
(* let y : variable = Fresh("x", 2) *)

(* let e1 : expr = mk_var x *)
(* let e2 : expr = mk_lambda (x, mk_universe (Num 0), mk_var x) *)
(* let e3 : expr = mk_app (mk_var x) (mk_var y) *)
(* let e4 : expr = mk_pi (x, mk_universe (Num 0), mk_universe (Num 1)) *)
(* let e5 : expr = mk_sigma (x, mk_universe (Num 0), mk_universe (Num 1)) *)
(* let e6 : expr = mk_pair (mk_var x) (mk_var y) *)
(* let e7 : expr = mk_fst (mk_var x) (mk_var y) *)
(* let e8 : expr = mk_snd (mk_var x) (mk_var y) *)



(* let make_record (e : expr) = *)
(*   make_nowhere (convert_abstract_parse e) *)

(* let infer_type_test_suite = *)
(*   "infer_type_test_suite">::: *)
(*   [ *)
(*     "infer_type_t1">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e1)))) *)
(*       (mk_universe (Num 0)); *)

(*     "infer_type_t2">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e2)))) *)
(*       (mk_pi (x, mk_universe (Num 0), mk_universe (Num 0))); *)

(*     "infer_type_t3">:: *)
(*     (fun _ -> *)
(*       try *)
(*         let _ = infer_type context3 (make_nowhere (convert_abstract_parse e3)) in *)
(*         assert_failure "Expected FUNCTION_EXPECTED exception" *)
(*       with *)
(*         Error(_) -> () *)
(*     ); *)

(*     "infer_type_t4">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e4)))) *)
(*       (mk_universe (Num 2)); *)

(*     "infer_type_t5">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e5)))) *)
(*       (mk_universe (Num 2)); *)

(*     "infer_type_t6">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e6)))) *)
(*       (mk_sigma ((fresh (Name "x")), mk_universe (Num 0), mk_universe (Num 0))); *)

(*     "infer_type_t7">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse (e7))))) *)
(*       (mk_universe (Num 0)); *)

(*     "infer_type_t8">:: *)
(*     check_equal_expression *)
(*       (mk (infer_type context3 (make_nowhere (convert_abstract_parse e8)))) *)
(*       (mk_universe (Num 0)); *)
(*   ] *)

(* let check_type_test_suite = *)
(*   "check_type_test_suite">::: *)
(*   [ *)
(*     "check_type_t1">:: *)
(*     check_equal_bool *)
(*     ( *)
(*       true *)
(*     ) *)
(*     ( *)
(*       (check_type context3 (make_record e1) (make_record (mk_universe (Num 0)))) *)

(*     ); *)
(*     "check_type_t2">:: *)
(*      check_equal_bool *)
(*      ( *)
(*        true *)
(*      ) *)
(*      ( *)
(*         (check_type context3 (make_record e2) (make_record (mk_pi (x, mk_universe (Num 0), mk_universe (Num 0))))) *)
(*      ); *)
(*     "check_type_t3">:: *)
(*      check_equal_bool *)
(*      ( *)
(*        true *)
(*      ) *)
(*      ( *)
(*        (check_type context3 (make_record e6) (make_record (mk_sigma (y, mk_universe (Num 0), mk_universe (Num 0))))) *)
(*      ); *)
(*     "check_type_t4">:: *)
(*       check_equal_bool *)
(*       ( *)
(*       false *)
(*       ) *)
(*       ( *)
(*         (check_type context3 (make_record e1) (make_record (mk_universe (Num 1)))) *)
(*       ); *)

(*     "check_type_t5">:: *)
(*       check_equal_bool *)
(*       (false) *)
(*       ( *)
(*         (check_type context3 (make_record e2) (make_record (mk_universe (Num 0)))) *)
(*       ); *)

(*     "check_type_t6">:: *)
(*     check_equal_bool *)
(*       ( *)
(*         false *)
(*       ) *)
(*       ( *)
(*         (check_type context3 (make_record e6) (make_record (mk_pi (x, mk_universe (Num 0), mk_universe (Num 0))))) *)
(*       ); *)
(*   ] *)

(* let () = *)
(*   run_test_tt_main check_type_test_suite; *)
(*   run_test_tt_main infer_type_test_suite *)