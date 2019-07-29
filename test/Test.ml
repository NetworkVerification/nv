open OUnit2;;

let all_tests =
  "tests" >:::
  [
    (* Test_BDDs.tests; *)
    Test_end_to_end.tests;
  ]
;;

run_test_tt_main all_tests;;
