open OUnit2;;

let all_tests =
  "tests" >:::
  [
    Test_BDDs.tests;
  ]
;;

run_test_tt_main all_tests;;
