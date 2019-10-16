open OUnit2
open Nv_lib
open Nv_lang
open Nv_solution
open Main_defs

type testfun =
  string ->
  Cmdline.t ->
  Console.info ->
  Syntax.network ->
  (Solution.t -> Solution.t) list ->
  Main_defs.answer * ((Solution.t -> Solution.t) list)

type test = { testname: string;
              args: string array;
              testfun: testfun;
              expected: bool }

(* To account for the fact that all the filenames are relative to the nv
   directory, and dune runs the tests from a subdirectory of _build *)
let filename_prefix = "../../../"

(* Expected results should correspond to this function *)
let bool_of_answer (a : answer * ((Solution.t -> Solution.t) list)) =
  (* Print the final result to make sure we don't crash in the process,
     then return a bool *)
  begin
    match a with
    | CounterExample sol, fs -> Solution.print_solution (apply_all sol fs)
    | Success (Some sol), fs ->
      Printf.printf "No counterexamples found\n";
      Solution.print_solution (apply_all sol fs)
    | Success None, _ ->
      Printf.printf "No counterexamples found\n"
  end
  ;
  match a with
  | Success _, _ -> true
  | CounterExample _,_-> false
;;

let simulator_test filename expected: test =
  {
    testname = filename ^ "_simulator";
    args = Array.of_list ["nv"; "-s"; filename_prefix ^ filename];
    testfun = (fun _ cfg info decls fs -> run_simulator cfg info decls fs);
    expected;
  }
;;

let smt_test filename expected: test =
  {
    testname = filename ^ "_smt";
    args= Array.of_list ["nv"; "-m"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let bv_test filename expected: test =
  {
    testname = filename ^ "_bv";
    args = Array.of_list ["nv"; "-m"; "-unbox"; "-finite-arith"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let parallel_test filename expected: test =
  {
    testname = filename ^ "_parallel";
    args = Array.of_list ["nv"; "-m"; "-unbox"; "-smt-parallel"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let unboxed_test filename expected: test =
  {
    testname = filename ^ "_unboxed";
    args = Array.of_list ["nv"; "-m"; "-unbox"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let hiding_test filename expected: test =
  {
    testname = filename ^ "_hiding";
    args = Array.of_list ["nv"; "-m"; "-hiding"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let slicing_test filename expected: test =
  {
    testname = filename ^ "_slicing";
    args = Array.of_list ["nv"; "-m"; "-slicing"; filename_prefix ^ filename];
    testfun = run_smt;
    expected;
  }
;;

let compiler_test filename expected: test =
  {
    testname = filename ^ "_compiled";
    args = Array.of_list ["nv"; "-compile"; filename_prefix ^ filename];
    testfun = (fun _ cfg info decls fs -> run_compiled (filename_prefix ^ filename) cfg info decls fs);
    expected;
  }
;;

(*** Suites of tests ***)
let simulator_tests =
  List.map (fun (f,b) -> simulator_test f b)
    [
      ("examples/debugging/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", true);
      ("examples/failure2.nv", true);
      ("examples/FatTrees/fattree.nv", true);
      ("examples/map.nv", true);
      ("examples/map2.nv", false);
      ("examples/minesweeper.nv", true);
      ("examples/property.nv", true);
      ("examples/set.nv", true);
      ("examples/simple.nv", true);
      ("examples/symbolic.nv", true);
      ("examples/symbolic2.nv", true);
      ("examples/maprecord.nv", true);
      ("examples/maprecordpattern.nv", true);
      ("examples/maprecord2.nv", true);
      ("examples/record.nv", true);
      ("examples/recordwith.nv", true);

      ("examples/symbolic3.nv", true);
      ("examples/symbolicDecls.nv", true);
      ("examples/ospf-areas.nv", true);
    ]
;;

let compiler_tests =
  match Sys.getenv_opt "TRAVIS" with
  | Some "true" -> [] (* These tests are too fragile for travis atm *)
  | _ ->
  List.map (fun (f,b) -> compiler_test f b)
    [
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", true);
      (* ("examples/failure2.nv", true); *) (* TODO: Enable *)
      ("examples/FatTrees/fattree.nv", true);
      ("examples/map.nv", true);
      ("examples/map2.nv", false);
      ("examples/property.nv", true);
      ("examples/set.nv", true);
      ("examples/simple.nv", true);
      ("examples/symbolic.nv", true);
      ("examples/symbolic2.nv", true);
      ("examples/maprecord.nv", true);
      ("examples/maprecordpattern.nv", true);
      ("examples/maprecord2.nv", true);

      ("examples/symbolic3.nv", true);
      ("examples/symbolicDecls.nv", true);
    ]
;;


let unboxed_tests =
  List.map (fun (f,b) -> unboxed_test f b)
    [
      ("examples/debugging/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", false);
      ("examples/failure2.nv", false);
      ("examples/FatTrees/fattree.nv", true);
      ("examples/map.nv", true);
      ("examples/map2.nv", false);
      ("examples/minesweeper.nv", false);
      ("examples/property.nv", true);
      ("examples/set.nv", true);
      ("examples/simple.nv", true);
      ("examples/symbolic.nv", false);
      ("examples/symbolic2.nv", false);
      ("examples/maprecord.nv", true);
      ("examples/maprecordpattern.nv", true);
      ("examples/maprecord2.nv", true);
      ("examples/record.nv", true);
      ("examples/recordwith.nv", true);

      ("examples/symbolic3.nv", false);
      ("examples/symbolicDecls.nv", false);
      ("examples/ospf-areas.nv", true);
    ]
;;

let hiding_tests =
  List.map (fun (f,b) -> hiding_test f b)
    [
      ("examples/debugging/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", false);
      ("examples/failure2.nv", false);
      ("examples/FatTrees/fattree.nv", true);
      ("examples/map.nv", true);
      ("examples/map2.nv", false);
      ("examples/minesweeper.nv", false);
      ("examples/property.nv", true);
      ("examples/set.nv", true);
      ("examples/simple.nv", true);
      ("examples/symbolic.nv", false);
      ("examples/symbolic2.nv", false);
      ("examples/maprecord.nv", true);
      ("examples/maprecordpattern.nv", true);
      ("examples/maprecord2.nv", true);
      ("examples/record.nv", true);
      ("examples/recordwith.nv", true);

      ("examples/symbolic3.nv", false);
      ("examples/symbolicDecls.nv", false);
      ("examples/ospf-areas.nv", true);
    ]
;;

let slicing_tests =
  List.map (fun (f,b) -> slicing_test f b)
    [
      ("examples/debugging/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", false);
      ("examples/failure2.nv", false);
      ("examples/FatTrees/fattree.nv", true);
      ("examples/map.nv", true);
      ("examples/map2.nv", false);
      ("examples/minesweeper.nv", false);
      ("examples/property.nv", true);
      ("examples/set.nv", true);
      ("examples/simple.nv", true);
      ("examples/symbolic.nv", false);
      ("examples/symbolic2.nv", false);
      ("examples/maprecord.nv", true);
      ("examples/maprecordpattern.nv", true);
      ("examples/maprecord2.nv", true);
      ("examples/record.nv", true);
      ("examples/recordwith.nv", true);

      ("examples/symbolic3.nv", false);
      ("examples/symbolicDecls.nv", false);
      ("examples/ospf-areas.nv", true);
    ]
;;

let bv_tests =
  List.map (fun (f,b) -> bv_test f b)
    [
      ("examples/bitvectors/fattree125-bv-single.nv", true);
    ]
;;

let parallel_tests =
  List.map (fun (f,b) -> parallel_test f b)
    [
      ("examples/bitvectors/fattree125-bv-single.nv", true);
    ]
;;

let make_ounit_test test =
  test.testname >:: fun _ ->
    let cfg, info, file, decls, fs = parse_input test.args in
    let result = bool_of_answer @@ test.testfun file cfg info decls fs in
    assert_equal ~printer:string_of_bool test.expected result;
;;

(* Name the test cases and group them together *)
let tests =
  Printf.printf "%s\n" (Unix.getcwd ());
  "Test_end_to_end"
  >:::
  List.map make_ounit_test @@
  simulator_tests @
  unboxed_tests @
  hiding_tests @
  slicing_tests @
  bv_tests @
  parallel_tests @
  compiler_tests @
  [] (* So we can easily comment out the last actual test *)
