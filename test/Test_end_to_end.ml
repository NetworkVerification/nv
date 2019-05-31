open OUnit2
open Main_defs

type testfun =
  string ->
  Cmdline.t ->
  Console.info ->
  Syntax.network ->
  (Solution.t -> Solution.t) list ->
  Main_defs.answer * ((Solution.t -> Solution.t) list)

type test = { testname: string; args: string array; testfun: testfun; expected: bool }

(* Expected results should correspond to this function *)
let bool_of_answer (a : Main_defs.answer * ((Solution.t -> Solution.t) list)) =
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
    args = Array.of_list ["nv"; "-s"; filename];
    testfun = (fun _ cfg info decls fs -> run_simulator cfg info decls fs);
    expected;
  }
;;

let smt_test filename expected: test =
  {
    testname = filename ^ "_smt";
    args= Array.of_list ["nv"; "-m"; filename];
    testfun = run_smt;
    expected;
  }
;;

let unboxed_test filename expected: test =
  {
    testname = filename ^ "_unboxed";
    args = Array.of_list ["nv"; "-m"; "-unbox"; filename];
    testfun = run_smt;
    expected;
  }
;;

(*** Suites of tests ***)
let simulator_tests =
  List.map (fun (f,b) -> simulator_test f b)
    [
      ("examples/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", true);
      ("examples/failure2.nv", true);
      ("examples/fattree.nv", true);
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

let smt_tests =
  List.map (fun (f,b) -> smt_test f b)
    [
      ("examples/debug-combine.nv", true);
      (* Takes forever? *)
      (* ("examples/batfish.nv", false); *)
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", false);
      ("examples/failure2.nv", false);
      ("examples/fattree.nv", true);
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

let unboxed_tests =
  List.map (fun (f,b) -> unboxed_test f b)
    [
      ("examples/debug-combine.nv", true);
      ("examples/batfish.nv", false);
      ("examples/diamond.nv", true);
      ("examples/diamond-ospf.nv", true);
      ("examples/env.nv", true);
      ("examples/failure.nv", false);
      ("examples/failure2.nv", false);
      ("examples/fattree.nv", true);
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

(*
   List of files we will run end-to-end tests on. Feel free to add
   more; just make sure they terminate quickly.

   The format is (filename, simluate_success, smt_success), where
   simluate_success is true if we expect the simulator to succeed
   (with default inputs), and smt_success is true if we expect the
   smt solver to succeed
*)

let make_ounit_test test =
  test.testname >:: fun _ ->
    let cfg, info, file, decls, fs = parse_input test.args in
    let result = bool_of_answer @@ test.testfun file cfg info decls fs in
    assert_equal ~printer:string_of_bool test.expected result;
;;

(* Name the test cases and group them together *)
let tests =
  "Test_end_to_end"
  >:::
  List.map make_ounit_test @@
  simulator_tests @
  smt_tests @
  unboxed_tests @
  [] (* So we can easily comment out the last actual test *)
