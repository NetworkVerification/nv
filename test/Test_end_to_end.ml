(* open BatSet *)
open OUnit2
open Main_defs

(*
   List of files we will run end-to-end tests on. Feel free to add
   more; just make sure they terminate quickly.

   The format is (filename, simluate_success, smt_success), where
   simluate_success is true if we expect the simulator to succeed
   (with default inputs), and smt_success is true if we expect the
   smt solver to succeed
*)
let files_to_test : (string * bool * bool) list =
  [
    ("examples/debug-combine.nv", true, true);
    ("examples/diamond.nv", true, true);
    ("examples/diamond-ospf.nv", true, true);
    ("examples/env.nv", true, true);
    ("examples/failure.nv", true, false);
    ("examples/failure2.nv", true, false);
    (* ("examples/fattree.nv", true, true); *)
    ("examples/map.nv", true, true);
    ("examples/map2.nv", false, false);
    ("examples/minesweeper.nv", true, false);
    ("examples/property.nv", true, false);
    ("examples/set.nv", true, true);
    ("examples/simple.nv", true, true);
    ("examples/symbolic.nv", true, false);
    ("examples/symbolic2.nv", true, false);
  ]
;;

let make_test file =
  let filename, sim_success, smt_success = file in
  filename >:: fun _ ->
    let args = Array.of_list ["nv"; "-s"; "-m"; filename] in
    let cfg, info, decls = parse_input args in
    assert_equal ~printer:string_of_bool sim_success @@ run_simulator cfg info decls;
    assert_equal ~printer:string_of_bool smt_success @@ run_smt cfg info decls;
;;

(* Name the test cases and group them together *)
let tests =
  "Test_end_to_end"
  >:::
  List.map make_test files_to_test
