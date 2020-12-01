open Nv.Main_defs
open Nv_solution
open Nv_lang
open Cmdline

let main_func () =
  Printexc.record_backtrace true;
  let cfg, info, file, net, fs = parse_input Sys.argv in
  (* if cfg.check_monotonicity then *)
  (*   checkPolicy info cfg file decls; *)
  let networkOp =
    if cfg.smt
    then run_smt file
    else if cfg.simulate
    then run_simulator
    else if cfg.compile
    then run_compiled file
    else exit 0
  in
  (* Don't know how to do this over declarations *)
  let results = networkOp cfg info net fs in
  List.iter
    (fun r ->
      match r with
      | CounterExample sol, fs -> Solution.print_solution (apply_all sol fs)
      | Success (Some sol), fs ->
        Printf.printf "No counterexamples found\n";
        Solution.print_solution (apply_all sol fs)
      | Success None, _ -> Printf.printf "No counterexamples found\n")
    results
;;

let main = Nv_utils.Profile.time_profile_absolute "Entire Program" main_func
