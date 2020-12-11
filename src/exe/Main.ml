open Nv.Main_defs
open Nv_solution
open Nv_lang
open Cmdline

let handle_op result =
  match result with
  | CounterExample sol, fs -> Solution.print_solution (apply_all sol fs)
  | Success (Some sol), fs ->
    Printf.printf "No counterexamples found\n";
    Solution.print_solution (apply_all sol fs)
  | Success None, _ -> Printf.printf "No counterexamples found\n"

let main_func () =
  Printexc.record_backtrace true;
  (* let inputs = parse_input Sys.argv in *)
  let cfg, info, file, decls, parts, fs = parse_input Sys.argv in
  (* if cfg.check_monotonicity then *)
  (*   checkPolicy info cfg file decls; *)
  (* List.iter
   *   (fun (cfg, info, file, net, fs) -> *)
      let networkOp =
        if cfg.smt
        then run_smt file cfg info decls parts fs
        else if cfg.simulate
        then [run_simulator cfg info decls fs]
        else if cfg.compile
        then [run_compiled file cfg info decls fs]
        else exit 0
      in
      let results = networkOp in
      List.iter handle_op results
    (* ) *)
    (* inputs *)
;;

let main = Nv_utils.Profile.time_profile_absolute "Entire Program" main_func
