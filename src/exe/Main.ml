open Nv_lib.Main_defs
open Nv_solution

let main_func () =
  Printexc.record_backtrace true;
let cfg, info, file, net, fs = parse_input Sys.argv in
  (* if cfg.check_monotonicity then *)
  (*   checkPolicy info cfg file decls; *)
  let networkOp =
      if cfg.smt then run_smt file
      else if cfg.random_test then run_test
      else if cfg.simulate then run_simulator
      else if cfg.compile then run_compiled file
      else exit 0
  in
  if cfg.compress >= 0 then
    begin
      compress file info net cfg fs (run_smt file)
    end
  else
    begin
      match networkOp cfg info net fs with
      | CounterExample sol, fs -> Solution.print_solution (apply_all sol fs)
      | Success (Some sol), fs ->
         Printf.printf "No counterexamples found\n";
         Solution.print_solution (apply_all sol fs)
      | Success None, _ ->
         Printf.printf "No counterexamples found\n"
    end

let main =
  Nv_utils.Profile.time_profile_absolute "Entire Program" main_func
