open Main_defs
open Solution

let main =
  Printexc.record_backtrace true;
  let cfg, info, file, net, fs = parse_input Sys.argv in
  (* if cfg.check_monotonicity then *)
  (*   checkPolicy info cfg file decls; *)
  let networkOp =
      if cfg.smt then run_smt file
      (* else if cfg.random_test then run_test *)
      else if cfg.simulate then run_simulator
      else exit 0
  in
  if cfg.compress >= 0 then
    begin
      compress file info net cfg fs (run_smt file)
    end
  else
    begin
      match networkOp cfg info net fs with
      | CounterExample sol, Some fs -> print_solution (apply_all sol fs)
      | CounterExample sol, None -> print_solution sol
      | Success (Some sol), fs ->
         Printf.printf "No counterexamples found\n";
         print_solution (match fs with None -> sol | Some fs -> apply_all sol fs)
      | Success None, _ ->
         Printf.printf "No counterexamples found\n"
    end
