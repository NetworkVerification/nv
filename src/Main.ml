open Main_defs
open Solution

let main =
  let cfg, info, file, decls = parse_input Sys.argv in
  let networkOp =
      if cfg.smt then run_smt file
      else if cfg.random_test then run_test
      else if cfg.simulate then run_simulator
      else run_simulator
  in
  if cfg.compress >= 0 then
    begin
      compress file info decls cfg networkOp
    end
  else
    begin
      match networkOp cfg info decls with
      | CounterExample sol, Some fs -> print_solution (apply_all sol fs)
      | CounterExample sol, None -> print_solution sol
      | Success _, _ -> Printf.printf "No counterexamples found\n"
    end
