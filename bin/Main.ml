let () =
  let module Md = Main_defs in
    Printexc.record_backtrace true;
    let cfg, info, file, net, fs = Md.parse_input Sys.argv in
    (* if cfg.check_monotonicity then *)
    (*   checkPolicy info cfg file decls; *)
    let networkOp =
        if cfg.smt then Md.run_smt file
        else if cfg.random_test then Md.run_test
        else if cfg.simulate then Md.run_simulator
        else exit 0
    in
    if cfg.compress >= 0 then
      begin
        (* TODO: why doesn't this use networkOp? *)
        Md.compress file info net cfg fs (Md.run_smt file)
      end
    else
      begin
        let module Sol = Solution in 
          match networkOp cfg info net fs with
          | CounterExample sol, fs -> Sol.print_solution (apply_all sol fs)
          | Success (Some sol), fs ->
             Printf.printf "No counterexamples found\n";
             Sol.print_solution (apply_all sol fs)
          | Success None, _ ->
             Printf.printf "No counterexamples found\n"
        end
