open Nv.Main_defs
open Nv_solution
open Nv_lang

let main_func () =
  Printexc.record_backtrace true;
  let inputs = parse_input Sys.argv in
  List.iter (fun ((cfg: Cmdline.t), info, file, net, fs) ->
      (* if cfg.check_monotonicity then *)
      (*   checkPolicy info cfg file decls; *)
      let networkOp =
        if cfg.smt then run_smt file
        else if cfg.simulate then run_simulator
        else if cfg.compile then run_compiled file
        else exit 0
      in
      (* Don't know how to do this over declarations *)
      begin
        match networkOp cfg info net fs with
        | CounterExample sol, fs -> Solution.print_solution (apply_all sol fs)
        | Success (Some sol), fs ->
          Printf.printf "No counterexamples found\n";
          Solution.print_solution (apply_all sol fs)
        | Success None, _ ->
          Printf.printf "No counterexamples found\n"
      end) inputs

let main =
  Nv_utils.Profile.time_profile_absolute "Entire Program" main_func
