open Main_defs
open Solution

let compile_and_simulate cfg info file net fs =
   let path = Filename.remove_extension file in
   let name = Filename.basename path in
   let dir = Filename.dirname path in
   let name = String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) name in
   let newpath = dir ^ "/" ^ name in
     Compile.compile_ocaml newpath net;
     Loader.simulate newpath

let main =
  Printexc.record_backtrace true;
  let cfg, info, file, decls = parse_input Sys.argv in
  let cfg, info, file, net, fs = process_input cfg info file decls in
  (* if cfg.check_monotonicity then *)
  (*   checkPolicy info cfg file decls; *)
  let networkOp =
      if cfg.smt then run_smt file
      else if cfg.random_test then run_test
      else if cfg.simulate then run_simulator
      else if cfg.compile then
        (compile_and_simulate cfg info file net []; failwith "todo")
      else exit 0
  in
  if cfg.compress >= 0 then
    begin
      compress file info net cfg fs (run_smt file)
    end
  else
    begin
      match networkOp cfg info net fs with
      | CounterExample sol, fs -> print_solution (apply_all sol fs)
      | Success (Some sol), fs ->
         Printf.printf "No counterexamples found\n";
         print_solution (apply_all sol fs)
      | Success None, _ ->
         Printf.printf "No counterexamples found\n"
    end
