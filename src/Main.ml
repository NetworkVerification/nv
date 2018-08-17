open ANSITerminal
open Cmdline
open Syntax
open Printing
open Interp
open Typing
open Renaming
open Inline
open Quickcheck
open Smt
open Solution

let init_renamer sol =
  let drop_zero s = String.sub s 0 (String.length s - 1) in
  let syms =
    Collections.StringMap.fold
      (fun s v acc -> Collections.StringMap.add (drop_zero s) v acc)
      sol.symbolics Collections.StringMap.empty
  in
  {sol with symbolics= syms}

let rec apply_all s fs =
  match fs with [] -> s | f :: fs -> apply_all (f s) fs

let run_smt cfg info ds =
  let fs = [init_renamer] in
  let decls, f = Renaming.alpha_convert_declarations ds in
  let fs = f :: fs in
  let decls = Inline.inline_declarations info decls in
  let res, fs =
    if cfg.unroll_maps then (
      try
        let decls, vars, f = MapUnrolling.unroll info decls in
        let decls = Inline.inline_declarations info decls in
        let fs = f :: fs in
        (Smt.solve decls ~symbolic_vars:vars, fs)
      with MapUnrolling.Cannot_unroll _ ->
        Console.warning
          "unable to unroll map due to non constant index:" ;
        (Smt.solve decls ~symbolic_vars:[], fs) )
    else (Smt.solve decls ~symbolic_vars:[], fs)
  in
  match res with
  | Unsat -> ()
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution -> print_solution (apply_all solution fs)

let run_test cfg info ds =
  let fs = [init_renamer] in
  let (sol, stats), fs =
    if cfg.smart_gen then
      let ds, f = Renaming.alpha_convert_declarations ds in
      let fs = f :: fs in
      let ds = Inline.inline_declarations info ds in
      (Quickcheck.check_smart info ds ~iterations:20, fs)
    else (Quickcheck.check_random ds ~iterations:300, fs)
  in
  match sol with
  | None -> ()
  | Some sol ->
      print_newline () ;
      print_string [Bold] "Test cases: " ;
      Printf.printf "%d\n" stats.iterations ;
      print_string [Bold] "Rejected: " ;
      Printf.printf "%d\n" stats.num_rejected ;
      print_solution (apply_all sol fs)

let run_simulator cfg info decls =
  let fs = [init_renamer] in
  try
    let solution, q =
      match cfg.bound with
      | None -> (Srp.simulate_declarations decls, [])
      | Some b -> Srp.simulate_declarations_bound decls b
    in
    print_solution (apply_all solution fs) ;
    match q with
    | [] -> ()
    | qs ->
        print_string [] "non-quiescent nodes:" ;
        List.iter
          (fun q ->
            print_string [] (Unsigned.UInt32.to_string q ^ ";") )
          qs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

let main =
  let cfg, rest = argparse default "example" Sys.argv in
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  if cfg.verbose then (
    print_endline "** SRP Definition **" ;
    print_endline (Printing.declarations_to_string ds) ;
    print_endline "** End SRP Definition **" ) ;
  if cfg.smt then run_smt cfg info decls ;
  if cfg.random_test then run_test cfg info decls ;
  if cfg.simulate then run_simulator cfg info decls
