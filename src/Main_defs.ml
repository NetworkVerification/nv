open ANSITerminal
open Cmdline
open Inline
open Interp
open Hashcons
open Printing
open Quickcheck
open Renaming
open Smt
open Solution
open Syntax
open Typing

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
  let decls = Inline.inline_declarations info ds in
  let decls, f = Renaming.alpha_convert_declarations decls in
  let fs = f :: fs in
  let decls = Typing.infer_declarations info decls in
  let res, fs =
    if cfg.unroll_maps then (
      try
        let decls, vars, f = MapUnrolling.unroll info decls in
        let decls = Inline.inline_declarations info decls in
        let fs = f :: fs in
        (Smt.solve decls ~symbolic_vars:vars, fs)
      with MapUnrolling.Cannot_unroll e ->
        let msg =
          Printf.sprintf
            "unable to unroll map due to non constant index: %s"
            (Printing.exp_to_string e)
        in
        Console.warning msg ;
        (Smt.solve decls ~symbolic_vars:[], fs) )
    else (Smt.solve decls ~symbolic_vars:[], fs)
  in
  match res with
  | Unsat ->
    print_string [green; Bold] "Success: " ;
    Printf.printf "No assertions can be violated\n";
    false
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
    print_solution (apply_all solution fs);
    match solution.assertions with
    | None -> true
    | Some m -> Graph.VertexMap.for_all (fun _ b -> b) m

let run_test cfg info ds =
  let fs = [init_renamer] in
  let (sol, stats), fs =
    if cfg.smart_gen then
      let ds, f = Renaming.alpha_convert_declarations ds in
      let fs = f :: fs in
      let ds = Inline.inline_declarations info ds in
      (Quickcheck.check_smart info ds ~iterations:cfg.ntests, fs)
    else (Quickcheck.check_random ds ~iterations:cfg.ntests, fs)
  in
  match sol with
  | None -> false
  | Some sol ->
    print_newline () ;
    print_string [Bold] "Test cases: " ;
    Printf.printf "%d\n" stats.iterations ;
    print_string [Bold] "Rejected: " ;
    Printf.printf "%d\n" stats.num_rejected ;
    print_solution (apply_all sol fs);
    true

let run_simulator cfg info decls =
  let fs, decls =
    if cfg.inline then
      let decls, f = Renaming.alpha_convert_declarations decls in
      let decls = Inline.inline_declarations info decls in
      ([f; init_renamer], decls)
    else ([init_renamer], decls)
  in
  try
    let solution, q =
      match cfg.bound with
      | None ->
        ( Srp.simulate_declarations decls
        , QueueSet.empty Integer.compare )
      | Some b -> Srp.simulate_declarations_bound decls b
    in
    print_solution (apply_all solution fs) ;
    ( match QueueSet.pop q with
      | None -> ()
      | Some _ ->
        print_string [] "non-quiescent nodes:" ;
        QueueSet.iter
          (fun q ->
             print_string [] (Integer.to_string q ^ ";") )
          q ;
        print_newline () ;
        print_newline () ;
    );
    match solution.assertions with
    | None -> true
    | Some m -> Graph.VertexMap.for_all (fun _ b -> b) m
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

let parse_input (args : string array)
  : Cmdline.t * Console.info * Syntax.declarations =
  let cfg, rest = argparse default "nv" args in
  Cmdline.set_cfg cfg ;
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  (cfg, info, decls)
