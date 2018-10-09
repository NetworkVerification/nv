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
open Slicing
open Syntax
open Typing

exception Success
   
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
  | Unsat -> Unsat
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution -> (* print_solution (apply_all solution fs) *)
     Sat (apply_all solution fs)

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
  | None -> ()
  | Some sol ->
      print_newline () ;
      print_string [Bold] "Test cases: " ;
      Printf.printf "%d\n" stats.iterations ;
      print_string [Bold] "Rejected: " ;
      Printf.printf "%d\n" stats.num_rejected ;
      print_solution (apply_all sol fs)

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
          , QueueSet.empty Unsigned.UInt32.compare )
      | Some b -> Srp.simulate_declarations_bound decls b
    in
    print_solution (apply_all solution fs) ;
    match QueueSet.pop q with
    | None -> ()
    | Some _ ->
        print_string [] "non-quiescent nodes:" ;
        QueueSet.iter
          (fun q ->
            print_string [] (Unsigned.UInt32.to_string q ^ ";") )
          q ;
        print_newline () ;
        print_newline ()
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"
        
let compress info decls cfg networkOp =
  let decls = Inline.inline_declarations info decls in
  let network =
    match
      ( get_merge decls
      , get_trans decls
      , get_init decls
      , get_nodes decls
      , get_edges decls
      , get_attr_type decls
      , get_assert decls )
    with
    | Some emerge, Some etrans, Some einit, Some n, Some es, Some aty, Some eassert ->
       let graph = Graph.add_edges (Graph.create n) es in
       { attr_type = aty; init = einit; trans = etrans;
         merge = emerge; assertion = eassert; graph = graph }
    | _ ->
       Console.error
         "missing definition of nodes, edges, merge, trans, init or assert"
  in

  (* partially evaluate the functions of the network *)
  let transMap = Abstraction.partialEvalTrans network.graph network.trans in
  let mergeMap = Abstraction.partialEvalMerge network.graph network.merge in
  let initMap = Slicing.partialEvalInit network in
  let assertMap = Slicing.partialEvalAssert network in
  
  (* find the prefixes that are relevant to the assertions *)
  let prefixes = Slicing.relevantPrefixes assertMap in
  (* find where each prefix is announced from *)
  let slices = Slicing.findInitialSlices initMap in
  (* keep only the relevant slices, i.e. prefixes that are used by the assertion *)
  let relevantSlices = BatMap.filter (fun pre _ -> BatSet.mem pre prefixes) slices in
  (* each set of prefixes represents an SRP *)
  (* there is a slight overapproximation here: if a prefix is not used
     by the assertion, but some other prefix that is announced from
     the same node is then this prefix is not sliced out. This is
     sound, but it can be optimized in the future *)
  let relevantSliceGroups = Collections.groupKeysByValue relevantSlices in

  BatSet.iter
    (fun prefixes -> 
      let rec loop (f: AbstractionMap.abstractionMap) (ds: Graph.Vertex.t BatSet.t) =
        (* build abstract network *)
        let decls = Abstraction.buildAbstractNetwork f network.graph mergeMap transMap
                                                     initMap assertMap ds
                                                     network.attr_type cfg.compress in
        match networkOp cfg info decls with
        | Unsat -> ()
        | Sat sol ->
           (* find the abstraction function *)
           (* let f = Abstraction.findAbstraction network.graph transMap mergeMap ds in *)
           (*TODO: loop if necessary *)
           let groups = AbstractionMap.printAbstractGroups f "\n" in
           Console.show_message groups Console.T.Blue "Abstract groups";
           print_solution sol
        | _ -> Console.error "Solver returned unknown"
      in
      (* get a prefix from this class of prefixes *)
      let pre = BatSet.min_elt prefixes in
      (* find the nodes this class is announced from *)
      let ds = BatMap.find pre relevantSlices in
      (* find the initial abstraction function for these destinations *)
      let f = Abstraction.findAbstraction network.graph transMap mergeMap ds in
      loop f ds) relevantSliceGroups
  
let main =
  let cfg, rest = argparse default "nv" Sys.argv in
  Cmdline.set_cfg cfg ;
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  if cfg.compress >= 0 then
    begin
      let networkOp = if cfg.smt then run_smt
                      else run_smt
                      (* else if cfg.random_test then run_test *)
                      (* else run_simulator *)
      in
      compress info decls cfg networkOp
    end
  else
    begin
      if cfg.smt then
        begin
          match run_smt cfg info decls with
          | Sat sol -> print_solution sol
          | _ -> ()
        end;
      if cfg.random_test then run_test cfg info decls ;
      if cfg.simulate then run_simulator cfg info decls
    end
