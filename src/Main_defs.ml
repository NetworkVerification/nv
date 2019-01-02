open ANSITerminal
open Cmdline
open Inline
open Interp
open Hashcons
open Printing
open Quickcheck
open Renaming
open Smt2
open Solution
open Slicing
open Syntax
open Typing
open Abstraction
open BuildAbstractNetwork
open Lazy
open Profile

type answer =
  | Success of (Solution.t option)
  | CounterExample of Solution.t

let rec apply_all s fs =
  match fs with [] -> s | f :: fs -> apply_all (f s) fs

let smt_query_file =
  let counter = ref (-1) in
  fun (file: string) ->
  incr counter;
  lazy (open_out (file ^ "-" ^
                    (string_of_int !counter) ^ "-query"))
                                   
let run_smt file cfg info decls =
  let fs = [] in
  (* let decls = Inline.inline_declarations info decls in *)
  (* let decls = Typing.infer_declarations info decls in *)
  let decls, f = Renaming.alpha_convert_declarations decls in
  let fs = f :: fs in
  let decls =
    if cfg.unbox then
      begin
        smt_config.unboxing <- true;
        UnboxOptions.unbox decls |> TupleFlatten.flatten
      end
    else decls
  in

  let res, fs =
    if cfg.unroll_maps then (
      try
        let decls, vars, f = MapUnrolling.unroll info decls in
        let decls = Inline.inline_declarations info decls in
        let fs = f :: fs in
        (Smt2.solve info cfg.query (smt_query_file file) decls ~symbolic_vars:vars, fs)
      with MapUnrolling.Cannot_unroll e ->
        let msg =
          Printf.sprintf
            "unable to unroll map due to non constant index: %s"
            (Printing.exp_to_string e)
        in
        Console.warning msg ;
        (Smt2.solve info cfg.query (smt_query_file file) decls ~symbolic_vars:[], fs))
    else (Smt2.solve info cfg.query (smt_query_file file) decls ~symbolic_vars:[], fs)
  in
  match res with
  | Unsat -> (Success None, None)
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
     match solution.assertions with
     | None -> Success (Some solution), Some fs
     | Some m ->
        if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
          CounterExample solution, Some fs
        else
          Success (Some solution), Some fs

let run_test cfg info ds =
  let fs = [] in
  let (sol, stats), fs =
    if cfg.smart_gen then
      let ds, f = Renaming.alpha_convert_declarations ds in
      let fs = f :: fs in
      let ds = Inline.inline_declarations info ds in
      (Quickcheck.check_random ds ~iterations:cfg.ntests, fs) (*used to be check_smart *)
    else (Quickcheck.check_random ds ~iterations:cfg.ntests, fs)
  in
  match sol with
  | None -> (Success None, None)
  | Some sol ->
      print_newline () ;
      print_string [Bold] "Test cases: " ;
      Printf.printf "%d\n" stats.iterations ;
      print_string [Bold] "Rejected: " ;
      Printf.printf "%d\n" stats.num_rejected ;
      (CounterExample sol, Some fs)

let run_simulator cfg info decls =
  let fs, decls =
    if cfg.inline then
      (* why are we renaming here?*)
      let decls, f = Renaming.alpha_convert_declarations decls in
      let decls = Inline.inline_declarations info decls in
      ([f], decls)
    else ([], decls)
  in
  try
    let solution, q =
      match cfg.bound with
      | None ->
        ( Srp.simulate_declarations decls
        , QueueSet.empty Integer.compare )
      | Some b -> Srp.simulate_declarations_bound decls b
    in
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
    | None -> Success (Some solution), Some fs
    | Some m ->
       if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
         CounterExample solution, Some fs
       else
         Success (Some solution), Some fs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

let compress file info decls cfg networkOp =
  let network, symb =
    match
      ( get_merge decls
      , get_trans decls
      , get_init decls
      , get_nodes decls
      , get_edges decls
      , get_attr_type decls
      , get_assert decls
      , get_symbolics decls )
    with
    | Some emerge, Some etrans, Some einit, Some n, Some es,
      Some aty, Some eassert, symb ->
       let graph = AdjGraph.add_edges (AdjGraph.create n) es in
       { attr_type = aty; init = einit; trans = etrans;
         merge = emerge; assertion = eassert; graph = graph }, symb
    | _ ->
       Console.error
         "missing definition of nodes, edges, merge, trans, init or assert"
  in

  let k = cfg.compress in
  (* partially evaluate the functions of the network *)
  let transMap = Abstraction.partialEvalTrans network.graph network.trans in
  let mergeMap = Abstraction.partialEvalMerge network.graph network.merge in
  let initMap = Slicing.partialEvalInit network in
  let assertMap = Slicing.partialEvalAssert network in

  (*printing concrete graph *)
  if cfg.draw then
    begin
      let fname = AdjGraph.DrawableGraph.graph_dot_file k file in
      AdjGraph.DrawableGraph.drawGraph network.graph fname
    end;
  
  (* find the prefixes that are relevant to the assertions *)
  let assertionPrefixes = Slicing.relevantPrefixes assertMap in
  (* find where each prefix is announced from *)
  let slices = Slicing.findInitialSlices initMap in
  (* keep only the relevant slices, i.e. prefixes that are used by the assertion *)
  let relevantSlices =
    PrefixMap.filter (fun pre _ -> PrefixSet.mem pre assertionPrefixes) slices in
  (* each set of prefixes represents an SRP *)
  let relevantSliceGroups = Slicing.groupPrefixesByVertices relevantSlices in

  let fres = ref AbstractionMap.emptyAbstraction in
  let rec loop (finit: AbstractionMap.abstractionMap)
               (f: AbstractionMap.abstractionMap)
               (pre: Prefix.t)
               (ds: AdjGraph.VertexSet.t)
               (k: int)
               (i: int) =
    (* build abstract network *)
    let failVars, decls =
      time_profile "Build abstract network"
                   (fun () -> buildAbstractNetwork f network.graph mergeMap transMap
                                                   initMap assertMap ds
                                                   network.attr_type pre symb k) in
    let decls = Inline.inline_declarations info decls in
    let groups = AbstractionMap.printAbstractGroups f "\n" in
    Console.show_message groups Console.T.Blue "Abstract groups";
    match networkOp cfg info decls with
    | Success _, _ -> Printf.printf "No counterexamples found\n"
    | (CounterExample sol), fs ->
       let sol = apply_all sol (oget fs) in
       let aty = if cfg.unbox then
                   TupleFlatten.flatten_ty (UnboxOptions.unbox_ty network.attr_type)
                 else
                   network.attr_type
       in
       let f' =
         time_profile "Refining abstraction after failures"
                      (fun () ->
                        FailuresAbstraction.refineCounterExample
                          cfg.draw file network.graph finit f failVars sol k ds aty i)
       in
       match f' with
       | None -> print_solution sol;
       | Some f' ->
          fres := f';
          loop finit f' pre ds k (i+1)
  in
  PrefixSetSet.iter
    (fun prefixes ->
      Console.show_message (Slicing.printPrefixes prefixes)
                           Console.T.Green "Checking SRP for prefixes";
      (* get a prefix from this class of prefixes *)
      let pre = PrefixSet.min_elt prefixes in
      (* find the nodes this class is announced from *)
      let ds = PrefixMap.find pre relevantSlices in
      (* compute the bonsai abstraction *)
      let fbonsai = Abstraction.findAbstraction network.graph transMap mergeMap ds in
      fres := fbonsai;
      (* do abstraction for 0...k failures. Reusing previous abstraction *)
      for i=0 to k do
        Console.show_message "" Console.T.Green
                             (Printf.sprintf "Checking for %d failures" i);
        (* find the initial abstraction function for these destinations *)
        let f = 
          time_profile "Computing Abstraction for K failures"
                       (fun () ->
                         FailuresAbstraction.refineK network.graph !fres ds i)
        in
        loop fbonsai f pre ds i 1
      done
    ) relevantSliceGroups

let parse_input (args : string array)
  : Cmdline.t * Console.info * string * Syntax.declarations =
  let cfg, rest = argparse default "nv" args in
  Cmdline.set_cfg cfg ;
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  let decls =
    if cfg.smt || cfg.inline then
        Inline.inline_declarations info decls
    else
      decls
  in
  (cfg, info, file, decls)

  
