open ANSITerminal
open Cmdline
open Inline
open Interp
open Hashcons
open Printing
open Quickcheck
open Renaming
open Smt
open SmtUtils
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

let rec apply_all (s : Solution.t) fs =
  match fs with
  | [] -> s
  | f :: fs -> apply_all (f s) fs

let smt_query_file =
  let counter = ref (-1) in
  fun (file: string) ->
    incr counter;
    lazy (open_out (file ^ "-" ^
                    (string_of_int !counter) ^ "-query"))

let partialEvalNet net =
  {net with
   init = Interp.interp_partial_opt net.init;
   trans = Interp.interp_partial_opt net.trans;
   merge = Interp.interp_partial_opt net.merge
  }

let run_smt file cfg info (net : Syntax.network) fs =
  if cfg.func then
    smt_config.encoding <- Functional;
  let net, fs =
    if cfg.unbox then
      begin
        smt_config.unboxing <- true;
        let net, f1 = time_profile "Unbox options" (fun () -> UnboxOptions.unbox_net net) in
        let net, f2 =
          time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_net net)
        in
        (*have two different partial evaluation techniques *)
        (* Printf.printf "emerge %s\n" (Printing.exp_to_string net.merge); *)
        (* let net = partialEvalNet net in *)
        (* Printf.printf "emerge %s\n" (Printing.exp_to_string net.merge); *)
        (* let net = time_profile "optimizing branches" (fun () -> OptimizeBranches.optimizeNet net) in *)
        net, (f2 :: f1 :: fs)
      end
    else net, fs
  in
  let net, f = Renaming.alpha_convert_net net in
  let fs = f :: fs in
  let res = Smt.solve info cfg.query (smt_query_file file) net ~symbolic_vars:[] in
  match res with
  | Unsat ->
     (Success None, None)
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
    match solution.assertions with
    | None -> Success (Some solution), Some fs
    | Some m ->
      if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
        CounterExample solution, Some fs
      else
        Success (Some solution), Some fs

let run_test cfg info net fs =
  let (sol, stats), fs =
    if cfg.smart_gen then
      let net, f = Renaming.alpha_convert_net net in
      let fs = f :: fs in
      (Quickcheck.check_smart info net ~iterations:cfg.ntests, fs)
    else (Quickcheck.check_random net ~iterations:cfg.ntests, fs)
  in
  print_newline () ;
  print_string [Bold] "Test cases: " ;
  Printf.printf "%d\n" stats.iterations ;
  print_string [Bold] "Rejected: " ;
  Printf.printf "%d\n" stats.num_rejected ;
  match sol with
  | None -> (Success None, None)
  | Some sol -> (CounterExample sol, Some fs)

let run_simulator cfg _ net fs =
  try
    let solution, q =
      match cfg.bound with
      | None ->
        ( Srp.simulate_net net
        , QueueSet.empty Integer.compare )
      | Some b -> Srp.simulate_net_bound net b
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

let compress file info net cfg fs networkOp =
  (* Printf.printf "Number of concrete edges:%d\n" (List.length (oget (get_edges decls))); *)
  let k = cfg.compress in
  if cfg.smt then
    smt_config.failures <- Some k;

  FailuresAbstraction.refinement_breadth := cfg.depth;
  FailuresAbstraction.counterexample_refinement_breadth := cfg.depth;
  let net = OptimizeBranches.optimizeNet net in

  let rec loop (finit: AbstractionMap.abstractionMap)
      (f: AbstractionMap.abstractionMap)
      (slice : Slicing.network_slice)
      (sources: AdjGraph.VertexSet.t)
      (mergeMap: (AdjGraph.Vertex.t, int * Syntax.exp) Hashtbl.t)
      (transMap: (AdjGraph.Edge.t, int * Syntax.exp) Hashtbl.t)
      (k: int)
      (i: int) =
    (* build abstract network *)
    let failVars, absNet =
      time_profile "Build abstract network"
        (fun () -> buildAbstractNetwork f mergeMap transMap slice k) in
    smt_config.multiplicities <- getEdgeMultiplicities slice.net.graph f failVars;
    (* let groups = AbstractionMap.printAbstractGroups f "\n" in *)
    let aedges = BatList.length (AdjGraph.edges absNet.graph) in
    let groups = Printf.sprintf "%d/%d" (AbstractionMap.normalized_size f) aedges in
    Console.show_message groups Console.T.Blue "Number of abstract nodes/edges";
    match networkOp cfg info absNet fs with
    | Success _, _ ->
      Printf.printf "No counterexamples found\n"
    | (CounterExample sol), fs ->
      let sol = apply_all sol (oget fs) in
      let aty = (* if cfg.unbox then
                 *   TupleFlatten.flatten_ty (UnboxOptions.unbox_ty slice.net.attr_type)
                 * else *)
        slice.net.attr_type
      in
      Console.show_message (Printf.sprintf "%d" i) Console.T.Green "Refinement Iteration";
      let f' =
        time_profile "Refining abstraction after failures"
          (fun () ->
             FailuresAbstraction.refineCounterExample
               file slice.net.graph finit f failVars sol
               k sources slice.destinations aty i)
      in
      match f' with
      | None -> print_solution sol;
      | Some f' ->
        loop finit f' slice sources mergeMap transMap k (i+1)
  in
  (* Iterate over each network slice *)
  BatList.iter
    (fun slice ->
       Console.show_message (Slicing.printPrefixes slice.prefixes)
         Console.T.Green "Checking SRP for prefixes";
       (* find source nodes *)
       let n = AdjGraph.num_vertices slice.net.graph in
       let sources =
         Slicing.findRelevantNodes (partialEvalOverNodes n (oget slice.net.assertion)) in
       (* partially evaluate the functions of the network. *)
       (* TODO, this should be done outside of this loop, maybe just redone here *)
       (* Printf.printf "Just before opt\n"; *)
       (* let optTrans = OptimizeBranches.optimizeExp slice.net.trans in *)
       (* Printf.printf "trans:%s\n" (Printing.exp_to_string slice.net.trans); *)
       (* Printf.printf "trans\n"; *)
       (* (Visitors.iter_exp (fun e -> *)
       (*      match e.e with *)
       (*      | EMatch (e, bs) -> *)
       (*         branchSize bs *)
       (*      | _ -> ()) optTrans); *)
       (* flush stdout; *)
       (* failwith "stop"; *)
       let transMap =
         Profile.time_profile "partial eval trans"
           (fun () ->
              Abstraction.partialEvalTrans
                slice.net.graph slice.net.trans)
       in
       let mergeMap = Abstraction.partialEvalMerge slice.net.graph slice.net.merge in
       (* compute the bonsai abstraction *)

       let fbonsai, f =
         time_profile "Computing Abstraction"
           (fun () ->
              let fbonsai =
                Abstraction.findAbstraction slice.net.graph transMap
                  mergeMap slice.destinations
              in
              (* find the initial abstraction function for these destinations *)
              let f =
                FailuresAbstraction.refineK slice.net.graph fbonsai sources
                  slice.destinations k
              in
              fbonsai, f)
       in
       loop fbonsai f slice sources mergeMap transMap k 1
    ) (Slicing.createSlices info net)

let checkPolicy info cfg file ds =
  let ds, _ = Renaming.alpha_convert_declarations ds in
  let net = Slicing.createNetwork ds in
  SmtCheckProps.checkMonotonicity info cfg.query (smt_query_file file) net

let parse_input (args : string array)
  : Cmdline.t * Console.info * string * Syntax.network * ((Solution.t -> Solution.t) list) =
  let cfg, rest = argparse default "nv" args in
  Cmdline.set_cfg cfg ;
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in (* Parse nv file *)
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  let decls, f = RecordUnrolling.unroll decls in (* Unroll records done first *)
  let fs = [f] in
  let decls,fs = (* inlining definitions *)
    if cfg.inline || cfg.unroll || cfg.smt || cfg.check_monotonicity || cfg.smart_gen then
      (* Note! Must rename before inling otherwise inling is unsound *)
      let decls, f = Renaming.alpha_convert_declarations decls in
      (time_profile "Inlining" (
           fun () ->
           Inline.inline_declarations decls |>
             Typing.infer_declarations info), f :: fs)
    else
      (decls,fs)
  in
  let decls, fs =
    if cfg.unroll || cfg.smt then
      let decls, f = (* unrolling maps *)
        time_profile "Map unrolling" (fun () -> MapUnrolling.unroll info decls)
      in
      (Typing.infer_declarations info decls, f :: fs)
    else decls, fs
  in
  let decls = (*Inline again after unrolling, is this necessary? *)
    if cfg.unroll || cfg.smt then
      time_profile "Inlining" (
          fun () -> Inline.inline_declarations decls |>
                      Typing.infer_declarations info)
    else
      decls
  in
  let net = Slicing.createNetwork decls in (* Create something of type network *)
  let net =
    if cfg.link_failures > 0 then
      Failures.buildFailuresNet net cfg.link_failures
    else net
  in
  (cfg, info, file, net, fs)
