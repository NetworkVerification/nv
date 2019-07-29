open Nv_datastructures
open ANSITerminal
open Nv_lang
open Nv_lang.Cmdline
open Nv_smt
open Nv_solution
open Nv_slicing
open Nv_lang.Syntax
open Nv_interpreter
open Nv_transformations
open Abstraction
open BuildAbstractNetwork
open Nv_utils
open OCamlUtils

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
    let count = !counter in
    lazy (open_out (file ^ "-" ^
                    (string_of_int count) ^ "-query"))

let partialEvalNet net =
  {net with
   init = InterpPartial.interp_partial_opt net.init;
   trans = InterpPartial.interp_partial_opt net.trans;
   merge = InterpPartial.interp_partial_opt net.merge
  }

let run_smt_func file cfg info net fs =
  SmtUtils.smt_config.encoding <- Functional;
  let srp = SmtSrp.network_to_srp net in
  let srp, f = Renaming.alpha_convert_srp srp in
  let srp, fs =
    if cfg.unbox then
      begin
        SmtUtils.smt_config.unboxing <- true;
        let srp, f1 = Profile.time_profile "Unbox options" (fun () -> UnboxOptions.unbox_srp srp) in
        let srp, f2 =
          Profile.time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_srp srp)
        in
        srp, (f2 :: f1 :: f :: fs)
      end
    else
      srp, f :: fs
  in
  let res = Smt.solveFunc info cfg.query (smt_query_file file) srp in
  match res with
  | Unsat ->
    (Success None, [])
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
    match solution.assertions with
    | None -> Success (Some solution), fs
    | Some m ->
      if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
        CounterExample solution, fs
      else
        Success (Some solution), fs

let run_smt_classic file cfg info (net : Syntax.network) fs =
  let net, fs =
    if cfg.unbox || cfg.hiding then
      begin
        SmtUtils.smt_config.unboxing <- true;
        let net, f1 = Profile.time_profile "Unbox options" (fun () -> UnboxOptions.unbox_net net) in
        let net, f2 =
          Profile.time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_net net)
        in
        net, (f2 :: f1 :: fs)
      end
    else net, fs
  in

  let net, f = Renaming.alpha_convert_net net in (*TODO: why are we renaming here?*)
  let fs = f :: fs in
  let solve_fun =
    if cfg.hiding then
      (SmtHiding.solve_hiding ~starting_vars:[] ~full_chan:(smt_query_file file))
    else
      Smt.solveClassic
  in
  let res =
    solve_fun info cfg.query (smt_query_file file) net
  in
  match res with
  | Unsat ->
    (Success None, [])
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
    match solution.assertions with
    | None -> Success (Some solution), fs
    | Some m ->
      if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
        CounterExample solution, fs
      else
        Success (Some solution), fs

let run_smt file cfg info (net : Syntax.network) fs =
  if cfg.func then
    run_smt_func file cfg info net fs
  else
    run_smt_classic file cfg info net fs

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
  | None -> (Success None, [])
  | Some sol -> (CounterExample sol, fs)

let run_simulator cfg _ net fs =
  try
    let solution, q =
      match cfg.bound with
      | None ->
        ( Srp.simulate_net net
        , QueueSet.empty Pervasives.compare )
      | Some b -> Srp.simulate_net_bound net b
    in
    ( match QueueSet.pop q with
      | None -> ()
      | Some _ ->
        print_string [] "non-quiescent nodes:" ;
        QueueSet.iter
          (fun q ->
             print_string [] (string_of_int q ^ ";") )
          q ;
        print_newline () ;
        print_newline () ;
    );
    match solution.assertions with
    | None -> Success (Some solution), fs
    | Some m ->
      if AdjGraph.VertexMap.exists (fun _ b -> not b) m then
        CounterExample solution, fs
      else
        Success (Some solution), fs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

let compress file info net cfg fs networkOp =
  (* Printf.printf "Number of concrete edges:%d\n" (List.length (oget (get_edges decls))); *)
  let k = cfg.compress in
  if cfg.smt then
    SmtUtils.smt_config.failures <- Some k;

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
      Profile.time_profile "Build abstract network"
        (fun () -> buildAbstractNetwork f mergeMap transMap slice k) in
    SmtUtils.smt_config.multiplicities <- getEdgeMultiplicities slice.net.graph f failVars;
    (* let groups = AbstractionMap.printAbstractGroups f "\n" in *)
    let aedges = BatList.length (AdjGraph.edges absNet.graph) in
    let groups = Printf.sprintf "%d/%d" (AbstractionMap.normalized_size f) aedges in
    Console.show_message groups Console.T.Blue "Number of abstract nodes/edges";
    match networkOp cfg info absNet fs with
    | Success _, _ ->
      Printf.printf "No counterexamples found\n"
    | (CounterExample sol), fs ->
      let sol = apply_all sol fs in
      let aty = (* if cfg.unbox then
                 *   TupleFlatten.flatten_ty (UnboxOptions.unbox_ty slice.net.attr_type)
                 * else *)
        slice.net.attr_type
      in
      Console.show_message (Printf.sprintf "%d" i) Console.T.Green "Refinement Iteration";
      let f' =
        Profile.time_profile "Refining abstraction after failures"
          (fun () ->
             FailuresAbstraction.refineCounterExample
               file slice.net.graph finit f failVars sol
               k sources slice.destinations aty i)
      in
      match f' with
      | None -> Solution.print_solution sol;
      | Some f' ->
        loop finit f' slice sources mergeMap transMap k (i+1)
  in
  (* Iterate over each network slice *)
  BatList.iter
    (fun slice ->
       Console.show_message (Slicing.printPrefixes slice.Slicing.prefixes)
         Console.T.Green "Checking SRP for prefixes";
       (* find source nodes *)
       let n = AdjGraph.num_vertices slice.net.graph in
       let sources =
         Slicing.findRelevantNodes (Slicing.partialEvalOverNodes n (oget slice.net.assertion)) in
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
         Profile.time_profile "Computing Abstraction"
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
  let decls = ds in
  (* print_endline @@ Printing.declarations_to_string decls ; *)
  let decls = ToEdge.toEdge_decl decls :: decls in
  let decls = Typing.infer_declarations info decls in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  let decls, f = RecordUnrolling.unroll decls in (* Unroll records done first *)
  let fs = [f] in
  let decls,fs = (* inlining definitions *)
    if cfg.inline || cfg.unroll || cfg.smt || cfg.check_monotonicity || cfg.smart_gen then
      (* Note! Must rename before inling otherwise inling is unsound *)
      let decls, f = Renaming.alpha_convert_declarations decls in
      (Profile.time_profile "Inlining" (
           fun () ->
           Inline.inline_declarations decls |>
             Typing.infer_declarations info), f :: fs)
    else
      (decls,fs)
  in
  let decls, fs =
    if cfg.unroll || cfg.smt then
      let decls, f = (* unrolling maps *)
        Profile.time_profile "Map unrolling" (fun () -> MapUnrolling.unroll info decls)
      in
      (* Inline again after unrolling. Could probably optimize this away during unrolling *)
      let decls = Profile.time_profile "Inlining" (fun () -> Inline.inline_declarations decls) in
      (* (Typing.infer_declarations info decls, f :: fs) (* TODO: is type inf necessary here?*) *)
      (decls, f :: fs)
    else decls, fs
  in
  let net = Slicing.createNetwork decls in (* Create something of type network *)
  let net =
    if cfg.link_failures > 0 then
      Failures.buildFailuresNet net cfg.link_failures
    else net
  in
  (cfg, info, file, net, fs)
