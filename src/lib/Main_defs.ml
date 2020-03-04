open ANSITerminal
open Nv_datastructures
open Nv_lang
open Nv_lang.Cmdline
open Nv_smt
open Nv_solution
open Nv_lang.Syntax
open Nv_interpreter
open Nv_transformations
open Nv_compile
open Nv_compression.Abstraction
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

let partialEvalNet (net : network) =
  {net with
   init = InterpPartial.interp_partial_opt net.init;
   trans = InterpPartial.interp_partial_opt net.trans;
   merge = InterpPartial.interp_partial_opt net.merge;
   assertion = omap (InterpPartial.interp_partial_opt) net.assertion
  }

let mk_net cfg decls =
  let net = createNetwork decls in (* Create something of type network *)
  let net =
    if cfg.link_failures > 0 then
      Failures.buildFailuresNet net cfg.link_failures
    else net
  in
  net
;;

let run_smt_func file cfg info decls fs =
  SmtUtils.smt_config.encoding <- Functional;
  let net = mk_net cfg decls in
  let net, fs =
    let net, f = UnboxEdges.unbox_net net in
    net, f :: fs
  in
  let srp = SmtSrp.network_to_srp net in
  let srp, fs =
    let srp, f = UnboxUnits.unbox_srp srp in
    srp, f :: fs
  in
  let srp, fs =
    SmtUtils.smt_config.unboxing <- true;
    let srp, f1 = Profile.time_profile "Unbox options" (fun () -> UnboxOptions.unbox_srp srp) in
    let srp, f2 =
      Profile.time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_srp srp)
    in
    srp, (f2 :: f1 :: fs)
  in
  let srp, f = Renaming.alpha_convert_srp srp in
  let fs = f :: fs in
  let res = Smt.solveFunc info cfg.query (smt_query_file file) srp in
  match res with
  | Unsat ->
    (Success None, [])
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution ->
    match solution.assertions with
    | None -> Success (Some solution), fs
    | Some m ->
      if not m then
        CounterExample solution, fs
      else
        Success (Some solution), fs

let run_smt_classic file cfg info decls fs =
  let net = mk_net cfg decls in
  let net, fs =
    let net, f = UnboxEdges.unbox_net net in
    net, f :: fs
  in
  let net, fs =
    SmtUtils.smt_config.unboxing <- true;
    let net, f1 = Profile.time_profile "Unbox options" (fun () -> UnboxOptions.unbox_net net) in
    let net, f2 =
      Profile.time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_net net)
    in
    net, (f2 :: f1 :: fs)
  in
  (* let net = {net with trans = InterpPartial.interp_partial net.trans} in*)
  (* Printf.printf "%s\n" (Printing.network_to_string net); *)
  let net, f = Renaming.alpha_convert_net net in (*TODO: why are we renaming here?*)
  let fs = f :: fs in
  let net, _ = OptimizeBranches.optimize_net net in (* The _ should match the identity function *)
  let net = Profile.time_profile "Partially Evaluating Network" (fun () -> partialEvalNet net) in
  (* print_endline @@ Printing.network_to_string net; *)
  let get_answer net fs =
    let solve_fun =
      if cfg.hiding then
        (SmtHiding.solve_hiding ~starting_vars:[] ~full_chan:(smt_query_file file))
      else
        Smt.solveClassic
    in
    match solve_fun info cfg.query (smt_query_file file) net with
    | Unsat ->
      (Success None, [])
    | Unknown -> Console.error "SMT returned unknown"
    | Sat solution ->
      match solution.assertions with
      | None -> Success (Some solution), fs
      | Some m ->
        (* if AdjGraph.VertexMap.exists (fun _ b -> not b) m then *)
        if not m then
          CounterExample solution, fs
        else
          Success (Some solution), fs
  in

  (* Attribute Slicing requires the net to have an assertion and for its attribute
     to be a tuple type. *)
  let slices =
    match cfg.slicing, net.assertion, net.attr_type with
    | true, Some _, TTuple _ ->
      AttributeSlicing.slice_network net
      |> List.map (dmap (fun (net, f) -> net, f :: fs))
    | _ ->
      [fun () -> (net, fs)]
  in
  let slices =
    List.map
      (dmap (fun (net, fs) ->
           let net, f = UnboxUnits.unbox_net net in
           net, f :: fs))
      slices
  in

  (* Return the first slice that returns a counterexample, or the result of the
     last slice if all of them succeed *)
  (* List.iter (fun f -> print_endline @@ Printing.network_to_string (fst @@ f ())) slices; *)
  let count = ref (-1) in
  let rec solve_slices slices =
    match slices with
    | [] -> failwith "impossible"
    | laz::tl ->
      let answer =
        incr count;
        Profile.time_profile_absolute ("Slice " ^ string_of_int !count)
          (fun () ->
             let net, fs = laz () in
             get_answer net fs)
      in
      match answer with
      | CounterExample _, _ -> answer
      | Success _, _ ->
        if BatList.is_empty tl then answer else solve_slices tl
  in
  (* let results = Parmap.parmap (BatPervasives.uncurry get_answer) @@ Parmap.L slices in
     match List.find_opt (function | CounterExample _, _ -> true | _ -> false) results with
     | Some answer -> answer
     | None -> List.hd results *)
  let solve_parallel ncores slices =
    Parmap.parfold ~ncores:ncores
      (fun laz acc ->
         let net, fs = laz () in
         match acc with
         | CounterExample _, _ -> acc
         | _ -> get_answer net fs)
      (Parmap.L slices) (Success None, [])
      (fun ans1 ans2 ->
         match ans1 with
         | CounterExample _, _ -> ans1
         | _ -> ans2)
  in
  match cfg.parallelize with
  | None -> solve_slices slices
  | Some n -> solve_parallel n slices
;;

let run_smt file cfg info decls fs =
  (if cfg.finite_arith then
     SmtUtils.smt_config.infinite_arith <- false);
  (if cfg.smt_parallel then
     SmtUtils.smt_config.parallel <- true);
  if cfg.func then
    run_smt_func file cfg info decls fs
  else
    run_smt_classic file cfg info decls fs

let run_test cfg info decls fs =
  let net = mk_net cfg decls in
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

let run_simulator cfg _ decls fs =
  (* let net = mk_net cfg decls in
  let net = partialEvalNet net in
  let net, _ = OptimizeBranches.optimize_net net in (* The _ should match the identity function *) *)
  try
    let solution, q =
      match cfg.bound with
      | None ->
        (Profile.time_profile "Interpreted simulation"
           (fun () -> Simulator.simulate_declarations ~throw_requires:true decls)
        , QueueSet.empty Pervasives.compare )
      | Some b -> ignore b; failwith "Don't know what this means" (* Srp.simulate_net_bound net b *)
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
      if not m then
        CounterExample solution, fs
      else
        Success (Some solution), fs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

(** Native simulator - compiles SRP to OCaml *)
let run_compiled file cfg _ decls fs =
  let net = mk_net cfg decls in
  let path = Filename.remove_extension file in
  let name = Filename.basename path in
  let name = String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) name in
  let newpath = name in
  let solution = Loader.simulate newpath net in
  match solution.assertions with
  | None -> Success (Some solution), fs
  | Some m ->
    if m then
      CounterExample solution, fs
    else
      Success (Some solution), fs

let compress file info net cfg fs networkOp =
  (* Printf.printf "Number of concrete edges:%d\n" (List.length (oget (get_edges decls))); *)
  let open Nv_compression in
  let k = cfg.compress in
  if cfg.smt then
    SmtUtils.smt_config.failures <- Some k;

  FailuresAbstraction.refinement_breadth := cfg.depth;
  FailuresAbstraction.counterexample_refinement_breadth := cfg.depth;

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
       let n = AdjGraph.nb_vertex slice.net.graph in
       let sources =
         Slicing.findRelevantNodes (Slicing.partialEvalOverNodes n (oget slice.net.assertion)) in
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
  let net = createNetwork ds in
  SmtCheckProps.checkMonotonicity info cfg.query (smt_query_file file) net

let parse_input (args : string array) =
  let cfg, rest = argparse default "nv" args in
  Cmdline.set_cfg cfg ;
  Cmdline.update_cfg_dependencies ();
  let cfg = Cmdline.get_cfg () in
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in (* Parse nv file *)
  let decls = ds in
  (* print_endline @@ Printing.declarations_to_string decls ; *)
  let decls = (ToEdge.toEdge_decl decls) :: decls in
  let decls = Typing.infer_declarations info decls in
  Typing.check_annot_decls decls ;
  Wellformed.check info decls ;
  let decls, f = RecordUnrolling.unroll_declarations decls in
  let fs = [f] in
  let decls,fs = (* inlining definitions *)
    if cfg.inline then
      (* Note! Must rename before inling otherwise inling is unsound *)
      let decls, f = Renaming.alpha_convert_declarations decls in
      (Profile.time_profile "Inlining" (
          fun () ->
            Inline.inline_declarations decls |>
            (* TODO: We could probably propagate type information through inlining *)
            Typing.infer_declarations info), f :: fs)
    else
      (decls,fs)
  in
  let decls, fs =
    if cfg.unroll then
      let decls, f = (* unrolling maps *)
        Profile.time_profile "Map unrolling" (fun () -> MapUnrolling.unroll info decls)
      in
      (* Inline again after unrolling. Could probably optimize this away during unrolling *)
      let decls = Profile.time_profile "Inlining" (fun () -> Inline.inline_declarations decls) in
      (* (Typing.infer_declarations info decls, f :: fs) (* TODO: is type inf necessary here?*) *)
      (decls, f :: fs)
    else decls, fs
  in
  (cfg, info, file, decls, fs)
