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
  let decls =
    if cfg.unbox then
      begin
        smt_config.unboxing <- true;
        time_profile "Unboxing" (
                       fun () -> UnboxOptions.unbox decls |> TupleFlatten.flatten)
      end
    else decls
  in
  let decls, f = Renaming.alpha_convert_declarations decls in
  let fs = f :: fs in
  let res, fs =
    (Smt2.solve info cfg.query (smt_query_file file) decls ~symbolic_vars:[], fs)
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
      let ds = Inline.inline_declarations ds in
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
      let decls = Inline.inline_declarations decls in
      ([f], decls)
    else ([], decls)
  in
  let decls = Typing.infer_declarations info decls in
  let decls =
    if cfg.unroll then
      time_profile "unroll maps" (fun () -> MapUnrolling.unroll info decls)
    else
      decls
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
  (* Printf.printf "Number of concrete edges:%d\n" (List.length (oget (get_edges decls))); *)
  let k = cfg.compress in
  if cfg.smt then
    smt_config.failures <- Some k;
 
  (*printing concrete graph *)
  (* if cfg.draw then *)
  (*   begin *)
  (*     let fname = AdjGraph.DrawableGraph.graph_dot_file k file in *)
  (*     AdjGraph.DrawableGraph.drawGraph network.graph fname *)
  (*   end; *)

  let rec loop (finit: AbstractionMap.abstractionMap)
               (f: AbstractionMap.abstractionMap)
               (slice : Slicing.network)
               (sources: AdjGraph.VertexSet.t)
               (mergeMap: (AdjGraph.Vertex.t, int * Syntax.exp) Hashtbl.t)
               (transMap: (AdjGraph.Edge.t, int * Syntax.exp) Hashtbl.t)
               (k: int)
               (i: int) =
    (* build abstract network *)
    let failVars, decls =
      time_profile "Build abstract network"
        (fun () -> buildAbstractNetwork f mergeMap transMap slice k) in
    let absTrans = oget (get_trans decls) in
    Printf.printf "%s" (Printing.exp_to_string absTrans);
    smt_config.multiplicities <- getEdgeMultiplicities slice.graph f failVars;
    let groups = AbstractionMap.printAbstractGroups f "\n" in
    Console.show_message groups Console.T.Blue "Abstract groups";
    match networkOp cfg info decls with
    | Success _, _ ->
       Printf.printf "Number of abstract edges:%d\n"
                     (BatList.length (oget (get_edges decls)));
       Printf.printf "No counterexamples found\n"
    | (CounterExample sol), fs ->
       let sol = apply_all sol (oget fs) in
       let aty = if cfg.unbox then
                   TupleFlatten.flatten_ty (UnboxOptions.unbox_ty slice.attr_type)
                 else
                   slice.attr_type
       in
       let f' =
         time_profile "Refining abstraction after failures"
                      (fun () ->
                        FailuresAbstraction.refineCounterExample
                          cfg.draw file slice.graph finit f failVars sol
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
      let n = AdjGraph.num_vertices slice.graph in
      let sources =
        Slicing.findRelevantNodes (partialEvalOverNodes n slice.assertion) in
      (* partially evaluate the functions of the network *)
      let transMap = Abstraction.partialEvalTrans slice.graph slice.trans in
      let mergeMap = Abstraction.partialEvalMerge slice.graph slice.merge in
      (* compute the bonsai abstraction *)
      let fbonsai =
        Abstraction.findAbstraction slice.graph transMap mergeMap slice.destinations
      in
      (* find the initial abstraction function for these destinations *)
      try let f = 
            time_profile "Computing Refinement for K failures"
                         (fun () ->
                           FailuresAbstraction.refineK slice.graph fbonsai sources
                             slice.destinations k)
          in
          loop fbonsai f slice sources mergeMap transMap k 1
      with
      | Cutoff -> ()
    ) (Slicing.createSlices info decls)

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
    if cfg.inline || cfg.smt then
      time_profile "Inlining" (
                     fun () -> Inline.inline_declarations decls |>
                                 Typing.infer_declarations info)
    else
      decls
    in
  let decls = if cfg.unroll then
                time_profile "unroll maps" (fun () -> MapUnrolling.unroll info decls) |>
                  Typing.infer_declarations info 
              else decls
  in
  (cfg, info, file, decls)




      (* Visitors.iter_exp_decls (fun d e -> *)
    (*                  match e.ety with *)
    (*   | Some ty -> *)
    (*      (\* Printf.printf "typ:%s\n" (Printing.ty_to_string ty); *\) *)
    (*      (match hasTvar (get_inner_type ty) with *)
    (*      | true -> failwith ("has tvar" ^ (declaration_to_string d)) *)
    (*      | _ -> ()) *)
    (*   | None -> *)
    (*      (match e.e with *)
    (*      | EVal v -> *)
    (*         (match v.vty with *)
    (*          | Some ty -> *)
    (*             (match hasTvar (get_inner_type ty) with *)
    (*              | true -> failwith ("has tvar" ^ ( declaration_to_string d)) *)
    (*              | _ -> ()) *)
    (*          | None -> ()) *)
    (*      | _ -> ())) decls; *)
    (* failwith "end"; *)
