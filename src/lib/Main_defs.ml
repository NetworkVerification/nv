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
open Nv_utils
open OCamlUtils
open Nv_kirigami

type answer =
  | Success of Solution.t option
  | CounterExample of Solution.t

let rec apply_all (s : Solution.t) fs =
  match fs with
  | [] -> s
  | f :: fs -> apply_all (f s) fs
;;

let smt_query_file =
  let counter = ref (-1) in
  fun (file : string) ->
    incr counter;
    let count = !counter in
    lazy (open_out (file ^ "-" ^ string_of_int count ^ "-query"))
;;

let run_smt_classic_aux file cfg info decls part fs =
  (* Attribute Slicing requires the net to have an assertion and for its attribute
     to be a tuple type. *)
  let slices =
    (* Disable slicing until we figure out it works in the new model *)
    (* match cfg.slicing, net.assertion, net.attr_type with
       | true, Some _, TTuple _ ->
       AttributeSlicing.slice_network net
       |> List.map (dmap (fun (net, f) -> net, f :: fs))
       | _ -> *)
    [(fun () -> decls, fs)]
  in
  (* NOTE: slicing can introduce units, so if we ever re-introduce it,
   * this code needs to be moved up to use UnboxUnits *)
  let slices = List.map (dmap (fun (decls, fs) -> decls, fs)) slices in
  let get_answer decls fs =
    let solve_fun =
      if cfg.kirigami
      then SmtKirigami.solveKirigami ~check_ranked:cfg.ranked ~part:(part |> oget)
      else if cfg.hiding
      then SmtHiding.solve_hiding ~starting_vars:[] ~full_chan:(smt_query_file file)
      else Smt.solveClassic
    in
    match solve_fun info cfg.query cfg.timeout (smt_query_file file) decls with
    | Unsat -> Success None, []
    | Unknown -> Console.error "SMT returned unknown"
    | Sat solution ->
      (match solution.assertions with
      | [] -> Success (Some solution), fs
      | lst ->
        if List.for_all (fun b -> b) lst
        then Success (Some solution), fs
        else CounterExample solution, fs)
  in
  (* Return the first slice that returns a counterexample, or the result of the
     last slice if all of them succeed *)
  (* List.iter (fun f -> print_endline @@ Printing.declarations_to_string (fst @@ f ())) slices; *)
  let count = ref (-1) in
  let rec solve_slices slices =
    match slices with
    | [] -> failwith "impossible"
    | laz :: tl ->
      let answer =
        incr count;
        Profile.time_profile_absolute
          ("Slice " ^ string_of_int !count)
          (fun () ->
            let net, fs = laz () in
            get_answer net fs)
      in
      (match answer with
      | CounterExample _, _ -> answer
      | Success _, _ -> if BatList.is_empty tl then answer else solve_slices tl)
  in
  (* let results = Parmap.parmap (BatPervasives.uncurry get_answer) @@ Parmap.L slices in
     match List.find_opt (function | CounterExample _, _ -> true | _ -> false) results with
     | Some answer -> answer
     | None -> List.hd results *)
  let solve_parallel ncores slices =
    Parmap.parfold
      ~ncores
      (fun laz acc ->
        let net, fs = laz () in
        match acc with
        | CounterExample _, _ -> acc
        | _ -> get_answer net fs)
      (Parmap.L slices)
      (Success None, [])
      (fun ans1 ans2 ->
        match ans1 with
        | CounterExample _, _ -> ans1
        | _ -> ans2)
  in
  match cfg.parallelize with
  | None -> solve_slices slices
  | Some n -> solve_parallel n slices
;;

let run_smt_partitioned file cfg info decls parts fs =
  let pds =
    Profile.time_profile "Partitioning" (fun () ->
        List.map
          (fun p ->
            let p, d = Partition.transform_declarations decls p in
            if cfg.print_partitions
            then print_endline (SrpRemapping.string_of_partitioned_srp p)
            else ();
            Some p, d)
          parts)
  in
  List.map (fun (p, d) -> run_smt_classic_aux file cfg info d p fs) pds
;;

let run_smt_classic file cfg info decls parts fs =
  let decls, fs =
    let decls, f = UnboxEdges.unbox_declarations decls in
    decls, f :: fs
  in
  let decls, fs =
    SmtUtils.smt_config.unboxing <- true;
    let decls, f1 =
      Profile.time_profile "Unbox options" (fun () ->
          UnboxOptions.unbox_declarations decls)
    in
    let decls, f2 =
      Profile.time_profile "Flattening Tuples" (fun () ->
          TupleFlatten.flatten_declarations decls)
    in
    decls, f2 :: f1 :: fs
  in
  let decls, fs =
    let decls, f = Renaming.alpha_convert_declarations decls in
    (*TODO: why are we renaming here?*)
    let decls, _ = OptimizeBranches.optimize_declarations decls in
    (* The _ should match the identity function *)
    let decls, f' = RenameForSMT.rename_declarations decls in
    (* Maybe we should wrap this into the previous renaming... *)
    let decls, f'' = UnboxUnits.unbox_declarations decls in
    decls, f'' :: f' :: f :: fs
  in
  match parts with
  | Some p -> run_smt_partitioned file cfg info decls p fs
  | None -> [run_smt_classic_aux file cfg info decls None fs]
;;

let run_smt file cfg info decls parts fs =
  if cfg.finite_arith then SmtUtils.smt_config.infinite_arith <- false;
  if cfg.smt_parallel then SmtUtils.smt_config.parallel <- true;
  (* if cfg.func then
       run_smt_func file cfg info decls fs
     else *)
  run_smt_classic file cfg info decls parts fs
;;

let partialEvalDecls decls =
  List.map
    (fun d ->
      match d with
      | DLet (x, ty, e) -> DLet (x, ty, InterpPartial.interp_partial_opt e)
      | DAssert e -> DAssert (InterpPartial.interp_partial_opt e)
      | DSolve r ->
        DSolve
          { r with
            init = InterpPartial.interp_partial_opt r.init
          ; trans = InterpPartial.interp_partial_opt r.trans
          ; merge = InterpPartial.interp_partial_opt r.merge
          ; part = omap (map_part (fun i -> InterpPartial.interp_partial_opt i)) r.part
          }
      | DRequire _ | DPartition _ | DNodes _ | DSymbolic _ | DUserTy _ | DEdges _ -> d)
    decls
;;

let run_simulator cfg _ decls fs =
  (* It is important to partially evaluate before optimizing branches and before simulation. *)
  let decls =
    Profile.time_profile "partial eval took:" (fun () -> partialEvalDecls decls)
  in
  let decls, _ = OptimizeBranches.optimize_declarations decls in
  try
    let solution, q =
      match cfg.bound with
      | None ->
        ( Profile.time_profile "Interpreted simulation" (fun () ->
              Simulator.simulate_declarations ~throw_requires:true decls)
        , QueueSet.empty Pervasives.compare )
      | Some b ->
        ignore b;
        failwith "Don't know what this means"
      (* Srp.simulate_net_bound net b *)
    in
    (match QueueSet.pop q with
    | None -> ()
    | Some _ ->
      print_string [] "non-quiescent nodes:";
      QueueSet.iter (fun q -> print_string [] (string_of_int q ^ ";")) q;
      print_newline ();
      print_newline ());
    match solution.assertions with
    | [] -> Success (Some solution), fs
    | lst ->
      if List.for_all (fun b -> b) lst
      then Success (Some solution), fs
      else CounterExample solution, fs
  with
  | Srp.Require_false -> Console.error "required conditions not satisfied"
;;

(** Native simulator - compiles SRP to OCaml *)
let run_compiled file _ _ decls fs =
  let path = Filename.remove_extension file in
  let name = Filename.basename path in
  let name = String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) name in
  let newpath = name in
  let solution = Loader.simulate newpath decls in
  match solution.assertions with
  | [] -> Success (Some solution), fs
  | lst ->
    if List.for_all (fun b -> b) lst
    then Success (Some solution), fs
    else CounterExample solution, fs
;;

let parse_input_aux cfg info file decls parts fs =
  let decls, fs =
    if cfg.unroll
    then (
      let decls, f =
        (* unrolling maps *)
        Profile.time_profile "Map unrolling" (fun () -> MapUnrolling.unroll info decls)
      in
      (* Inline again after unrolling. Could probably optimize this away during unrolling *)
      let decls =
        Profile.time_profile "Inlining" (fun () -> Inline.inline_declarations decls)
      in
      (* (Typing.infer_declarations info decls, f :: fs) (* TODO: is type inf necessary here?*) *)
      decls, f :: fs)
    else decls, fs
  in
  cfg, info, file, decls, parts, fs
;;

let parse_input (args : string array) =
  let cfg, rest = argparse default "nv" args in
  Cmdline.set_cfg cfg;
  Cmdline.update_cfg_dependencies ();
  let cfg = Cmdline.get_cfg () in
  if cfg.debug then Printexc.record_backtrace true;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  (* Parse nv file *)
  let decls = ds in
  (* print_endline @@ Printing.declarations_to_string decls ; *)
  let decls = ToEdge.toEdge_decl decls :: decls in
  let decls = Typing.infer_declarations info decls in
  Typing.check_annot_decls decls;
  Wellformed.check info decls;
  let partitions, decls =
    if cfg.kirigami
    then (
      let parts = SrpRemapping.partition_declarations decls in
      let new_symbolics =
        let aty = get_attr_type decls |> oget in
        Partition.get_hyp_symbolics aty parts
      in
      Some parts, new_symbolics @ decls)
    else None, decls
  in
  let decls, f = RecordUnrolling.unroll_declarations decls in
  let fs = [f] in
  let decls, fs =
    (* inlining definitions *)
    if cfg.inline
    then (
      (* Note! Must rename before inlining otherwise inlining is unsound *)
      let decls, f = Renaming.alpha_convert_declarations decls in
      let decls, fs =
        ( Profile.time_profile "Inlining" (fun () ->
              Inline.inline_declarations decls
              (* TODO: We could probably propagate type information through inlining *))
        , f :: fs )
      in
      (Typing.infer_declarations info) decls, fs)
    else decls, fs
  in
  parse_input_aux cfg info file decls partitions fs
;;
