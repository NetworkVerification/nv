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
  | Timeout of int

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

(** Run the SMT solver appropriate for this instance. *)
let solve_smt file cfg info decls part fs =
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
  | Timeout -> Timeout cfg.timeout, []
  | Sat solution ->
    (match solution.assertions with
    | [] -> Success (Some solution), fs
    | lst ->
      if List.for_all (fun b -> b) lst
      then Success (Some solution), fs
      else CounterExample solution, fs)
;;

let run_smt_partitioned file cfg info decls parts fs =
  let open Batteries in
  (* construct a separate partition and decls to solve for each fragment *)
  let partition frag =
    let frag, d = Partition.transform_declarations decls frag in
    if cfg.print_partitions
    then print_endline (SrpRemapping.string_of_fragment frag)
    else ();
    Some frag, d
  in
  let partition_parallel ncores parts =
    Parmap.parmap ~ncores (fun laz -> partition (laz ())) (Parmap.L parts)
  in
  let pds =
    Profile.time_profile "Partitioning" (fun () ->
        let solves = get_solves decls in
        let interfaces =
          List.filter_map (fun s -> Option.map (fun p -> p.interface) s.part) solves
        in
        let parts = List.fold_left Partition.add_interface_predicates parts interfaces in
        match cfg.parallelize with
        | Some n -> partition_parallel n (List.map (fun p () -> p) parts)
        | None -> List.map partition parts)
  in
  (* run fragments in parallel *)
  let solve_parallel ncores fragments =
    Parmap.parmap
      ~ncores
      (fun laz ->
        let part, decls, fs = laz () in
        solve_smt file cfg info decls part fs)
      (Parmap.L fragments)
  in
  match cfg.parallelize with
  | None -> List.map (fun (p, d) -> solve_smt file cfg info d p fs) pds
  | Some n -> solve_parallel n (List.map (fun (p, d) () -> p, d, fs) pds)
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
  | None -> [solve_smt file cfg info decls None fs]
;;

let run_smt file cfg info decls parts fs =
  if cfg.finite_arith then SmtUtils.smt_config.infinite_arith <- false;
  if cfg.smt_parallel then SmtUtils.smt_config.parallel <- true;
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
        , QueueSet.empty Stdlib.compare )
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
  let decls, info = Input.parse file in
  let decls = ToEdge.toEdge_decl decls :: decls in
  let decls = Typing.infer_declarations info decls in
  Typing.check_annot_decls decls;
  Wellformed.check info decls;
  let partitions, decls =
    if cfg.kirigami
    then (
      let which = Option.map OCamlUtils.range_str_to_set cfg.fragments in
      let parts = SrpRemapping.partition_declarations decls ~which in
      let new_symbolics =
        let aty = get_attr_type decls |> oget in
        List.fold_left
          (fun l p -> List.append (Partition.get_hyp_symbolics aty p) l)
          []
          parts
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
