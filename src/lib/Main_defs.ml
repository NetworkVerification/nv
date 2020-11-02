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

let run_smt_classic file cfg info decls fs =
  let decls, fs =
    let decls, f = UnboxEdges.unbox_declarations decls in
    decls, f :: fs
  in
  let decls, fs =
    SmtUtils.smt_config.unboxing <- true;
    let decls, f1 = Profile.time_profile "Unbox options" (fun () -> UnboxOptions.unbox_declarations decls) in
    let decls, f2 =
      Profile.time_profile "Flattening Tuples" (fun () -> TupleFlatten.flatten_declarations decls)
    in
    decls, (f2 :: f1 :: fs)
  in

  let decls, fs =
    let decls, f = Renaming.alpha_convert_declarations decls in (*TODO: why are we renaming here?*)
    let decls, _ = OptimizeBranches.optimize_declarations decls in (* The _ should match the identity function *)
    let decls, f' = RenameForSMT.rename_declarations decls in (* Maybe we should wrap this into the previous renaming... *)
    decls, f' :: f :: fs
  in

  let get_answer decls fs =
    let solve_fun =
      if cfg.kirigami then
        Smt.solveKirigami
      else
      if cfg.hiding then
        (SmtHiding.solve_hiding ~starting_vars:[] ~full_chan:(smt_query_file file))
      else
        Smt.solveClassic
    in
    match solve_fun info cfg.query (smt_query_file file) decls with
    | Unsat ->
      (Success None, [])
    | Unknown -> Console.error "SMT returned unknown"
    | Sat solution ->
      match solution.assertions with
      | [] -> Success (Some solution), fs
      | lst ->
        if List.for_all (fun b -> b) lst then
          Success (Some solution), fs
        else
          CounterExample solution, fs
  in

  (* Attribute Slicing requires the net to have an assertion and for its attribute
     to be a tuple type. *)
  let slices =
    (* Disable slicing until we figure out it works in the new model *)
    (* match cfg.slicing, net.assertion, net.attr_type with
       | true, Some _, TTuple _ ->
       AttributeSlicing.slice_network net
       |> List.map (dmap (fun (net, f) -> net, f :: fs))
       | _ -> *)
    [fun () -> (decls, fs)]
  in
  let slices =
    List.map
      (dmap (fun (decls, fs) ->
           let decls, f = UnboxUnits.unbox_declarations decls in
           decls, f :: fs))
      slices
  in

  (* Return the first slice that returns a counterexample, or the result of the
     last slice if all of them succeed *)
  (* List.iter (fun f -> print_endline @@ Printing.declarations_to_string (fst @@ f ())) slices; *)
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
  (* if cfg.func then
     run_smt_func file cfg info decls fs
     else *)
  run_smt_classic file cfg info decls fs

let run_simulator cfg _ decls fs =
  (* let net = mk_net cfg decls in
     let net = partialEvalNet net in
     let net, _ = OptimizeBranches.optimize_net net in (* The _ should match the identity function *) *)
  let decls, _ = OptimizeBranches.optimize_declarations decls in
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
    | [] -> Success (Some solution), fs
    | lst ->
      if List.for_all (fun b -> b) lst then
        Success (Some solution), fs
      else
        CounterExample solution, fs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied"

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
    if List.for_all (fun b -> b) lst then
      Success (Some solution), fs
    else
      CounterExample solution, fs

let parse_input_aux cfg info file decls fs =
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

let parse_input (args : string array) :
  (Cmdline.t * Console.info * string * Syntax.declarations * Solution.map_back list) list
  =
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
  if not cfg.no_wellformed then Wellformed.check info decls ;
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
  if cfg.kirigami then
    (* FIXME: this breaks ToEdge *)
    (* NOTE: we partition after checking well-formedness so we can reuse edges that don't exist *)
    (* TODO: keep the declarations separate, run them through the transformations,
     * and then sort them out once we get to SMT encoding *)
    let new_decls_base = List.map (fun (d1, d2) -> ("Initial check:", d1 @ d2))
        (Nv_kirigami.Partition.divide_decls cfg decls ~base_check:true) in
    (* perform the base checks before the regular checks *)
    let new_decls = List.map (fun (d1, d2) -> ("Safety check:", d1 @ d2))
        (Nv_kirigami.Partition.divide_decls cfg decls ~base_check:false) in
    List.map (fun (_s, d) ->
        (* print_endline @@ s; *)
        print_endline @@ Printing.declarations_to_string d;
        parse_input_aux cfg info file d fs)
      (* just the I-checks *)
      (* new_decls *)
      (* I-checks plus base checks *)
      (new_decls_base @ new_decls)
  else
    [parse_input_aux cfg info file decls fs]
