open SrpNative
open Findlib
open Fl_dynload
open Nv_utils
open Symbolics
open CompileBDDs
open Nv_datastructures
open Nv_lang.Syntax
open Nv_lang
open OCamlUtils

let load_srp name =
  let () = Findlib.init () in
  try Fl_dynload.load_packages [name] with
  | Dynlink.Error err -> Printf.printf "%s\n" (Dynlink.error_message err)
;;

let simulate name decls =
  ignore (Compile.compile_ocaml name decls);
  (* TODO: make this optional *)
  load_srp (name ^ ".plugin");
  (* Build symbolics module *)
  let symbs = get_symbolics decls in
  let module Symbs = (val defaultSymbolics symbs) in
  (*NOTE: Building Symbs (at least once) must be done before build_type_array,
     as defaultSymbolics populates type_array.*)

  (* Build the topology *)
  let graph =
    let n = get_nodes decls |> oget in
    let es = get_edges decls |> oget in
    List.fold_left AdjGraph.add_edge_e (AdjGraph.create n) es
  in
  let module G : Topology = struct
    let graph = graph
  end
  in
  (* build bdd and type arrays so that lookups during execution will work *)
  Collections.TypeIds.seal type_store;
  (*build_bdd_array (); *)
  Collections.ExpIds.seal pred_store;
  (* Build a simulator for SRPs *)
  let module SrpSimulator = (val (module SrpSimulation (G)) : SrpSimulationSig) in
  (* Load compiled NV program*)
  let module CompleteSRP = (val get_srp ()) in
  (* Plug everything together to simulate the SRPs - this is where simulation occurs*)
  (* Doing the time profiling manually because I don't know how to make it work with modules *)
  let start_time = Sys.time () in
  let module Srp = (val (module CompleteSRP (Symbs) (SrpSimulator)) : NATIVE_SRP) in
  let finish_time = Sys.time () in
  Printf.printf
    "Native simulation took: %f secs to complete\n%!"
    (finish_time -. start_time);
  (* Get the computed solutions *)
  build_solutions (AdjGraph.nb_vertex graph) Srp.record_fns !SrpSimulator.solved
;;
