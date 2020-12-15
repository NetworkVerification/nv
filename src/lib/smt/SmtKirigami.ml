open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SmtUtils
open SolverUtil
open SmtEncodingSigs
open Smt
open Nv_lang
open Nv_datastructures.AdjGraph
open Nv_kirigami.SrpRemapping

(* Solver for Kirigami *)
let solveKirigami info query chan ~part ~decls =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let nodes = Nv_datastructures.AdjGraph.nb_vertex (get_graph decls |> oget) in
  let assertions = List.length (get_asserts decls) in
  let guarantees = VertexMap.fold (fun _ l acc -> List.length l + acc) part.outputs 0 in
  solve
    info
    query
    chan
    (fun () -> Enc.kirigami_encode_z3 part decls)
    nodes
    assertions
    guarantees
;;
