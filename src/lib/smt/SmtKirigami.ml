open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SmtUtils
open SolverUtil
open SmtEncodingSigs
open Smt
open Nv_lang
open Nv_kirigami.Partition

(* Solver for Kirigami *)
let solveKirigami info query chan ~decls =
  let { lesser_hyps; greater_hyps; guarantees; properties; network } = decls in
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let nodes = Nv_datastructures.AdjGraph.nb_vertex (get_graph network |> oget) in
  let assertions = get_asserts properties @ get_asserts guarantees in
  solve
    info
    query
    chan
    (fun () -> Enc.kirigami_encode_z3 decls)
    nodes
    assertions
    (lesser_hyps @ greater_hyps)
;;
