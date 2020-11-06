open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SmtUtils
open SolverUtil
open SmtEncodingSigs
open Smt
open Nv_lang
open Nv_kirigami.Partition

(* Solver for Kirigami, which performs two SMT encodings, one for initial checks and one for safety checks.
*)
let solveKirigami info query chan ~decls =
  (* TODO: unfinished *)
  let { lesser_hyps; greater_hyps; guarantees; properties; network } = decls in
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  (* second solve *)
  let nodes = Nv_datastructures.AdjGraph.nb_vertex (get_graph network |> oget) in
  let assertions = get_asserts properties in
  let ranked_initial_decls = lesser_hyps @ guarantees @ network in
  (* FIXME: report this result and introduce scoping *)
  let ranked_result =
    solve
      info
      query
      chan
      (fun () -> Enc.encode_z3 ranked_initial_decls)
      nodes
      assertions
      lesser_hyps
  in
  let safety_decls = lesser_hyps @ greater_hyps @ properties @ network in
  solve
    info
    query
    chan
    (fun () -> Enc.encode_z3 safety_decls)
    nodes
    assertions
    (lesser_hyps @ greater_hyps)
;;
