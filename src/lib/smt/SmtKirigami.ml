open Batteries
open Nv_lang
open Nv_lang.Collections
open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SmtUtils
open SolverUtil
open SmtEncodingSigs
open Smt
open SmtOptimizations
open Nv_datastructures.AdjGraph

type kirigami_result =
  | Unknown
  | Timeout
  (* guarantee is unsat, fail early *)
  | GuaranteeFailure
  (* guarantee is sat, but property fails *)
  | PropertyFailure of Nv_solution.Solution.t
  (* guarantee is sat, property holds *)
  | PropertyPass

let solve info query time chan net_or_srp nodes assertions guarantees =
  let solver = Lazy.force (solver time) in
  let print_and_ask q =
    if query then printQuery chan q;
    ask_solver_blocking solver q
  in
  let solve_aux () =
    let renaming, env =
      time_profile_absolute "Encoding network" (fun () ->
          let env = net_or_srp () in
          (* debugging *)
          (* print_endline (env_to_smt ~verbose:smt_config.verbose info env); *)
          if smt_config.optimize
          then propagate_eqs env
          else (StringMap.empty, StringMap.empty), env)
    in
    (* compile the encoding to SMT-LIB *)
    let smt_encoding =
      time_profile_absolute "Compiling query" (fun () ->
          env_to_smt ~verbose:smt_config.verbose info env)
    in
    (* print query to a file if asked to *)

    (* submit the given encoded SMT string to the solver, which returns a result for the given
       number of assertions and guarantees
     *)
    let get_ret enc nassertions nguarantees =
      print_and_ask enc;
      let q = check_sat info in
      print_and_ask q;
      let reply = solver |> parse_reply in
      get_sat query chan info env solver renaming nodes nassertions nguarantees reply
    in
    let enc_parts = String.split_on_string smt_encoding ~by:"(echo \"#END_OF_SCOPE#\")" in
    let enc_part1, enc_part2 =
      match enc_parts with
      | [a; b] -> a, b
      | _ -> failwith "solveKirigami: wrong number of scopes"
    in
    (* ask if there is a satisfying assignment for the guarantees *)
    let ret1 = get_ret enc_part1 0 guarantees in
    (* ask if there is a solution that does not satisfy the assertions *)
    let ret2 = get_ret enc_part2 assertions guarantees in
    match ret1 with
    | Sat _ -> (match ret2 with
        | Sat m -> PropertyFailure m
        | Unsat -> PropertyPass
        | Unknown -> Unknown
        | Timeout -> Timeout)
    | Unsat -> GuaranteeFailure
    | Unknown -> Unknown
    | Timeout -> Timeout
  in
  print_and_ask "(push)";
  let ret = solve_aux () in
  print_and_ask "(pop)";
  ret
;;

(* Solver for Kirigami *)
let solveKirigami info query time chan ~part decls =
  let open Nv_lang.Syntax in
  let open Nv_kirigami.SrpRemapping in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let assertions = List.length (get_asserts decls) in
  (* print_endline (Printing.declarations_to_string decls); *)
  (* count up a guarantee for every predicate on every output *)
  let outputs = VertexMap.fold (fun _ l acc -> l @ acc) part.outputs [] in
  let guarantees = List.fold_left (fun acc (_, ps) -> List.length ps + acc) 0 outputs in
  solve
    info
    query
    time
    chan
    (fun () -> Enc.kirigami_encode_z3 part decls)
    part.nodes
    assertions
    guarantees
;;
