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
open Nv_kirigami.SrpRemapping

let solve info query chan net_or_srp nodes assertions guarantees =
  let solver = Lazy.force solver in
  let print_and_ask q =
    if query then printQuery chan q;
    ask_solver_blocking solver q
  in
  let solve_aux () =
    let renaming, env  =
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

    (* Printf.printf "communicating with solver"; *)
    (* TODO: split the encoding after the guarantees;
     * then call check_sat + get_sat, return reply,
     * and then add the rest of the encoding,
     * call check_sat + get_sat again, and then return reply2
     *)
    let enc_part1, enc_part2 = BatString.split smt_encoding ~by:"(echo \"#END_OF_GUARANTEES#\")" in
    print_and_ask enc_part1;
    let q = check_sat info in
    print_and_ask q;
    let reply = solver |> parse_reply in
    let ret1 = get_sat query chan info env solver renaming nodes 0 guarantees reply in
    print_and_ask enc_part2;
    let q = check_sat info in
    print_and_ask q;
    let reply2 = solver |> parse_reply in
    let ret2 = get_sat query chan info env solver renaming nodes assertions 0 reply2 in
    ret1, ret2
  in
  (* Initial check *)
  print_and_ask "(push)";
  let (ret1, ret2) = solve_aux () in
  print_and_ask "(pop)";
  match ret1 with
  | Unsat -> ret2
  | _ -> ret1
;;


(* Solver for Kirigami *)
let solveKirigami info query chan ~part ~decls =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let assertions = List.length (get_asserts decls) in
  let guarantees = VertexMap.fold (fun _ l acc -> List.length l + acc) part.outputs 0 in
  solve
    info
    query
    chan
    (fun () -> Enc.kirigami_encode_z3 part decls)
    (get_old_nodes part)
    assertions
    guarantees
;;
