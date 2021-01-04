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
open Nv_kirigami.SrpRemapping

let solve info query chan net_or_srp nodes assertions guarantees globals =
  let solver = Lazy.force solver in
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

    (* Printf.printf "communicating with solver"; *)
    (* TODO: split the encoding after the guarantees;
     * then call check_sat + get_sat, return reply,
     * and then add the rest of the encoding,
     * call check_sat + get_sat again, and then return reply2
     *)
    let enc_parts = String.split_on_string smt_encoding ~by:"(echo \"#END_OF_SCOPE#\")" in
    (* 3 parts if we have globals, otherwise 2 parts *)
    let enc_part0, enc_part1, enc_part2 =
      match enc_parts with
      | [a; b; c] -> Some a, b, c
      | [a; b] -> None, a, b
      | _ -> failwith "solveKirigami: wrong number of scopes"
    in
    let get_ret enc assertions guarantees =
      print_and_ask enc;
      let q = check_sat info in
      print_and_ask q;
      let reply = solver |> parse_reply in
      get_sat
        query
        chan
        info
        env
        solver
        renaming
        nodes
        assertions
        guarantees
        globals
        reply
    in
    let ret0 = Option.map (fun enc -> get_ret enc 0 0) enc_part0 in
    let ret1 = get_ret enc_part1 0 guarantees in
    let ret2 = get_ret enc_part2 assertions 0 in
    let and_ret r1 r2 =
      match r1 with
      | Unsat -> r2
      | _ -> r1
    in
    match ret0 with
    | Some Unsat -> and_ret ret1 ret2
    | Some r -> r
    | None -> and_ret ret1 ret2
  in
  (* Initial check *)
  print_and_ask "(push)";
  let ret = solve_aux () in
  print_and_ask "(pop)";
  ret
;;

(* Solver for Kirigami *)
let solveKirigami info query chan ~part ~decls =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let assertions = List.length (get_asserts decls) in
  (* count up a guarantee for every predicate on every output *)
  let outputs = VertexMap.fold (fun _ l acc -> l @ acc) part.outputs [] in
  let guarantees = List.fold_left (fun acc (_, ps) -> List.length ps + acc) 0 outputs in
  let globals = List.length outputs + (2 * part.nodes) in
  solve
    info
    query
    chan
    (fun () -> Enc.kirigami_encode_z3 part decls)
    (get_old_nodes part)
    assertions
    guarantees
    globals
;;
