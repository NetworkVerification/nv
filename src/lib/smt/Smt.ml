(** * SMT encoding of network *)

open Nv_lang
open Nv_lang.Collections
open Nv_solution.Solution
open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SolverUtil
open SmtUtils
open SmtLang
open SmtEncodingSigs
open SmtOptimizations
open SmtModel

(* TODO:
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.
   * Don't hardcode tactics, try psmt (preliminary results were bad),
     consider par-and/par-or once we have multiple problems to solve.*)

type smt_result =
  | Unsat
  | Unknown
  | Timeout
  | Sat of Nv_solution.Solution.t

(** ** Translate the environment to SMT-LIB2 *)

let env_to_smt ?(verbose = false) ?(name_asserts = false) info (env : smt_env) =
  let count = ref (-1) in
  let map_fun =
    if name_asserts
    then (fun c ->
      count := !count + 1;
      smt_command_to_smt ~name_asserts:true ~count:!count info c.com)
    else fun c -> smt_command_to_smt info c.com
  in
  let context = BatList.rev_map map_fun env.ctx in
  let context = BatString.concat "\n" context in
  (* Emit constants *)
  let constants = ConstantSet.to_list env.const_decls in
  let constants =
    BatString.concat
      "\n"
      (BatList.map (fun c -> const_decl_to_smt ~verbose info c) constants)
  in
  (* Emit type declarations *)
  let decls = StringMap.bindings env.type_decls in
  let decls =
    String.concat "\n" (BatList.map (fun (_, typ) -> type_decl_to_smt typ) decls)
  in
  Printf.sprintf "(push)%s\n %s\n %s\n" decls constants context
;;

let check_sat info =
  Printf.sprintf "%s\n" (CheckSat |> mk_command |> command_to_smt smt_config.verbose info)
;;

(* Emits the query to a file in the disk *)
let printQuery (chan : out_channel Lazy.t) (msg : string) =
  let chan = Lazy.force chan in
  Printf.fprintf chan "%s\n%!" msg
;;

let expr_encoding smt_config =
  match smt_config.unboxing with
  | true -> (module SmtUnboxed.Unboxed : ExprEncoding)
  | false -> failwith "Boxed encoding no longer supported"
;;

(* Asks the SMT solver to return a model and translates it to NV lang *)
let ask_for_model query chan info env solver renaming nodes asserts guars =
  (* build a counterexample based on the model provided by Z3 *)
  let model = eval_model env.SmtUtils.symbolics asserts guars renaming in
  let model_question = commands_to_smt smt_config.verbose info model in
  ask_solver solver model_question;
  if query then printQuery chan model_question;
  let model = solver |> parse_model in
  match model with
  | MODEL m -> Sat (translate_model_unboxed nodes m)
  | OTHER s ->
    Printf.printf "%s\n" s;
    failwith "failed to parse a model"
  | _ -> failwith "failed to parse a model"
;;

let ask_if_canceled solver =
  ask_solver solver "(get-info :reason-unknown)\n\n(echo \"end why\")\n";
  let rs = get_reply_until "end why" solver in
  let rs = String.concat "\n" rs in
  BatString.exists rs "canceled"
;;

(** Asks the smt solver whether the query was unsat or not
    and returns a model if it was sat.*)
let get_sat query chan info env solver renaming nodes asserts guars reply =
  ask_solver
    solver
    "(get-info :all-statistics)\n\n                         (echo \"end stats\")\n";
  let rs = get_reply_until "end stats" solver in
  let rs =
    BatList.filter
      (fun s -> BatString.starts_with s " :time" || BatString.starts_with s " :memory")
      rs
    |> String.concat "\n"
  in
  Printf.printf "Z3 stats:\n %s\n" rs;
  match reply with
  | UNSAT -> Unsat
  | SAT -> ask_for_model query chan info env solver renaming nodes asserts guars
  | UNKNOWN -> if ask_if_canceled solver then Timeout else Unknown
  | _ -> failwith "unexpected answer from solver\n"
;;

let solver time =
  let params = if time > 0 then [Printf.sprintf "-t:%d" (time * 1000)] else [] in
  lazy
    (let solver = start_solver params in
     (* Apparently not setting this option can lead to Z3 not giving us a response *)
     ask_solver solver "(set-option :model_evaluator.completion true)\n";
     solver)
;;

let solve info query time chan net_or_srp nodes assertions =
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

    (* Printf.printf "communicating with solver"; *)
    print_and_ask smt_encoding;
    let q = check_sat info in
    print_and_ask q;
    let reply = solver |> parse_reply in
    get_sat query chan info env solver renaming nodes assertions 0 reply
  in
  print_and_ask "(push)";
  let ret = solve_aux () in
  print_and_ask "(pop)";
  ret
;;

let solveClassic info query time chan ~decls =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  solve
    info
    query
    time
    chan
    (fun () -> Enc.encode_z3 decls)
    (Nv_datastructures.AdjGraph.vertices (get_graph decls |> oget))
    (List.length (get_asserts decls))
;;
