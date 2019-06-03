(** * SMT encoding of network *)

open Collections
open Syntax
open Solution
open SolverUtil
open Profile
open SmtLang
open SmtExprEncodings
open SmtUtils
open SmtEncodings
open SmtOptimizations
open SmtModel

(* TODO:
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.
   * Don't hardcode tactics, try psmt (preliminary results were bad),
     consider par-and/par-or once we have multiple problems to solve.*)

type smt_result = Unsat | Unknown | Sat of Solution.t

(** ** Translate the environment to SMT-LIB2 *)

(* TODO: For some reason this version of env_to_smt does not work correctly..
   maybe investigate at some point *)
(* let env_to_smt ?(verbose=false) info (env : smt_env) = *)
(* let buf = Buffer.create 8000000 in *)
(* (\* Emit context *\) *)
(* Buffer.add_string buf "(set-option :model_evaluator.completion true)"; *)
(* List.iter (fun c -> Buffer.add_string buf (command_to_smt verbose info c)) env.ctx; *)
(* ConstantSet.iter (fun c -> *)
(*     Buffer.add_string buf (const_decl_to_smt ~verbose:verbose info c)) env.const_decls; *)
(* Buffer.contents buf *)

let env_to_smt ?(verbose=false) ?(name_asserts=false) info (env : smt_env) =
  let count = ref (-1) in
  let map_fun =
    if name_asserts then
      (fun c ->  count := !count + 1; smt_command_to_smt ~name_asserts:true ~count:(!count) info c.com)
    else
      (fun c ->  smt_command_to_smt info c.com)
  in
  let context = BatList.rev_map map_fun env.ctx in
  let context = BatString.concat "\n" context in

  (* Emit constants *)
  let constants = ConstantSet.to_list env.const_decls in
  let constants =
    BatString.concat "\n"
      (BatList.map (fun c -> const_decl_to_smt ~verbose:verbose info c)
         constants)
  in
  (* Emit type declarations *)
  let decls = StringMap.bindings env.type_decls in
  let decls = String.concat "\n"
      (BatList.map (fun (_,typ) -> type_decl_to_smt typ) decls) in
  Printf.sprintf "(set-option :model_evaluator.completion true)
                          \n %s\n %s\n %s\n" decls constants context
(* this new line is super important otherwise we don't get a reply
   from Z3.. not understanding why*)

let check_sat info =
  Printf.sprintf "%s\n"
    ((CheckSat |> mk_command) |> command_to_smt smt_config.verbose info)

(* Emits the query to a file in the disk *)
let printQuery (chan: out_channel Lazy.t) (msg: string) =
  let chan = Lazy.force chan in
  Printf.fprintf chan "%s\n%!" msg

let expr_encoding smt_config =
  match smt_config.unboxing with
  | true -> (module Unboxed : ExprEncoding)
  | false -> (module Boxed : ExprEncoding)

(* Asks the SMT solver to return a model and translates it to NV lang *)
let ask_for_model query chan info env solver renaming net =
  (* build a counterexample based on the model provided by Z3 *)
  let num_nodes = AdjGraph.num_vertices net.graph in
  let eassert = net.assertion in
  let model = eval_model env.symbolics num_nodes eassert renaming in
  let model_question = commands_to_smt smt_config.verbose info model in
  ask_solver solver model_question;
  if query then
    printQuery chan model_question;
  let model = solver |> parse_model in
  (match model with
   | MODEL m ->
     if smt_config.unboxing then
       Sat (translate_model_unboxed m)
     else
       Sat (translate_model m)
   | OTHER s ->
     Printf.printf "%s\n" s;
     failwith "failed to parse a model"
   | _ -> failwith "failed to parse a model")


(** Asks the smt solver whether the query was unsat or not
    and returns a model if it was sat.*)
let get_sat query chan info env solver renaming net reply =
  ask_solver solver "(get-info :all-statistics)\n
                         (echo \"end stats\")\n";
  let rs = get_reply_until "end stats" solver in
  let rs =
    BatList.filter (fun s -> BatString.starts_with s " :time" ||
                             BatString.starts_with s " :memory") rs
    |> String.concat "\n"
  in
  Printf.printf "Z3 stats:\n %s\n" rs;
  match reply with
  | UNSAT -> Unsat
  | SAT ->
    ask_for_model query chan info env solver renaming net
  | UNKNOWN ->
    Unknown
  | _ -> failwith "unexpected answer from solver\n"

let refineModel (model : Solution.t) info query chan env solver renaming
    (net : Syntax.network) =
  let refiner = refineModelMinimizeFailures in
  match refiner model info query chan solver renaming env net with
  | None ->
    (* Console.warning "Model was not refined\n"; *)
    Sat model (* no refinement can occur *)
  | Some q ->
    Console.warning "Refining the model...\n";
    let checkSat = CheckSat |> mk_command |> command_to_smt smt_config.verbose info in
    let q = Printf.sprintf "%s%s\n" q checkSat in
    if query then
      (printQuery chan q);
    ask_solver solver q;
    let reply = solver |> parse_reply in
    let isSat = get_sat query chan info env solver renaming net reply in
    (* if the second query was unsat, return the first counterexample *)
    match isSat with
    | Sat newModel ->
      Console.warning "Refined the model";
      isSat
    | _ -> Sat model

let solve info query chan ?(sym_vars=[]) ?(params=[]) net =
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc =
    (val (if smt_config.encoding = Classic then
            (module ClassicEncoding(ExprEnc) : Encoding)
          else
            (module FunctionalEncoding(ExprEnc) : Encoding)))
  in

  (* compute the encoding of the network *)
  let renaming, env =
    time_profile "Encoding network"
      (fun () -> let env = Enc.encode_z3 net sym_vars in
        if smt_config.optimize then propagate_eqs env
        else (StringMap.empty, StringMap.empty), env)
  in
  (* compile the encoding to SMT-LIB *)
  let smt_encoding =
    time_profile "Compiling query"
      (fun () -> env_to_smt ~verbose:smt_config.verbose info env) in
  (* print query to a file if asked to *)
  if query then
    printQuery chan smt_encoding;
  (* Printf.printf "communicating with solver"; *)
  (* start communication with solver process *)
  let solver = start_solver params in
  ask_solver_blocking solver smt_encoding;
  match smt_config.failures with
  | None ->
    let q = check_sat info in
    if query then
      printQuery chan q;
    ask_solver solver q;
    let reply = solver |> parse_reply in
    get_sat query chan info env solver renaming net reply
  | Some k ->
    let q = check_sat info in
    if query then
      printQuery chan q;
    (* ask if it is satisfiable *)
    ask_solver solver q;
    let reply = solver |> parse_reply in
    (* check the reply *)
    let isSat = get_sat query chan info env solver renaming net reply in
    (* In order to minimize refinement iterations, once we get a
       counter-example we try to minimize it by only keeping failures
       on single links. If it works then we found an actual
       counterexample, otherwise we refine using the first
       counterexample. *)
    match isSat with
    | Unsat -> Unsat
    | Unknown -> Unknown
    | Sat model1 ->
      refineModel model1 info query chan env solver renaming net

(* For quickcheck smart value generation *)
let symvar_assign info (net: Syntax.network) : value VarMap.t option =
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc =  (val (module ClassicEncoding(ExprEnc) : Encoding)) in
  let env = ExprEnc.init_solver net.symbolics in
  let requires = net.requires in
  Enc.add_symbolic_constraints env requires env.symbolics;
  let smt_encoding = env_to_smt ~verbose:smt_config.verbose info env in
  let solver = start_solver [] in
  ask_solver_blocking solver smt_encoding;
  let q = check_sat info in
  ask_solver solver q;
  let reply = solver |> parse_reply in
  match reply with
  | UNSAT  | UNKNOWN -> None
  | SAT ->
    (* build model question *)
    let model = eval_model env.symbolics 0 None (StringMap.empty, StringMap.empty) in
    let model_question = commands_to_smt smt_config.verbose info model in
    ask_solver solver model_question;
    (* get answer *)
    let model = solver |> parse_model in
    let model =
      match model with
      | MODEL m ->
        if smt_config.unboxing then
          translate_model_unboxed m
        else
          translate_model m
      | OTHER s ->
        Printf.printf "%s\n" s;
        failwith "failed to parse a model"
      | _ -> failwith "failed to parse a model"
    in
    Some model.symbolics
  | _ -> failwith "Unexpected reply from SMT solver"
