(** * SMT encoding of network *)

open Nv_lang.Collections
open Nv_solution.Solution
open Nv_utils.Profile
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

type smt_result = Unsat | Unknown | Sat of Nv_solution.Solution.t

(** ** Translate the environment to SMT-LIB2 *)

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
  Printf.sprintf "(push)%s\n %s\n %s\n" decls constants context

let check_sat info =
  Printf.sprintf "%s\n"
    ((CheckSat |> mk_command) |> command_to_smt smt_config.verbose info)

(* Emits the query to a file in the disk *)
let printQuery (chan: out_channel Lazy.t) (msg: string) =
  let chan = Lazy.force chan in
  Printf.fprintf chan "%s\n%!" msg

let expr_encoding smt_config =
  match smt_config.unboxing with
  | true -> (module SmtUnboxed.Unboxed : ExprEncoding)
  | false -> (module SmtBoxed.Boxed : ExprEncoding)

(* Asks the SMT solver to return a model and translates it to NV lang *)
let ask_for_model query chan info env solver renaming nodes eassert =
  (* build a counterexample based on the model provided by Z3 *)
  let model = eval_model env.SmtUtils.symbolics nodes eassert renaming in
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
let get_sat query chan info env solver renaming nodes eassert reply =
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
    ask_for_model query chan info env solver renaming nodes eassert
  | UNKNOWN ->
    Unknown
  | _ -> failwith "unexpected answer from solver\n"

let refineModel (model : Nv_solution.Solution.t) info query chan env solver renaming
    nodes eassert requires =
  let refiner = refineModelMinimizeFailures in
  match refiner model info query chan solver renaming env requires with
  | None ->
    (* Nv_lang.Console.warning "Model was not refined\n"; *)
    Sat model (* no refinement can occur *)
  | Some q ->
    Nv_lang.Console.warning "Refining the model...\n";
    let checkSat = CheckSat |> mk_command |> command_to_smt smt_config.verbose info in
    let q = Printf.sprintf "%s%s\n" q checkSat in
    if query then
      (printQuery chan q);
    ask_solver solver q;
    let reply = solver |> parse_reply in
    let isSat = get_sat query chan info env solver renaming nodes eassert reply in
    (* if the second query was unsat, return the first counterexample *)
    match isSat with
    | Sat _newModel ->
      Nv_lang.Console.warning "Refined the model";
      isSat
    | _ -> Sat model

(* Apparently not setting this option can lead to Z3 not giving us a response *)
let solver = lazy(let solver = start_solver [] in
                  ask_solver solver "(set-option :model_evaluator.completion true)\n";
                  solver)

let solve info query chan net_or_srp nodes eassert requires =
  let solver = Lazy.force solver in
  let print_and_ask q =
    if query then
      printQuery chan q;
    ask_solver_blocking solver q
  in
  let solve_aux () =
    let renaming, env =
      time_profile_absolute "Encoding network"
        (fun () -> let env = net_or_srp () in
          if smt_config.optimize then propagate_eqs env
          else (StringMap.empty, StringMap.empty), env)
    in
    (* compile the encoding to SMT-LIB *)
    let smt_encoding =
      time_profile_absolute "Compiling query"
        (fun () -> env_to_smt ~verbose:smt_config.verbose info env) in
    (* print query to a file if asked to *)

    (* Printf.printf "communicating with solver"; *)
    print_and_ask smt_encoding;
    match smt_config.failures with
    | None ->
      let q = check_sat info in
      print_and_ask q;
      let reply = solver |> parse_reply in
      get_sat query chan info env solver renaming nodes eassert reply
    | Some _ ->
      let q = check_sat info in
      (* ask if it is satisfiable *)
      print_and_ask q;
      let reply = solver |> parse_reply in
      (* check the reply *)
      let isSat = get_sat query chan info env solver renaming nodes eassert reply in
      (* In order to minimize refinement iterations, once we get a
         counter-example we try to minimize it by only keeping failures
         on single links. If it works then we found an actual
         counterexample, otherwise we refine using the first
         counterexample. *)
      match isSat with
      | Unsat -> Unsat
      | Unknown -> Unknown
      | Sat model1 ->
        refineModel model1 info query chan env solver renaming nodes eassert requires
  in
  print_and_ask "(push)";
  let ret = solve_aux () in
  print_and_ask "(pop)";
  ret

let solveClassic info query chan net =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc =
    (val (module SmtClassicEncoding.ClassicEncoding(ExprEnc) : SmtClassicEncoding.ClassicEncodingSig))
  in
  solve info query chan (fun () -> Enc.encode_z3 net)
    (Nv_datastructures.AdjGraph.nb_vertex net.graph) net.assertion net.requires

let solveFunc info query chan srp =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc =
    (val (module SmtFunctionalEncoding.FunctionalEncoding(ExprEnc) : SmtFunctionalEncoding.FunctionalEncodingSig))
  in
  solve info query chan (fun () -> Enc.encode_z3 srp)
    (Nv_datastructures.AdjGraph.nb_vertex srp.srp_graph) srp.srp_assertion srp.srp_requires

(** For quickcheck smart value generation *)
let symvar_assign info (net: Nv_lang.Syntax.network) : Nv_lang.Syntax.value VarMap.t option =
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding(ExprEnc) : Encoding)) in
  let env = ExprEnc.init_solver net.Nv_lang.Syntax.symbolics ~labels:[] in
  let requires = net.Nv_lang.Syntax.requires in
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
    Some model.Nv_solution.Solution.symbolics
  | _ -> failwith "Unexpected reply from SMT solver"
