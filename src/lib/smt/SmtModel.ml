open Nv_lang
open Nv_lang.Collections
open Nv_lang.Syntax
open Nv_solution.Solution
open Nv_datastructures
open SmtUtils
open SmtLang
open SolverUtil
open Batteries
open Nv_utils.OCamlUtils

(** Emits the code that evaluates the model returned by Z3. *)
let eval_model
    (symbolics : Syntax.ty_or_exp VarMap.t)
    (num_nodes : int list)
    (assertions : int)
    (guarantees : int)
    (renaming : string StringMap.t * smt_term StringMap.t)
    : command list
  =
  ignore num_nodes;
  let renaming, valMap = renaming in
  let var x = "Var:" ^ x in
  let find_renamed_term str =
    let renamed = StringMap.find_default str str renaming in
    let smt_term =
      match StringMap.Exceptionless.find renamed valMap with
      | None -> mk_var renamed
      | Some tmv -> tmv
    in
    mk_term smt_term
  in
  let base = [mk_echo "\"end_of_model\"" |> mk_command] in
  (* Compute eval statements for guarantees (Kirigami) *)
  let guarantee_cmds =
    List.fold_lefti
      (fun acc i _ ->
        let assu = Printf.sprintf "guarantee-%d" i in
        let tm = find_renamed_term assu in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ var assu ^ "\"") |> mk_command in
        ec :: ev :: acc)
      base
      (list_seq guarantees)
  in
  (* Compute eval statements for assertions *)
  let assertion_cmds =
    List.fold_lefti
      (fun acc i _ ->
        let assu = Printf.sprintf "assert-%d" i in
        let tm = find_renamed_term assu in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ var assu ^ "\"") |> mk_command in
        ec :: ev :: acc)
      guarantee_cmds
      (list_seq assertions)
  in
  (* Compute eval statements for symbolic variables *)
  let symbols =
    VarMap.fold
      (fun sv _ acc ->
        let sv = SmtUtils.symbolic_var sv in
        let z3name = sv in
        let tm = find_renamed_term z3name in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ var sv ^ "\"") |> mk_command in
        ec :: ev :: acc)
      symbolics
      assertion_cmds
  in
  symbols
;;

let rec parse_model (solver : solver_proc) =
  let rs = get_reply_until "end_of_model" solver in
  let rec loop rs model =
    match rs with
    | [] -> MODEL model
    | [v] when v = "end_of_model" -> MODEL model
    | vname :: rs when BatString.starts_with vname "Var:" ->
      let vname = BatString.lchop ~n:4 vname in
      let rec grab_vals rs acc =
        match rs with
        | [] -> failwith "expected string"
        | v :: _ when BatString.starts_with v "Var:" || v = "end_of_model" -> acc, rs
        | v :: rs' -> grab_vals rs' (acc ^ v)
      in
      let vval, rs' = grab_vals rs "" in
      loop rs' (BatMap.add vname vval model)
    | _ -> failwith "wrong format"
  in
  loop rs BatMap.empty
;;

let parse_val (s : string) : Syntax.value =
  let lexbuf = Lexing.from_string s in
  try SMTParser.smtlib SMTLexer.token lexbuf with
  | _exn ->
    let tok = Lexing.lexeme lexbuf in
    failwith (Printf.sprintf "failed to parse string %s on %s" s tok)
;;

let box_vals (xs : (int * Syntax.value) list) =
  match xs with
  | [(_, v)] -> v
  | _ ->
    vtuple
      (BatList.sort (fun (x1, _x2) (y1, _y2) -> compare x1 y1) xs
      |> BatList.map (fun (_, y) -> y))
;;

let translate_model_unboxed nodes (m : (string, string) BatMap.t) : Nv_solution.Solution.t
  =
  let symbolics, solves, assertions, guarantees =
    BatMap.foldi
      (fun k v (symbolics, solves, assertions, guarantees) ->
        let nvval = parse_val v in
        match k with
        | k when BatString.starts_with k "guarantee" ->
          let guar =
            match nvval.v with
            | VBool b -> b
            | _ -> failwith "Bad guarantee"
          in
          symbolics, solves, assertions, guar :: guarantees
        | k when BatString.starts_with k "assert" ->
          let asn =
            match nvval.v with
            | VBool b -> b
            | _ -> failwith "Bad assert"
          in
          symbolics, solves, asn :: assertions, guarantees
        | k when BatString.starts_with k "solve" ->
          let kname = Var.of_var_string k in
          symbolics, (kname, nvval) :: solves, assertions, guarantees
        | k ->
          let new_symbolics = (Var.of_var_string k, nvval) :: symbolics in
          new_symbolics, solves, assertions, guarantees)
      m
      ([], [], [], [])
  in
  let box v = { sol_val = v; mask = None; attr_ty = Syntax.TUnit } in
  (*Tunit is arbitrary here**)
  { symbolics = List.rev symbolics
  ; solves = List.rev_map (fun (k, v) -> k, box v) solves
  ; assertions = List.rev assertions
  ; guarantees = List.rev guarantees
  ; nodes
  }
;;
