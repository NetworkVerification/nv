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
open Smt

(** Removes all variable equalities *)
(** Modified from propagate_eqs in SmtOptimizations.ml. It has the following
    differences:

    We do NOT propagate equalities between label- variables and merge-result
    variables. This allows us to selectively remove some of those equalities
    during hiding.

    We do NOT propagate equalities between constants (i.e ints/bools) and
    variables. We probably want to allow this later (TODO), but for now I
    don't want to think about it.

    We also ensure that the label- variables are used as the representatives
    for the equivalence classes of variables. *)
let propagate_eqs_for_hiding (env : smt_env) =
  let updateUnionFind eqSets s =
    try
      StringMap.find s eqSets, eqSets
    with Not_found ->
      let r = BatUref.uref s in
      r, StringMap.add s r eqSets
  in
  (* True iff this is not an equality between a label- and a merge- variable *)
  let should_propagate s1 s2 =
    not @@
    (* FIXME: The bit that checks for -result is a little fragile, since a user could
              conceivably make a variable name containing that string. If it starts
              causing problems we won't lose any precision by removing it. *)
    (BatString.starts_with s1 "label-" && BatString.starts_with s2 "merge-" && BatString.exists s2 "-result") ||
    (BatString.starts_with s2 "label-" && BatString.starts_with s1 "merge-" && BatString.exists s1 "-result")
  in
  (* Used for BatUref.unite to ensure it always selects label- variables if
     possible, so the resulting SMT program has things in terms of the attributes
     of each node *)
  let sel s1 s2 = if BatString.starts_with s1 "label-" then s1 else s2 in
  (* compute equality classes of variables and remove equalities between variables *)
  let (eqSets, valMap, new_ctx) = BatList.fold_left (fun (eqSets, valMap, acc) c ->
      match c.com with
      | Assert tm ->
        (match tm.t with
         | Eq (tm1, tm2) ->
           (match tm1, tm2 with
            | Var s1, Var s2 when should_propagate s1 s2 ->
              let r1, eqSets = updateUnionFind eqSets s1 in
              let r2, eqSets = updateUnionFind eqSets s2 in
              BatUref.unite ~sel:sel r1 r2;
              (eqSets, valMap, acc)
            (* | Var s1, Int _ | Var s1, Bool _ ->
               let valMap = StringMap.add s1 tm2 valMap in
               (eqSets, valMap, acc) *)
            | _ -> (eqSets, valMap, c :: acc))
         | _ -> (eqSets, valMap, c :: acc))
      | _ -> (eqSets, valMap, c :: acc))
      (StringMap.empty, StringMap.empty, []) env.ctx
  in
  let renaming = StringMap.map (fun r -> BatUref.uget r) eqSets in
  let newValMap = StringMap.fold (fun s v acc ->
      match StringMap.Exceptionless.find s renaming with
      | None -> StringMap.add s v acc
      | Some r -> StringMap.add r v acc) valMap StringMap.empty
  in
  (* apply the computed renaming *)
  env.ctx <- BatList.rev_map (fun c ->
      match c.com with
      | Assert tm ->
        {c with com = Assert (alpha_rename_term renaming newValMap tm)}
      | Eval tm ->
        {c with com = Eval (alpha_rename_term renaming newValMap tm)}
      | _  -> c) new_ctx;
  (* remove unnecessary declarations *)
  (* had to increase stack size to avoid overflow here..
     consider better implementations of this function*)
  env.const_decls <-
    ConstantSet.filter (fun cdecl ->
        if StringMap.mem cdecl.cname newValMap then false
        else
          begin
            try
              let repr = StringMap.find cdecl.cname renaming in
              if repr = cdecl.cname then true else false
            with Not_found ->
              true
          end) env.const_decls;
  renaming, env
;;

(* Retrieve the names of all smt variables which appear in tm *)
let rec get_vars (tm : SmtLang.smt_term) : string list =
  (* This could be optimized to not use @ and be tail-reursive, but I don't
     think our terms are ever very large so it probably doesn't matter *)
  match tm with
  | SmtLang.Int _
  | SmtLang.Bool _
  | SmtLang.Bv _
  | SmtLang.Constructor _ ->
    []
  | SmtLang.Var s ->
    [s]
  | SmtLang.Not tm1 ->
    get_vars tm1
  | SmtLang.And (tm1, tm2)
  | SmtLang.Or (tm1, tm2)
  | SmtLang.Add (tm1, tm2)
  | SmtLang.Sub (tm1, tm2)
  | SmtLang.Eq (tm1, tm2)
  | SmtLang.Lt (tm1, tm2)
  | SmtLang.Leq (tm1, tm2) ->
    get_vars tm1 @ get_vars tm2
  | SmtLang.Ite (tm1, tm2, tm3) ->
    get_vars tm1 @ get_vars tm2 @ get_vars tm3
  | SmtLang.AtMost (tms1, tms2, tm1) ->
    get_vars tm1 @ (List.concat @@ List.map get_vars tms1) @ (List.concat @@ List.map get_vars tms2)
  | SmtLang.App (tm1, tms) ->
    get_vars tm1 @ (List.concat @@ List.map get_vars tms)
;;

(* Overall alg:
   Remove all constraints and decls except the assertion
   Re-add decls for each variable in the assertions
   Unhide all starting_vars (once I figure out how to format them)
   When unhiding variables:
      Re-add their constraint & decl
      for each var in the constraint:
        if it's not a label var, recursively unhide it
        otherwise, just add its decl
*)

let get_vars_in_command com =
  match com.com with
  | Assert tm -> get_vars tm.t
  | _ -> []
;;

let get_assert_var com =
  match com.com with
  | Assert tm ->
    begin
      match tm.t with
      | Eq (Var s1, _) -> Some (s1)
      | _ -> None
    end
  | _ -> None
;;

(*
  This data structure represents the current state of a partially hidden network.
  For each variable:
  The bool represents whether that variable is currently hidden
  The command is the constraint for that variable
  The constant is the declaration of that variable
*)
type hiding_map = (bool * command * constant) StringMap.t
(* A hiding map, together with an integer which represents the number of
   currently hidden variables *)
type hiding_status = {map : hiding_map; hidden : int}

(*
  Hide all variables except those which are involved in the assertion. Return
  * A starting Z3 program
  * A hiding map
  * The number of hidden variables
*)
let construct_starting_env (full_env : smt_env) : smt_env * hiding_status =
  (* Step 1: Remove all variable equality commands that don't involve the
     assertion *)
  let must_keep com =
    match get_assert_var com with
    | None -> true
    | Some s1 -> BatString.starts_with s1 "assert-"
  in
  let ctx = BatList.filter must_keep full_env.ctx in

  (* Step 2: Add decls for all variables which appear in ctx *)
  let activeVars = List.concat @@ List.map get_vars_in_command ctx in
  let const_decls, hidden_decls =
    ConstantSet.partition (fun const -> List.mem const.cname activeVars) full_env.const_decls
  in

  let type_decls = full_env.type_decls in
  let symbolics = full_env.symbolics in

  (* Step 3: Create out mapping of variables to their constraint and const_decl *)
  let com_map : command StringMap.t =
    List.fold_left
      (fun map com ->
         match get_assert_var com with
         | None -> map
         | Some s1 -> StringMap.add s1 com map)
      StringMap.empty
      ctx
  in
  let hidden_map =
    ConstantSet.fold
      (fun const map ->
         let com = StringMap.find const.cname com_map in
         StringMap.add const.cname (false, com, const) map)
      const_decls
      StringMap.empty
  in
  let hidden_map =
    ConstantSet.fold
      (fun const map ->
         let com = StringMap.find const.cname com_map in
         StringMap.add const.cname (true, com, const) map)
      hidden_decls
      hidden_map
  in
  {ctx; const_decls; type_decls; symbolics},
  {map=hidden_map; hidden=ConstantSet.cardinal hidden_decls}
;;

(* Given an env with some variables hidden, and the full env, unhide the variable
   var and all intermediate variables it depends on.

   TODO: Plenty of potential for optimization here. We could store a list of which
   variables are hidden at a given point, and check that; we could also
   have a dict mapping variables to their constraint. *)
let rec unhide_variable hiding_status var : hiding_status * command list * ConstantSet.t =
  let hidden, com, const = StringMap.find var hiding_status.map in
  if not hidden then
    hiding_status, [], ConstantSet.empty
  else
    let new_map = StringMap.update var var (false, com, const) hiding_status.map in
    let new_hiding_status = {map=new_map; hidden=hiding_status.hidden-1} in

    let additional_vars_to_unhide = get_vars_in_command com in
    (* We could make this tail-recursive if we're having problems with the stack,
       or if we want it to be a little more efficient. *)
      List.fold_left
        (fun (hs, coms, consts) var ->
           let hs', coms', consts' = unhide_variable hs var in
           hs', coms @ coms', ConstantSet.union consts consts'
        )
        (new_hiding_status, [com], ConstantSet.singleton const)
        additional_vars_to_unhide
;;

(* Right now just a copy of the solve function from Smt.ml *)
let solve_hiding info query chan ?symbolic_vars ?(params=[]) ?(starting_vars=[]) net =
  let sym_vars =
    match symbolic_vars with None -> [] | Some ls -> ls
  in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc =
    (val (if smt_config.encoding = Classic then
            (module ClassicEncoding(ExprEnc) : Encoding)
          else
            (module FunctionalEncoding(ExprEnc) : Encoding)))
  in
  (* compute the encoding of the network *)
  let renaming, full_env =
    time_profile "Encoding network"
      (fun () -> let env = Enc.encode_z3 net sym_vars in
        propagate_eqs_for_hiding env)
  in
  let partial_env = construct_starting_env full_env in
  (* TODO: add starting_vars once I figure that out *)
  let env = full_env in
  (* compile the encoding to SMT-LIB *)
  let smt_encoding =
    time_profile "Compiling query"
      (fun () -> env_to_smt ~verbose:smt_config.verbose info env) in
  (* print query to a file if asked to *)
  if query then
    printQuery chan smt_encoding;

  failwith "Not past here yet";
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
