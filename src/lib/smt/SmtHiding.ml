(** * SMT encoding of network *)

open Nv_lang.Collections
open Nv_utils.Profile
open SolverUtil
open SmtLang
open SmtUtils
open SmtOptimizations
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
  (* True iff this is not an equality between a label- and a merge- variable,
     or between an assert-result variable and anything *)
  let should_propagate s1 s2 =
    let should_not_propagate =
      (* FIXME: The bit that checks for -result is a little fragile, since a user could
                conceivably make a variable name containing that string. If it starts
                causing problems we won't lose any precision by removing it. *)
      (BatString.starts_with s1 "label-" && BatString.starts_with s2 "merge-" && BatString.exists s2 "-result") ||
      (BatString.starts_with s2 "label-" && BatString.starts_with s1 "merge-" && BatString.exists s1 "-result") ||
      (BatString.starts_with s1 "assert-" && BatString.ends_with s1 "-result") ||
      (BatString.starts_with s2 "assert-" && BatString.ends_with s2 "-result")
    in
    not should_not_propagate
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
  (renaming, valMap), env
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

(* Return a map which sends a variable to the list of all constraints on that
   variable. *)
let map_vars_to_commands env : command list StringMap.t =
  (* Find the list of commands which involve only symbolic variable*)
  let update_map com map var =
    let old_coms = StringMap.find var map in
    StringMap.update var var (com::old_coms) map
  in
  let default_map =
    ConstantSet.fold
      (fun const acc -> StringMap.add const.cname [] acc)
      env.const_decls
      StringMap.empty
  in
  let add_com map com =
    match get_vars_in_command com with
    | [] -> map
    | lst ->
      (* If this is true, then this is *definitely* a "require" clause *)
      if BatList.for_all (fun s -> BatString.starts_with s "symbolic-") lst
      (* So unhide this clause when we unhide any of the symbolic variables *)
      then List.fold_left (update_map com) map lst
      else
        (* Otherwise, it's probably a regular assert. Unhide it when we unhide
           the primary variable *)
        match get_assert_var com with
        | Some s1 when not (BatString.starts_with s1 "symbolic-") ->
          update_map com map s1
        | _ ->
          (* This is a require clause which involves a non-symbolic variable.
             This can be caused by defining a new variable inside the require. *)
          (* Not entirely sure this is the best thing to do, but I think it
             should at least be conservative *)
          List.fold_left (update_map com) map lst
  in
  List.fold_left
    add_com
    default_map
    env.ctx
;;

(*
  This data structure represents the current state of a partially hidden network.
  For each variable:
  The bools represent whether that variable is currently hidden:
    The first is true if it has been declared; the second is true if its constraint(s)
    have been added. The second implies the first.
  The command list is the constraint(s) for that variable
  The constant is the declaration of that variable
*)
type hiding_map = (bool (* is_declared *) * bool (* is_visible *) * command list * constant) StringMap.t

(* For debugging *)
let hiding_map_to_string hm : string =
  let com_to_str com =
    match com.com with
    | Assert tm ->
      smt_term_to_smt tm.t
    | _ -> failwith "hiding_map_to_string failure"
  in
  StringMap.fold
    (fun _var (b1, b2, coms, decl) acc ->
       let str =
         Printf.sprintf "(%b, %b, [%s], %s)" b1 b2
           (BatString.concat ", " @@ List.map com_to_str coms)
           (decl.cname)
       in
       acc ^ str ^ "\n"
    )
    hm
    ""
;;

let declare_variable hiding_map var : hiding_map * ConstantSet.t =
  let declared, hidden, coms, decl = StringMap.find var hiding_map in
  if declared then
    hiding_map, ConstantSet.empty
  else
    StringMap.update var var (true, hidden, coms, decl) hiding_map,
    ConstantSet.singleton decl
;;

(* Given an env with some variables hidden, unhide the input variable
   var and all intermediate variables it depends on. *)
let rec unhide_variable hiding_map var : hiding_map * command list * ConstantSet.t =
  let declared, visible, coms, decl = StringMap.find var hiding_map in
  if visible then
    hiding_map, [], ConstantSet.empty
  else
    let new_map = StringMap.update var var (true, true, coms, decl) hiding_map in
    let new_decls =
      if declared then ConstantSet.empty else ConstantSet.singleton decl
    in

    (* TODO: Right now, this could potentially unhide lots of symbolics if we
       have big commands that involve lots of them, e.g. capping the number of
       failures. It would be nice to be cleverer. *)
    let additional_vars = List.concat @@ List.map get_vars_in_command coms in
    (* Never recursively unhide a label var: we only unhide these when they appear
       directly in an unsat core *)
    let label_vars, intermediate_vars =
      List.partition (fun s -> BatString.starts_with s "label-") additional_vars
    in
    (* Declare, but do not unhide, the label vars *)
    let new_map, new_decls =
      List.fold_left
        (fun (hm, decls) v ->
           let hm', decls' = declare_variable hm v in
           hm', ConstantSet.union decls decls')
        (new_map, new_decls)
        label_vars
    in
    (* Unhide (and implicitly declare if necessary) all other variable *)
    (* We could make this tail-recursive if we're having problems with the stack,
       or if we want it to be a little more efficient. *)
    List.fold_left
      (fun (hs, coms, consts) var ->
         let hs', coms', consts' = unhide_variable hs var in
         hs', coms @ coms', ConstantSet.union consts consts'
      )
      (new_map, coms, new_decls)
      intermediate_vars
;;

let unhide_variables hiding_map vars : hiding_map * command list * ConstantSet.t =
  List.fold_left
    (fun (hs, coms, decls) var ->
       let hs', coms', decls' = unhide_variable hs var in
       (hs', coms' @ coms, ConstantSet.union decls decls')
    )
    (hiding_map, [], ConstantSet.empty)
    vars
;;

(*
  Hide all variables except those which are involved in the assertion. Return
  * A starting Z3 program
  * A hiding map
  * The number of hidden variables
*)
let construct_starting_env (full_env : smt_env) : smt_env * hiding_map =
  (** Create our hiding_map, with every variable hidden **)
  let com_map = map_vars_to_commands full_env in
  let hidden_map =
    ConstantSet.fold
      (fun const map ->
         let com = StringMap.find const.cname com_map in
         StringMap.add const.cname (false, false, com, const) map)
      full_env.const_decls
      StringMap.empty
  in

  (** Search our constraints to find the one which corresponds to the final assertion **)
  let must_keep com =
    match com.com with
    | Assert tm ->
      begin
        match tm.t with
        | Not (And (_, (Eq (Var s1, Bool true)))) -> BatString.starts_with s1 "assert-"
        | _ -> false
      end
    (* I don't think we'll have any other commands besides asserts, so if we do
       they're probably important, and so should probably not be hidden. *)
    | _ -> true
  in
  let active_coms, _hidden_coms = BatList.partition must_keep full_env.ctx in

  (*** Step 2: Unhide all the variables which appear in the remaining commands.
       This will probably mean unhiding all the assert-result variables. ***)
  let active_vars = List.concat @@ List.map get_vars_in_command active_coms in
  let hidden_map, additional_coms, const_decls =
    unhide_variables hidden_map active_vars
  in

  let type_decls = full_env.type_decls in
  let symbolics = full_env.symbolics in

  {ctx= (active_coms @ additional_coms); const_decls; type_decls; symbolics},
  hidden_map
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

   (*
   Actually making queries strategy:
   Fire up two (2!) instances of Z3
   Give the first our partially hidden program; don't ask to check sat yet
   Give the second the full program, with assertion names and unsat core setting
   While hidden variables remain:
    Ask the first instance to solve the program.
    If it gets UNSAT, return "verified"
    If it gets SAT, query & parse the model
    In the second instance:
      Push a new frame onto its stack
      Give it the constraints from the model (don't need names here)
      Check if it's SAT
    If so, real counterexample: return the abstract model
    Else, false counterexample: query & parse the unsat core
    Unhide all variables that appear in the unsat core
 *)

(* Gets a different kind of model than the code in Smt.ml: here, we want values
   for each _SMT_ variable, rather than for the corresponding NV variables *)
let get_model verbose info _query _chan solver =
  let q =
    Printf.sprintf "%s\n" (GetModel |> mk_command |> command_to_smt verbose info)
  in
  (* if query then
     printQuery chan q; *)
  ask_solver_blocking solver q;
  let raw_model = get_reply_until ")" solver in
  let line_regex = Str.regexp "(define-fun \\([^ ]+\\) () [a-zA-z]+" in
  let rec process_raw_model lst acc =
    match lst with
    | []
    | _::[] -> acc
    | s1::s2::tl ->
      let varname =
        ignore @@ Str.search_forward line_regex s1 0;
        Str.matched_group 1 s1
      in
      let varval = BatString.chop ~l:1 s2 in
      process_raw_model tl @@ StringMap.add varname varval acc
  in
  process_raw_model (List.tl raw_model) StringMap.empty
;;

let make_constraints_from_model model =
  StringMap.fold
    (* The format here is hardcoded to avoid abusing the SmtLang interface *)
    (fun var value acc ->
       (* Don't need names on these assertions *)
       let con =
         Printf.sprintf "(assert (= %s %s))" var value
       in
       con :: acc
    )
    model []
;;

(* Query and parse the unsat core, and determine all variables which appear
   in it.
   Our naming scheme (see SmtLang.ml) tells us that every assertion is named
   with the variables that appear in it, plus a prefix to ensure uniqueness.
   So we can do simply string processing to retreive the set of variables
   which appear in the core *)
let get_variables_to_unhide query chan solver =
  let print_and_ask solver q =
    if query then
      printQuery chan q;
    ask_solver solver q
  in
  (* TODO: Z3 doesn't minimize cores by default; we may want it to do so *)
  print_and_ask solver "(get-unsat-core)\n";
  let raw_core = Nv_utils.OCamlUtils.oget @@ get_reply solver in
  (* Chop off leading and trailing parens *)
  let chopped_core = BatString.chop ~l:1 ~r:1 raw_core in
  let assertion_names = String.split_on_char ' ' chopped_core in
  let prefix = Str.regexp "constraint-[0-9]+\\$" in
  List.concat @@
  List.map
    (fun s ->
       let chopped = Str.replace_first prefix "" s in
       String.split_on_char '$' chopped
    )
    assertion_names
;;

let rec refineModel info verbose query partial_chan full_chan ask_for_nv_model partial_solver full_solver hiding_map =
  let print_and_ask solver chan q =
    if query then
      printQuery chan q;
    ask_solver_blocking solver q
  in
  let print_and_ask_partial = print_and_ask partial_solver partial_chan in
  let print_and_ask_full = print_and_ask full_solver full_chan in
  (* Check to see if the partially hidden program is SAT. If not, we're done; if
     so, its model gives us a potential counterexample that we need to check *)
  print_and_ask_partial (check_sat info);
  let reply = partial_solver |> parse_reply in
  match reply with
  | SAT ->
    begin
      (* Get a model, and add that model to the full encoding as constraints *)
      let model = get_model verbose info query partial_chan partial_solver in
      let constraints = make_constraints_from_model model in
      let constraints_from_model =
        List.fold_left (fun s1 s2 -> s1 ^ s2 ^ "\n") "(push)\n" constraints
      in
      print_and_ask_full constraints_from_model;
      (* See if the full network is SAT with the new constraints. If so,
         we have an actual counterexample; otherwise, the counterexample was
         spurious, so we refine our partial program by unhiding variables *)
      print_and_ask_full (check_sat info);
      let reply = full_solver |> parse_reply in
      match reply with
      | SAT ->
        (* Real counterexample: Ask for NV model *)
        ask_for_nv_model full_solver
      | UNSAT ->
        (* Spurious counterexample: Get unsat core and unhide the variables
           which appear in it *)
        let vars_to_unhide =
          get_variables_to_unhide query full_chan full_solver
        in
        (* Pop the constraints we added to the full program *)
        print_and_ask_full "(pop)\n";
        (* Unhide the variables, and get back the new commands and declarations
           that we need to add to the partial program *)
        let hiding_map, coms_to_add, decls_to_add =
          unhide_variables hiding_map vars_to_unhide
        in
        (* Convert the constant declarations into a string *)
        let constants =
          BatString.concat "\n" @@
          BatList.map (fun c -> const_decl_to_smt ~verbose:verbose info c)
            (ConstantSet.to_list decls_to_add)
        in
        (* Convert the commands into a string *)
        let commands =
          BatString.concat "\n" @@
          BatList.rev_map
            (fun c ->  smt_command_to_smt info c.com)
            coms_to_add
        in
        let unhidden_variables = Printf.sprintf "%s\n%s\n" constants commands in
        print_and_ask_partial unhidden_variables;
        (* Recurse: Check if the partial program is still SAT with the newly
           unhidden variables, and continue *)
        refineModel info verbose query partial_chan full_chan ask_for_nv_model partial_solver full_solver hiding_map
      | UNKNOWN -> Unknown
      | _ -> failwith "refineModel: Unexpected answer from solver"
    end
  | UNSAT -> Unsat
  | UNKNOWN -> Unknown
  | _ -> failwith "refineModel: Unexpected answer from solver"
;;

let partial_solver = lazy(let solver = start_solver [] in
                          ask_solver solver "(set-option :model_evaluator.completion true)";
                          solver)

let full_solver = lazy(let solver = start_solver [] in
                       ask_solver solver @@ "(set-option :model_evaluator.completion true)\n" ^
                                            "(set-option :produce-unsat-cores true)\n";
                       solver)

let solve_hiding info query partial_chan ~full_chan ?(starting_vars=[]) net =
  let partial_solver = Lazy.force partial_solver in
  let full_solver = Lazy.force full_solver in
  let print_and_ask solver chan q =
    if query then
      printQuery chan q;
    ask_solver_blocking solver q
  in
  let print_and_ask_partial = print_and_ask partial_solver partial_chan in
  let print_and_ask_full = print_and_ask full_solver full_chan in
  ignore starting_vars;
  (* We need two solver processes: one for the partially hidden program, and
     one for the full program with additional constraints *)
  let solve_aux () =
    let module ExprEnc = (val expr_encoding smt_config) in
    let module Enc =
      (val (module SmtClassicEncoding.ClassicEncoding(ExprEnc) : SmtClassicEncoding.ClassicEncodingSig))
      (*ignoring FuncEnc for now*)
    in
    (* compute the encoding of the network *)
    let renaming, full_env =
      time_profile "Encoding network"
        (fun () -> let env = Enc.encode_z3 net in
          propagate_eqs_for_hiding env)
    in
    let partial_env, hiding_map = construct_starting_env full_env in
    (* TODO: add starting_vars once I figure that out *)
    (* compile the encoding to SMT-LIB *)
    let full_encoding =
      time_profile "Compiling full query"
        (fun () -> env_to_smt ~verbose:smt_config.verbose ~name_asserts:true info full_env) in
    let partial_encoding =
      time_profile "Compiling partial query"
        (fun () -> env_to_smt ~verbose:smt_config.verbose ~name_asserts:false info partial_env) in

    print_and_ask_partial partial_encoding;
    print_and_ask_full full_encoding;

    let nodes = Nv_datastructures.AdjGraph.num_vertices net.graph in
    let ask_for_nv_model solver =
      ask_for_model query partial_chan info full_env solver renaming nodes net.assertion
    in
    time_profile_absolute "Solving with hiding"
      (fun () ->
         refineModel info smt_config.verbose query partial_chan full_chan ask_for_nv_model partial_solver full_solver hiding_map
      )
  in
  print_and_ask_partial "(push)";
  print_and_ask_full "(push)";
  let ret = solve_aux () in
  print_and_ask_partial "(pop)\n(pop)";
  print_and_ask_full "(pop)\n(pop)";
  ret
