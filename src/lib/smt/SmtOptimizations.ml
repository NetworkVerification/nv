open Nv_lang.Collections
open SmtLang
open SmtUtils

(** ** SMT query optimization *)
let rec alpha_rename_smt_term (renaming: string StringMap.t)
    (valMap: smt_term StringMap.t) (tm: smt_term) =
  match tm with
  | Int _ | Bool _ | Constructor _ -> tm
  | And (tm1, tm2) ->
    And (alpha_rename_smt_term renaming valMap tm1,
         alpha_rename_smt_term renaming valMap tm2)
  | Or (tm1, tm2) ->
    Or (alpha_rename_smt_term renaming valMap tm1,
        alpha_rename_smt_term renaming valMap tm2)
  | Not tm1 ->
    Not (alpha_rename_smt_term renaming valMap tm1)
  | Add (tm1, tm2) ->
    Add (alpha_rename_smt_term renaming valMap tm1,
         alpha_rename_smt_term renaming valMap tm2)
  | Sub (tm1, tm2) ->
    Sub (alpha_rename_smt_term renaming valMap tm1,
         alpha_rename_smt_term renaming valMap tm2)
  | Eq (tm1, tm2) ->
    Eq (alpha_rename_smt_term renaming valMap tm1,
        alpha_rename_smt_term renaming valMap tm2)
  | Lt (tm1, tm2) ->
    Lt (alpha_rename_smt_term renaming valMap tm1,
        alpha_rename_smt_term renaming valMap tm2)
  | Leq (tm1, tm2) ->
    Leq (alpha_rename_smt_term renaming valMap tm1,
         alpha_rename_smt_term renaming valMap tm2)
  | Ite (tm1, tm2, tm3) ->
    Ite (alpha_rename_smt_term renaming valMap tm1,
         alpha_rename_smt_term renaming valMap tm2,
         alpha_rename_smt_term renaming valMap tm3)
  | AtMost (tm1, tm2, tm3) ->
    AtMost (BatList.map (alpha_rename_smt_term renaming valMap) tm1,
            tm2,
            alpha_rename_smt_term renaming valMap tm3)
  | Var s ->
    let sr = match StringMap.Exceptionless.find s renaming with
      | None -> s
      | Some x -> x
    in
    (match StringMap.Exceptionless.find sr valMap with
     | None -> Var sr
     | Some tmv -> tmv)
  | Bv _ -> failwith "not yet"
  | App (tm1, tms) ->
    App (alpha_rename_smt_term renaming valMap tm1,
         BatList.map (alpha_rename_smt_term renaming valMap) tms)

let alpha_rename_term (renaming: string StringMap.t) valMap (tm: term) =
  {tm with t = alpha_rename_smt_term renaming valMap tm.t}

(** Removes all variable equalities *)
let propagate_eqs (env : smt_env) =
  let updateUnionFind eqSets s =
    try
      StringMap.find s eqSets, eqSets
    with Not_found ->
      let r = BatUref.uref s in
      r, StringMap.add s r eqSets
  in
  (* compute equality classes of variables and remove equalities between variables *)
  let (eqSets, valMap, new_ctx) = BatList.fold_left (fun (eqSets, valMap, acc) c ->
      match c.com with
      | Assert tm ->
        (match tm.t with
         | Eq (tm1, tm2) ->
           (match tm1, tm2 with
            | Var s1, Var s2 ->
              let r1, eqSets = updateUnionFind eqSets s1 in
              let r2, eqSets = updateUnionFind eqSets s2 in
              BatUref.unite r1 r2;
              (eqSets, valMap, acc)
            | Var s1, Int _ | Var s1, Bool _ ->
              let valMap = StringMap.add s1 tm2 valMap in
              (eqSets, valMap, acc)
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
  (renaming, newValMap), env
