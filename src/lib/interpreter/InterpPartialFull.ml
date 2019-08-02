open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_lang.Collections
open Nv_utils.OCamlUtils
open InterpUtils
open Interp

(* This ludicrously named file contains a Full reduction partial interpreter.
   Not sure how it differs from the regular one. *)


(** * Simplifications *)
let simplify_and v1 e2 =
  match v1.v with
  | VBool true -> e2
  | VBool false -> exp_of_value (vbool false)
  | _ -> failwith "illegal value to boolean"

let simplify_or v1 e2 =
  match v1.v with
  | VBool true -> exp_of_value (vbool true)
  | VBool false -> e2
  | _ -> failwith "illegal value to boolean"

let rec simplify_tget lo hi e =
  match e.e with
  | ETuple es ->
    if lo = hi then List.nth es lo
    else etuple (es |> BatList.drop lo |> BatList.take (hi - lo + 1))
  | EMatch (e1, branches) ->
    (* Push the TGet into the branches *)
    let new_branches =
      mapBranches (fun (p, body) -> p, simplify_tget lo hi body) branches
    in
    ematch e1 new_branches
  | _ ->
    (* If all else fails, write a match statement *)
    let tys = match e.ety with | Some (TTuple lst) -> lst | _ -> failwith "impossible" in
    let get_ty =
      if lo = hi then List.nth tys lo
      else TTuple (tys |> BatList.drop lo |> BatList.take (hi - lo + 1))
    in

    let freshvars = List.map (fun ty -> ty, Var.fresh "TGetVar") tys in
    let pat =
      PTuple (
        List.mapi
          (fun i (_, v) -> if lo <= i && i <= hi then PVar v else PWild)
          freshvars)
    in

    let get_exps =
      freshvars
      |> BatList.drop lo |> BatList.take (hi - lo + 1)
      |> List.map (fun (ty, v) -> aexp (evar v, Some ty, e.espan))
    in
    let branch_body =
      if lo = hi then List.hd get_exps
      else aexp (etuple get_exps, Some get_ty, e.espan)
    in

    ematch e (addBranch pat branch_body emptyBranch)
;;

let simplify_tset lo hi tup v =
  (* If the expression is an actual tuple expression, we don't need a match
     to unpack its elements. This function computes an expression list corresponding
     the elements of exp (using a match only if needed) and calls cont on it. *)
  let curry_elts exp (cont : exp list -> exp) =
    match exp.e with
    | ETuple es -> cont es
    | _ ->
      match oget exp.ety with
      | TTuple tys ->
        let freshvars = List.map (fun ty -> ty, Var.fresh "TSetVar") tys in
        let freshvarexps = List.map (fun (ty, v) -> aexp (evar v, Some ty, exp.espan)) freshvars in
        let pat = PTuple (List.map (fun (_, v) -> PVar v) freshvars) in
        ematch exp (addBranch pat (cont freshvarexps) emptyBranch)
      | _ -> failwith "Bad TSet"
  in
  let cont tup_es v_es =
    let hd, tl =
      let hd, rest = BatList.takedrop lo tup_es in
      hd, BatList.drop (hi - lo + 1) rest
    in
    etuple (hd @ v_es @ tl) |> wrap tup
  in
  curry_elts tup
    (fun tup_es ->
       if lo = hi then cont tup_es [v]
       else curry_elts v (cont tup_es))

let simplify_exps op pes =
  match op with
  | And ->
    begin
      match pes with
      | [e1; e2] when (is_value e1) ->
        simplify_and (to_value e1) e2
      | [e1; e2] when (is_value e2) ->
        simplify_and (to_value e2) e1
      | _ -> eop op pes
    end
  | Or ->
    begin
      match pes with
      | [e1; e2] when (is_value e1) ->
        simplify_or (to_value e1) e2
      | [e1; e2] when (is_value e2) ->
        simplify_or (to_value e2) e1
      | [e1; e2] when (equal_exps ~cmp_meta:false e1 e2) ->
        e1
      | [e1; e2] ->
        (match e1.e with
         | EOp (Not, [e1']) when equal_exps ~cmp_meta:false e1' e2 ->
           exp_of_value (vbool true)
         | _ ->
           (match e2.e with
            | EOp (Not, [e2']) when equal_exps ~cmp_meta:false e1 e2' ->
              exp_of_value (vbool true)
            | _ -> eop op pes))
      | _ -> eop op pes
    end
  | TGet (_, lo, hi) ->
    begin
      match pes with
      | [e] -> simplify_tget lo hi e
      | _ -> failwith "Bad TGet"
    end
  | TSet (_, lo, hi) ->
    begin
      match pes with
      | [e1; e2] -> simplify_tset lo hi e1 e2
      | _ -> failwith "Bad TSet"
    end
  | _ -> eop op pes

type 'a isMatch =
    Match of 'a
  | NoMatch
  | Delayed

(* matches p b is Some env if v matches p and None otherwise; assumes no repeated variables in pattern *)
let rec matches p (e: Syntax.exp) : Syntax.exp Env.t isMatch =
  match p with
  | PWild -> Match Env.empty
  | PUnit -> Match Env.empty
  | PVar x -> Match (Env.bind x e)
  | PBool true ->
    if is_value e then
      match (to_value e).v with
      | VBool true -> Match Env.empty
      | _ -> NoMatch
    else
      Delayed
  | PBool false ->
    if is_value e then
      match (to_value e).v with
      | VBool false -> Match Env.empty
      | _ -> NoMatch
    else
      Delayed
  | PInt i1 ->
    if is_value e then
      match (to_value e).v with
      | VInt i2 ->
        if Integer.equal i1 i2 then Match Env.empty else NoMatch
      | _ -> NoMatch
    else
      Delayed
  | PNode n1 ->
    if is_value e then
      match (to_value e).v with
      | VNode n2 ->
        if n1 = n2 then Match Env.empty else NoMatch
      | _ -> NoMatch
    else
      Delayed
  | PEdge (p1, p2) ->
    if is_value e then
      match (to_value e).v with
      | VEdge (n1, n2) ->
        matches_list [p1; p2] [e_val (vnode n1); e_val (vnode n2)] Env.empty
      | _ -> NoMatch
    else
      Delayed
  | PTuple ps ->
    (* only match tuples when all components match *)
    if is_value e then
      (match e.e with
       | ETuple es ->
         matches_list ps es Env.empty
       | EVal v ->
         (match v.v with
          | VTuple vs ->
            matches_list ps (BatList.map exp_of_value vs) Env.empty
          | _ -> NoMatch)
       | _ -> NoMatch)
    else Delayed
  | POption None ->
    if is_value e then
      match (to_value e).v with
      | VOption None ->
        Match Env.empty
      | _ -> NoMatch
    else
      Delayed
  | POption (Some p) ->
    (match e.e with
     | ESome e1 ->
       matches p e1
     | _ when is_value e ->
       (match (to_value e).v with
        | VOption (Some v) ->
          matches p (exp_of_value v)
        | _ -> NoMatch)
     | _ -> Delayed)
  | PRecord _ -> failwith "Record found during partial interpretation"


and matches_list ps es env =
  match (ps, es) with
  | [], [] -> Match env
  | p :: ps, e :: es -> (
      match matches p e with
      | NoMatch -> NoMatch
      | Delayed -> Delayed
      | Match env1 ->
        matches_list ps es (Env.updates env env1))
  | _, _ -> NoMatch

let rec match_branches_lst branches v =
  match branches with
  | [] -> NoMatch
  | (p, e) :: branches ->
    match matches p v with
    | Match env -> Match (env, e)
    | NoMatch -> match_branches_lst branches v
    | Delayed -> Delayed

let rec matchExpPat pat pe1 env =
  match pat, pe1.e with
  | PWild, _ -> Match env
  | PUnit, _ -> Match env
  | PVar x, _ ->
    Match (Env.update env x pe1)
  | PTuple ps, ETuple es ->
    (match ps, es with
     | [], []-> Match env
     | p :: ps, e :: es ->
       (match matchExpPat p e env with
        | Delayed -> Delayed
        | Match env -> matchExpPat (PTuple ps) (etuple es) env
        | NoMatch -> failwith "No match?")
     | _, _ -> Delayed)
  | _, _ -> Delayed (*for now *)

let rec matchExp branches pe1 =
  match popBranch branches with
  | ((pat,e), branches') ->
    if isEmptyBranch branches' then
      match matchExpPat pat pe1 Env.empty with
      | Delayed -> Delayed
      | Match env -> Match (env, e)
      | NoMatch -> failwith "No match?"
    else
      Delayed (* I guess this means we only try to match supposedly-irrefutable patterns *)

let rec match_branches branches v =
  if is_value v then
    ((* Printf.printf "v:%s" (Printing.exp_to_string v);
      * iterBranches (fun (p,e) -> Printf.printf "pat:%s\n" (Printing.pattern_to_string p)) branches; *)
      match lookUpPat (val_to_pat (to_value v)) branches with
      | Found e -> Match (Env.empty, e)
      | Rest ls -> match_branches_lst ls v)
  else
    matchExp branches v



(** Assumes that inlining has been performed.  Not CBN in the
    strict sense. It will just do function applications over
    expressions, not just values.*)
let rec interp_exp_partial (env: Syntax.exp Env.t) e =
  match e.e with
  | ETy (e, _) -> interp_exp_partial env e
  | EVar x -> (
      match Env.lookup_opt env x with
      | None ->
        (env, e)
      | Some e1 ->
        (env, e1))
  | EVal _ -> (env, e)
  | EOp (op, es) ->
    (env, aexp (interp_op_partial env (oget e.ety) op es, e.ety, e.espan))
  | EFun _ -> (env, e)
  (* either need to do the partial interpretation here, or return a pair
     of the efun and the env at this point to be used, sort of like a closure.*)
  | EApp (e1, e2) ->
    let (cenv, pe1) = interp_exp_partial env e1 in
    let _, pe2 = interp_exp_partial env e2 in
    (match pe1.e with
     | EFun f ->
       interp_exp_partial (Env.update cenv f.arg pe2) f.body
     | _ ->
       (*this case shouldn't show up for us *)
       failwith "This case shouldn't show up")
  | EIf (e1, e2, e3) ->
    let _, pe1 = interp_exp_partial env e1 in
    if is_value pe1 then
      (match (to_value pe1).v with
       | VBool true  -> interp_exp_partial env e2
       | VBool false -> interp_exp_partial env e3
       | _ -> failwith "bad if condition")
    else
      (env, aexp (eif pe1 (snd (interp_exp_partial env e2)) (snd (interp_exp_partial env e3)),
                  e.ety, e.espan))
  | ELet (x, e1, e2) ->
    let _, pe1 = interp_exp_partial env e1 in
    (* if is_value pe1 then *)
    interp_exp_partial (Env.update env x pe1) e2
  (* else
   *   (env, aexp(elet x pe1 (snd (interp_exp_partial env e2)), Some (oget e.ety), e.espan)) *)
  | ETuple es ->
    (env, aexp (etuple (BatList.map (fun e -> snd (interp_exp_partial env e)) es),
                e.ety, e.espan))
  | ESome e' -> (env, aexp (esome (snd (interp_exp_partial env e')), e.ety, e.espan))
  | EMatch (e1, branches) ->
    let _, pe1 = interp_exp_partial env e1 in
    begin
      match match_branches branches pe1 with
      | Match (env2, e) -> interp_exp_partial (Env.updates env env2) e
      | NoMatch ->
        failwith
          ( "exp " ^ (Printing.exp_to_string pe1)
            ^ " did not match any pattern in match statement")
      | Delayed ->
        let pat = popBranch branches |> fst |> fst in
        (* If our pattern is irrefutable, then we probably have something of the
           form "match (match e with <branches1>) with <branches2>", and we weren't
           able to fully evaluate the inner match. In this case we can reverse
           the order of the matches to hopefully allow further simplification.
           This duplicates the contents of <branches2> (once for each element of
           <branches1>), but it will _usually_ give us a significant code decrease.
           TODO: It would be nice to have a heuristic for determining when this
           match permutation is likely to actually be helpful. *)
        match is_irrefutable pat, pe1.e with
        | true, EMatch (e2, branches2) ->
          let permuted_match =
            ematch e2
              (mapBranches
                 (fun (p,inner_branch) ->
                    (p,
                     ematch inner_branch branches |> wrap e))
                 branches2)
            |> wrap e
          in
          interp_exp_partial env permuted_match
        | _ ->
          (* Permutation won't help us, just recurse the branches *)
          (env,
           ematch pe1 (mapBranches (fun (p,e) ->
               (p, snd (interp_exp_partial env e))) branches)
           |> wrap e)
    end
  | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

(* this is same as above, minus the app boolean. see again if we can get rid of that? *)
and interp_op_partial env ty op es =
  let pes = BatList.map (fun e -> snd (interp_exp_partial env e)) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes then
    simplify_exps op pes
  else
    begin
      exp_of_value @@
      match (op, BatList.map to_value pes) with
      | And, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 && b2)
      | Or, [{v= VBool b1}; {v= VBool b2}] -> vbool (b1 || b2)
      | Not, [{v= VBool b1}] -> vbool (not b1)
      | UAdd _, [{v= VInt i1}; {v= VInt i2}] ->
        vint (Integer.add i1 i2)
      | Eq, [v1; v2] ->
        if equal_values ~cmp_meta:false v1 v2 then vbool true
        else vbool false
      | ULess _, [{v= VInt i1}; {v= VInt i2}] ->
        if Integer.lt i1 i2 then vbool true else vbool false
      | ULeq _, [{v= VInt i1}; {v= VInt i2}] ->
        if Integer.leq i1 i2 then vbool true else vbool false
      | NLess, [{v= VNode n1}; {v= VNode n2}] ->
        if n1 < n2 then vbool true else vbool false
      | NLeq, [{v= VNode n1}; {v= VNode n2}] ->
        if n1 <= n2 then vbool true else vbool false
      | TGet (size, lo, hi), [{v= VTuple elts}] ->
        assert (List.length elts = size) ; (* Sanity check *)
        if lo = hi then List.nth elts lo
        else vtuple (elts |> BatList.drop lo |> BatList.take (hi - lo + 1))
      | TSet (size, lo, hi), [{v= VTuple elts}; v] ->
        assert (List.length elts = size) ; (* Sanity check *)
        begin
          if lo = hi then
            vtuple (BatList.modify_at lo (fun _ -> v) elts)
          else
            match v.v with
            | VTuple velts ->
              let hd, rest = BatList.takedrop lo elts in
              let _, tl = BatList.takedrop (hi - lo + 1) rest in
              vtuple (hd @ velts @ tl)
            | _ -> failwith "Bad TSet"
        end
      | MCreate, [v] -> (
          match get_inner_type ty with
          | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
          | _ -> failwith "runtime error: missing map key type" )
      | MGet, [{v= VMap m}; v] -> BddMap.find m v
      | MSet, [{v= VMap m}; vkey; vval] ->
        vmap (BddMap.update m vkey vval)
      | MMap, [{v= VClosure (c_env, f)}; {v= VMap m}] ->
        let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
        let free = Syntax.free seen f.body in
        let env = build_env c_env free in
        vmap
          (BddMap.map ~op_key:(f.body, env)
             (fun v -> apply c_env f v)
             m)
      | MFoldNode, [{v= VClosure (c_env, f)}; acc; {v= VMap m}]
      | MFoldEdge, [{v= VClosure (c_env, f)}; acc; {v= VMap m}] ->
        let bindings, _ = BddMap.bindings m in
        let apply_f acc (k, v) =
          match apply c_env f k with
          | {v=VClosure (c_env', f')} ->
            begin
              match apply c_env' f' v with
              | {v=VClosure (c_env'', f'')} ->
                apply c_env'' f'' acc
              | _ -> failwith "internal error (interp_op_partial)"
            end
          | _ -> failwith "internal error (interp_op_partial)"
        in
        List.fold_left apply_f acc bindings
      | ( MMerge
        , {v= VClosure (c_env, f)}
          :: {v= VMap m1} :: {v= VMap m2} :: rest )
        -> (
            let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
            let env = build_env c_env (Syntax.free seen f.body) in
            (* TO DO:  Need to preserve types in VOptions here ? *)
            let f_lifted v1 v2 =
              match apply c_env f v1 with
              | {v= VClosure (c_env, f)} -> apply c_env f v2
              | _ -> failwith "internal error (interp_op)"
            in
            match rest with
            | [el0; el1; er0; er1] ->
              let opt = (el0, el1, er0, er1) in
              vmap
                (BddMap.merge ~opt ~op_key:(f.body, env) f_lifted m1 m2)
            | _ -> vmap (BddMap.merge ~op_key:(f.body, env) f_lifted m1 m2)
          )
      | ( MMapFilter
        , [ {v= VClosure (_, f1)}
          ; {v= VClosure (c_env2, f2)}
          ; {v= VMap m} ] ) ->
        let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
        let env = build_env c_env2 (Syntax.free seen f2.body) in
        let mtbdd =
          match ExpMap.Exceptionless.find f1.body !bddfunc_cache with
          | None -> (
              let bddf = BddFunc.create_value (Nv_utils.OCamlUtils.oget f1.argty) in
              let env = Env.update Env.empty f1.arg bddf in
              let bddf = BddFunc.eval env f1.body in
              match bddf with
              | BBool bdd ->
                let mtbdd = BddFunc.wrap_mtbdd bdd in
                bddfunc_cache :=
                  ExpMap.add f1.body mtbdd !bddfunc_cache ;
                mtbdd
              | _ -> failwith "impossible" )
          | Some bddf -> bddf
        in
        let f v = apply c_env2 f2 v in
        vmap (BddMap.map_when ~op_key:(f2.body, env) mtbdd f m)
      | _, _ ->
        failwith
          (Printf.sprintf "bad operator application: %s"
             (Printing.op_to_string op))
    end

let interp_partial = fun e -> snd (interp_exp_partial Env.empty e)

let interp_partial_fun (fn : Syntax.exp) (args: exp list) =
  let e = Syntax.apps fn args in
  interp_partial e
