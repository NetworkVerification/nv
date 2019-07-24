open Syntax
open OCamlUtils

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

  let rec simplify_tget size lo hi e =
    match e.e with
    | ETuple es ->
      if lo = hi then List.nth es lo
      else etuple (es |> BatList.drop lo |> BatList.take (hi - lo + 1))
    | EMatch (e1, branches) ->
      (* Push the TGet into the branches *)
      let new_branches =
        mapBranches (fun (p, body) -> p, simplify_tget size lo hi body) branches
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

  let simplify_tset size lo hi tup v =
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
    | TGet (size, lo, hi) ->
      begin
        match pes with
        | [e] -> simplify_tget size lo hi e
        | _ -> failwith "Bad TGet"
      end
    | TSet (size, lo, hi) ->
      begin
        match pes with
        | [e1; e2] -> simplify_tset size lo hi e1 e2
        | _ -> failwith "Bad TSet"
      end
    | _ -> eop op pes

  let simplify_match e =
    match e.e with
    | EMatch (_, branches) ->
      let blist = branchToList branches in
      (match blist with
       | [(_, e1); (_, e2)] when (is_value e1) && (is_value e2) ->
         if equal_exps ~cmp_meta:false e1 e2 then
           e1
         else
           e
       | _ -> e)
    | _ -> e

(** * Partial Interpreter *)

let isMapOp op =
  match op with
  | MCreate | MGet | MSet | MMap | MMerge | MFoldNode | MFoldEdge | MMapFilter -> true
  | _ -> false

let rec matchExpPat pat pe1 penv  =
  match pat, pe1.e with
  | PWild, _ -> Some penv
  | PVar x, EVar y ->
    Some (Env.update penv x y)
  | PTuple ps, ETuple es ->
    (match ps, es with
     | [], []-> Some penv
     | p :: ps, e :: es ->
       (match matchExpPat p e penv with
        | None -> None
        | Some env -> matchExpPat (PTuple ps) (etuple es) env)
     | _, _ -> None)
  | _, _ -> None (*for now *)

let rec matchExp branches pe1 penv =
  match popBranch branches with
  | ((pat,e), branches') ->
    if isEmptyBranch branches' then
      match matchExpPat pat pe1 penv with
      | None ->
        None
      | Some penv ->
        Some (penv, e)
    else
      None

(* This evaluates away some trivial match statements (e.g. renamings
   of variables) but it did not improve performance (it actually made it worse) *)
let rec interp_exp_partial_opt isapp env expEnv e =
  match e.e with
  | ETy (e, _) -> interp_exp_partial_opt isapp env expEnv e
  | EVar x -> (
      match Env.lookup_opt env.value x with
      | None ->
        (match Env.lookup_opt expEnv x with
         | None -> e
         | Some y ->
           aexp (evar y, e.ety, e.espan))
      | Some v ->
        aexp (e_val v, v.vty, v.vspan))
  | EVal v -> e
  | EOp (op, es) ->
    aexp (interp_op_partial_opt env expEnv (oget e.ety) op es, e.ety, e.espan)
  | EFun f ->
    (*Also note that we avoid using closures for our comfort, and
       since they are not needed for inlined functions *)
    (* if isapp then *)
    (*   exp_of_value (vclosure (env, f)) *)
    (* else *)
    (*   exp_of_value (vclosure (env, {f with body = interp_exp_partial_opt false env f.body})) *)
    if isapp then
      e
    else
      aexp (efun {f with body = interp_exp_partial_opt false env expEnv f.body}, e.ety, e.espan)
  | EApp (e1, e2) ->
    let pe1 = interp_exp_partial_opt true env expEnv e1 in
    let pe2 = interp_exp_partial_opt false env expEnv e2 in
    (match pe1.e with
     | EFun f when is_value pe2 ->
       interp_exp_partial_opt false (update_value env f.arg (to_value pe2)) expEnv f.body
     | _ -> aexp (eapp pe1 pe2, e.ety, e.espan))
  | EIf (e1, e2, e3) ->
    let pe1 = interp_exp_partial_opt false env expEnv e1 in
    if is_value pe1 then
      (match (to_value pe1).v with
       | VBool true  -> interp_exp_partial_opt false env expEnv e2
       | VBool false -> interp_exp_partial_opt false env expEnv e3
       | _ -> failwith "bad if condition")
    else
      aexp (eif pe1
              (interp_exp_partial_opt false env expEnv e2)
              (interp_exp_partial_opt false env expEnv e3),
            e.ety, e.espan)
  | ELet (x, e1, e2) ->
    let pe1 = interp_exp_partial_opt false env expEnv e1 in
    if is_value pe1 then
      interp_exp_partial_opt false (update_value env x (to_value pe1)) expEnv e2
    else
      aexp (elet x pe1 (interp_exp_partial_opt false env expEnv e2),
            e.ety, e.espan)
  | ETuple es ->
    aexp (etuple (BatList.map (interp_exp_partial_opt false env expEnv) es),
          e.ety, e.espan)
  | ESome e' -> aexp (esome (interp_exp_partial_opt false env expEnv e'), e.ety, e.espan)
  | EMatch (e1, branches) ->
    (* Printf.printf "match: %s\n" (Printing.exp_to_string e); *)
    let pe1 = interp_exp_partial_opt false env expEnv e1 in
    if is_value pe1 then
      (match InterpUtils.match_branches branches (to_value pe1) env.value with
       | Some (env2, e) -> interp_exp_partial_opt false {env with value=env2} expEnv e
       | None ->
         failwith
           ( "value " ^ Printing.value_to_string (to_value pe1)
             ^ " did not match any pattern in match statement"))
    else
      (
        (* Printf.printf "fancy match failed: %s\n" (Printing.exp_to_string e); *)
        match matchExp branches pe1 expEnv with
        | None ->
          aexp (ematch pe1 (mapBranches (fun (p,e) ->
              (p, interp_exp_partial_opt false env expEnv e)) branches),
                e.ety, e.espan) (* |> simplify_match *)
        | Some (penv, e) -> interp_exp_partial_opt false env penv e)
  | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

and interp_op_partial_opt env expEnv ty op es =
  let pes = BatList.map (interp_exp_partial_opt false env expEnv) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes then
    simplify_exps op pes
  else
  if isMapOp op then
    eop op pes
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
      | TGet (size, lo, hi), [{v= VTuple lst}] ->
        assert (List.length lst = size) ; (* Sanity check *)
        if lo = hi then List.nth lst lo
        else vtuple (lst |> BatList.drop lo |> BatList.take (hi - lo + 1))
      | TSet (size, lo, hi), [{v= VTuple lst}; v] ->
        assert (List.length lst = size) ; (* Sanity check *)
        if lo = hi then
          vtuple @@ BatList.modify_at lo (fun _ -> v) lst
        else
          let hd, rest = BatList.takedrop lo lst in
          let _, tl = BatList.takedrop (hi - lo + 1) rest in
          begin
            match v.v with
            | VTuple mid ->
              vtuple (hd @ mid @ tl)
            | _ -> failwith ""
          end
      | _, _ ->
        failwith
          (Printf.sprintf "bad operator application: %s"
             (Printing.op_to_string op))
    end

let rec interp_exp_partial isapp env e =
  match e.e with
  | ETy (e, _) -> interp_exp_partial isapp env e
  | EVar x -> (
      match Env.lookup_opt env.value x with
      | None ->
        e
      | Some v ->
        aexp (e_val v, v.vty, v.vspan))
  | EVal v -> e
  | EOp (op, es) ->
    aexp (interp_op_partial env (oget e.ety) op es, e.ety, e.espan)
  | EFun f ->
    (*Also note that we avoid using closures for our comfort, and
       since they are not needed for inlined functions *)
    if isapp then
      e
    else
      aexp (efun {f with body = interp_exp_partial false env f.body}, e.ety, e.espan)
  | EApp (e1, e2) ->
    let pe1 = interp_exp_partial true env e1 in
    let pe2 = interp_exp_partial false env e2 in
    (match pe1.e with
     | EFun f when is_value pe2 ->
       interp_exp_partial false (update_value env f.arg (to_value pe2)) f.body
     | _ -> aexp (eapp pe1 pe2, e.ety, e.espan))
  | EIf (e1, e2, e3) ->
    let pe1 = interp_exp_partial false env e1 in
    if is_value pe1 then
      (match (to_value pe1).v with
       | VBool true  -> interp_exp_partial false env e2
       | VBool false -> interp_exp_partial false env e3
       | _ -> failwith "bad if condition")
    else
      aexp (eif pe1
              (interp_exp_partial false env e2)
              (interp_exp_partial false env e3),
            e.ety, e.espan)
  | ELet (x, e1, e2) ->
    let pe1 = interp_exp_partial false env e1 in
    if is_value pe1 then
      interp_exp_partial false (update_value env x (to_value pe1)) e2
    else
      aexp (elet x pe1 (interp_exp_partial false env e2),
            e.ety, e.espan)
  | ETuple es ->
    aexp (etuple (BatList.map (interp_exp_partial false env) es),
          e.ety, e.espan)
  | ESome e' -> aexp (esome (interp_exp_partial false env e'), e.ety, e.espan)
  | EMatch (e1, branches) ->
    (* Printf.printf "match: %s\n" (Printing.exp_to_string e); *)
    let pe1 = interp_exp_partial false env e1 in
    if is_value pe1 then
      (match InterpUtils.match_branches branches (to_value pe1) env.value with
       | Some (env2, e) ->      (* Printf.printf "some: %s\n" (Printing.exp_to_string e); *)
         interp_exp_partial false {env with value=env2} e
       | None ->
         failwith
           ( "value " ^ Printing.value_to_string (to_value pe1)
             ^ " did not match any pattern in match statement"))
    else
      aexp (ematch pe1 (mapBranches (fun (p,e) ->
          (p, interp_exp_partial false env e)) branches),
            e.ety, e.espan) (* |> simplify_match *)

  | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

and interp_op_partial env ty op es =
  let pes = BatList.map (interp_exp_partial false env) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes then
    simplify_exps op pes
  else
  if isMapOp op then
    eop op pes
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
      | TGet (size, lo, hi), [{v= VTuple lst}] ->
        assert (List.length lst = size) ; (* Sanity check *)
        if lo = hi then List.nth lst lo
        else vtuple (lst |> BatList.drop lo |> BatList.take (hi - lo + 1))
      | TSet (size, lo, hi), [{v= VTuple lst}; v] ->
        assert (List.length lst = size) ; (* Sanity check *)
        if lo = hi then
          vtuple @@ BatList.modify_at lo (fun _ -> v) lst
        else
          let hd, rest = BatList.takedrop lo lst in
          let _, tl = BatList.takedrop (hi - lo + 1) rest in
          begin
            match v.v with
            | VTuple mid ->
              vtuple (hd @ mid @ tl)
            | _ -> failwith ""
          end
      | _, _ ->
        failwith
          (Printf.sprintf "bad operator application: %s"
             (Printing.op_to_string op))
    end

let interp_partial = fun e -> interp_exp_partial false empty_env e
let interp_partial_opt =
  fun e -> interp_exp_partial_opt false empty_env Env.empty e

(* let interp_partial_closure cl (args: value list) = *)
(*   interp_partial (Syntax.apply_closure cl args) *)

let interp_partial = Memoization.MemoizeExp.memoize ~size:1000 interp_partial
(* let interp_partial_opt = MemoizeExp.memoize ~size:1000 interp_partial_opt *)

let interp_partial_fun (fn : Syntax.exp) (args: value list) =
  Syntax.apps fn (List.map (fun a -> e_val a) args) |>
  interp_partial
