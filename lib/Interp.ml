open Syntax
open Memoization
open Printing
open Printf

(* Interpreter Errors *)
(* Interpreter Environments *)

let empty_env = {ty= Env.empty; value= Env.empty}

let update_value env x v = {env with value= Env.update env.value x v}

let update_values env venv =
  {env with value= Env.updates env.value venv}

let update_ty env x t = {env with ty= Env.update env.ty x t}

let update_tys env tvs tys =
  let rec loop tenv tvs tys =
    match (tvs, tys) with
    | [], [] -> tenv
    | tv :: tvs, ty :: tys -> loop (Env.update tenv tv ty) tvs tys
    | _, _ -> failwith "wrong arity in type application"
  in
  {env with ty= loop env.ty tvs tys}

(* Equality of values *)
(* ignores type annotations when checking for equality *)
let [@warning "-8"] rec equal_val v1 v2 =
  match (v1.v, v2.v) with
  | VBool b1, VBool b2 -> b1 = b2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VMap m1, VMap m2 -> BddMap.equal m1 m2
  | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
  | VOption None, VOption None -> true
  | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
  | VRecord map1, VRecord map2 -> RecordUtils.StringMap.equal equal_val map1 map2
  | VNode n1, VNode n2 -> n1 = n2
  | VEdge e1, VEdge e2 -> e1 = e2
  | VClosure _, _ -> failwith "internal error (equal_val)"
  | _, VClosure _ -> failwith "internal error (equal_val)"
  | _, _ -> false

and equal_vals vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | v1 :: rest1, v2 :: rest2 ->
    equal_val v1 v2 && equal_vals rest1 rest2
  | _, _ -> false

(* Expression and operator interpreters *)
(* matches p b is Some env if v matches p and None otherwise; assumes
   no repeated variables in pattern *)
let rec matches p (v: Syntax.value) env : Syntax.value Env.t option =
  match (p, v.v) with
  | PWild, _ -> Some env
  | PVar x, _ -> Some (Env.update env x v)
  | PUnit, VUnit -> Some env
  | PBool true, VBool true
  | PBool false, VBool false -> Some env
  | PInt i1, VInt i2 ->
    if Integer.equal i1 i2 then Some env else None
  | PNode n1, VNode n2 ->
    if n1 = n2 then Some env else None
  | PEdge (p1, p2), VEdge (n1, n2) ->
    begin
      match matches p1 (vnode n1) env with
      | None -> None
      | Some env -> matches p2 (vnode n2) env
    end
  | PTuple ps, VTuple vs -> (* matches_list ps vs *)
    (match ps, vs with
     | [], []-> Some env
     | p :: ps, v :: vs ->
       (match matches p v env with
        | None -> None
        | Some env -> matches (PTuple ps) (vtuple vs) env)
     | _, _ -> None)
  | POption None, VOption None -> Some env
  | POption (Some p), VOption (Some v) -> matches p v env
  | (PUnit | PBool _ | PInt _ | PTuple _ | POption _ | PNode _ | PEdge _), _ -> None
  | PRecord _, _ -> failwith "Record found during interpretation"


let rec match_branches_lst branches v env =
  match branches with
  | [] -> None
  | (p, e) :: branches ->
    match matches p v env with
    | Some env' -> Some (env', e)
    | None -> match_branches_lst branches v env

let rec val_to_pat v =
  match v.v with
  | VInt i -> PInt i
  | VBool b -> PBool b
  | VOption (Some v) -> POption (Some (val_to_pat v))
  | VOption None -> POption None
  | VTuple vs ->
    PTuple (BatList.map val_to_pat vs)
  | VRecord map -> PRecord (RecordUtils.StringMap.map val_to_pat map)
  | VNode n -> PNode n
  | VEdge (n1, n2) -> PEdge (PNode n1, PNode n2)
  | VUnit -> PUnit
  | VMap _
  | VClosure _ -> PWild

let rec match_branches branches v env =
  (* iterBranches (fun (p,e) ->  Printf.printf "%s\n" (Printing.pattern_to_string p)) branches;
   * Printf.printf "val: %s\n" (Printing.value_to_string v); *)
  match lookUpPat (val_to_pat v) branches with
  | Found e -> Some (env, e)
  | Rest ls -> match_branches_lst ls v env

module ExpMap = Map.Make (struct
    type t = exp

    let compare = Pervasives.compare
  end)

let build_env (env: env) (free_vars: Var.t BatSet.PSet.t) :
  value BatSet.PSet.t =
  let base = BatSet.PSet.create compare_values in
  BatSet.PSet.fold
    (fun v acc ->
       match Env.lookup_opt env.value v with
       | Some value -> BatSet.PSet.add value acc
       | None -> acc )
    free_vars base

let bddfunc_cache = ref ExpMap.empty

let rec interp_exp env e =
  match e.e with
  | ETy (e, _) -> interp_exp env e
  | EVar x -> (
      match Env.lookup_opt env.value x with
      | None ->
        failwith
          (Printf.sprintf "runtime exception - unbound variable: %s"
             (Var.to_string x))
      | Some v -> v )
  | EVal v -> v
  | EOp (op, es) ->
    interp_op env (oget e.ety) op es
  | EFun f -> vclosure (env, f)
  | EApp (e1, e2) -> (
      let v1 = interp_exp env e1 in
      let v2 = interp_exp env e2 in
      match v1.v with
      | VClosure (c_env, f) ->
        interp_exp (update_value c_env f.arg v2) f.body
      | _ -> failwith "bad functional application" )
  | EIf (e1, e2, e3) -> (
      match (interp_exp env e1).v with
      | VBool true -> interp_exp env e2
      | VBool false -> interp_exp env e3
      | _ -> failwith "bad if condition" )
  | ELet (x, e1, e2) ->
    let v1 = interp_exp env e1 in
    interp_exp (update_value env x v1) e2
  | ETuple es -> vtuple (List.map (interp_exp env) es)
  | ESome e -> voption (Some (interp_exp env e))
  | EMatch (e1, branches) -> (
      let v = interp_exp env e1 in
      match match_branches branches v env.value with
      | Some (env2, e) -> interp_exp {env with value=env2} e
      | None ->
        failwith
          ( "value " ^ value_to_string v
            ^ " did not match any pattern in match statement" ))
  | ERecord _ | EProject _ -> failwith "Record found during interpretation"

and interp_op env ty op es =
  (* if arity op != List.length es then
     failwith
      (sprintf "operation %s has arity %d not arity %d"
         (op_to_string op) (arity op) (List.length es)) ; *)
  let vs = BatList.map (interp_exp env) es in
  match (op, vs) with
  | And, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 && b2)
  | Or, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 || b2)
  | Not, [{v= VBool b1; _}] -> vbool (not b1)
  | UAdd _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
    vint (Integer.add i1 i2)
  | Eq, [v1; v2] ->
    if equal_values ~cmp_meta:false v1 v2 then vbool true
    else vbool false
  | ULess _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
    if Integer.lt i1 i2 then vbool true else vbool false
  | ULeq _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
    if Integer.leq i1 i2 then vbool true else vbool false
  | NLess, [{v= VNode n1; _}; {v= VNode n2; _}] ->
    if n1 < n2 then vbool true else vbool false
  | NLeq, [{v= VNode n1; _}; {v= VNode n2; _}] ->
    if n1 <= n2 then vbool true else vbool false
  | MCreate, [v] -> (
      match get_inner_type ty with
      | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
      | _ -> failwith "runtime error: missing map key type" )
  | MGet, [{v= VMap m; _}; v] -> BddMap.find m v
  | MSet, [{v= VMap m; _}; vkey; vval] ->
    vmap (BddMap.update m vkey vval)
  | MMap, [{v= VClosure (c_env, f); _}; {v= VMap m; _}] ->
    let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
    let free = Syntax.free seen f.body in
    let env = build_env c_env free in
    vmap
      (BddMap.map ~op_key:(f.body, env)
         (fun v -> apply c_env f v)
         m)
  | ( MMerge
    , {v= VClosure (c_env, f); _}
      :: {v= VMap m1; _} :: {v= VMap m2; _} :: rest )
    -> (
        let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
        let env = build_env c_env (Syntax.free seen f.body) in
        (* TO DO:  Need to preserve types in VOptions here ? *)
        let f_lifted v1 v2 =
          match apply c_env f v1 with
          | {v= VClosure (c_env, f); _} -> apply c_env f v2
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
      , [ {v= VClosure (_c_env1, f1); _}
      ; {v= VClosure (c_env2, f2); _}
      ; {v= VMap m; _} ] ) ->
    let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
    let env = build_env c_env2 (Syntax.free seen f2.body) in
    let mtbdd =
      let open BddFunc in
      match ExpMap.find_opt f1.body !bddfunc_cache with
      | None -> (
          let bddf = BddFunc.create_value (oget f1.argty) in
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

and apply env f v = interp_exp (update_value env f.arg v) f.body

let interp e = interp_exp empty_env e

let interp = MemoizeExp.memoize ~size:1000 interp

let interp_closure cl (args: value list) =
  interp (Syntax.apply_closure cl args)

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

let simplify_logic op pes =
  match op with
  | And ->
    (match pes with
     | [e1; e2] when (is_value e1) ->
       simplify_and (to_value e1) e2
     | [e1; e2] when (is_value e2) ->
       simplify_and (to_value e2) e1
     | _ -> eop op pes)
  | Or ->
    (match pes with
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
     | _ -> eop op pes)
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
  | MCreate | MGet | MSet | MMap | MMerge | MMapFilter -> true
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
  | EVal _ -> e
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
      (match match_branches branches (to_value pe1) env.value with
       | Some (env2, e) -> interp_exp_partial_opt false {env with value=env2} expEnv e
       | None ->
         failwith
           ( "value " ^ value_to_string (to_value pe1)
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

and interp_op_partial_opt env expEnv _ty op es =
  let pes = BatList.map (interp_exp_partial_opt false env expEnv) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes then
    simplify_logic op pes
  else
  if isMapOp op then
    eop op pes
  else
    begin
      exp_of_value @@
      match (op, BatList.map to_value pes) with
      | And, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 && b2)
      | Or, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 || b2)
      | Not, [{v= VBool b1; _}] -> vbool (not b1)
      | UAdd _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        vint (Integer.add i1 i2)
      | Eq, [v1; v2] ->
        if equal_values ~cmp_meta:false v1 v2 then vbool true
        else vbool false
      | ULess _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        if Integer.lt i1 i2 then vbool true else vbool false
      | ULeq _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        if Integer.leq i1 i2 then vbool true else vbool false
      | NLess, [{v= VNode n1; _}; {v= VNode n2; _}] ->
        if n1 < n2 then vbool true else vbool false
      | NLeq, [{v= VNode n1; _}; {v= VNode n2; _}] ->
        if n1 <= n2 then vbool true else vbool false
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
  | EVal _ -> e
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
      (match match_branches branches (to_value pe1) env.value with
       | Some (env2, e) ->      (* Printf.printf "some: %s\n" (Printing.exp_to_string e); *)
         interp_exp_partial false {env with value=env2} e
       | None ->
         failwith
           ( "value " ^ value_to_string (to_value pe1)
             ^ " did not match any pattern in match statement"))
    else
      aexp (ematch pe1 (mapBranches (fun (p,e) ->
          (p, interp_exp_partial false env e)) branches),
            e.ety, e.espan) (* |> simplify_match *)

  | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

and interp_op_partial env _ty op es =
  let pes = BatList.map (interp_exp_partial false env) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes then
    simplify_logic op pes
  else
  if isMapOp op then
    eop op pes
  else
    begin
      exp_of_value @@
      match (op, BatList.map to_value pes) with
      | And, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 && b2)
      | Or, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 || b2)
      | Not, [{v= VBool b1; _}] -> vbool (not b1)
      | UAdd _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        vint (Integer.add i1 i2)
      | Eq, [v1; v2] ->
        if equal_values ~cmp_meta:false v1 v2 then vbool true
        else vbool false
      | ULess _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        if Integer.lt i1 i2 then vbool true else vbool false
      | ULeq _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
        if Integer.leq i1 i2 then vbool true else vbool false
      | NLess, [{v= VNode n1; _}; {v= VNode n2; _}] ->
        if n1 < n2 then vbool true else vbool false
      | NLeq, [{v= VNode n1; _}; {v= VNode n2; _}] ->
        if n1 <= n2 then vbool true else vbool false
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

let interp_partial = MemoizeExp.memoize ~size:1000 interp_partial
(* let interp_partial_opt = MemoizeExp.memoize ~size:1000 interp_partial_opt *)


let interp_partial_fun (fn : Syntax.exp) (args: value list) =
  Syntax.apps fn (List.map (fun a -> e_val a) args) |>
  interp_partial

(** * Full reduction Partial Interpreter *)

module Full =
struct

  type 'a isMatch =
      Match of 'a
    | NoMatch
    | Delayed

  (* matches p b is Some env if v matches p and None otherwise; assumes no repeated variables in pattern *)
  let rec matches p (e: Syntax.exp) : Syntax.exp Env.t isMatch =
    match p with
    | PWild -> Match Env.empty
    | PUnit ->
      if is_value e then
        match (to_value e).v with
        | VUnit -> Match Env.empty
        | _ -> NoMatch
      else
        Delayed
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
    | PVar x, EVar _ ->
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
        Delayed

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
         (match match_branches branches pe1 with
          | Match (env2, e) -> interp_exp_partial (Env.updates env env2) e
          | NoMatch ->
             failwith
               ( "exp " ^ (exp_to_string pe1)
                 ^ " did not match any pattern in match statement")
          | Delayed ->
             (env, aexp (ematch pe1 (mapBranches (fun (p,e) ->
                                         (p, snd (interp_exp_partial env e))) branches),
                   e.ety, e.espan)))
      | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

  (* this is same as above, minus the app boolean. see again if we can get rid of that? *)
  and interp_op_partial env ty op es =
    let pes = BatList.map (fun e -> snd (interp_exp_partial env e)) es in
    if BatList.exists (fun pe -> not (is_value pe)) pes then
      eop op pes
    else
      begin
        exp_of_value @@
        match (op, BatList.map to_value pes) with
        | And, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 && b2)
        | Or, [{v= VBool b1; _}; {v= VBool b2; _}] -> vbool (b1 || b2)
        | Not, [{v= VBool b1; _}] -> vbool (not b1)
        | UAdd _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
          vint (Integer.add i1 i2)
        | Eq, [v1; v2] ->
          if equal_values ~cmp_meta:false v1 v2 then vbool true
          else vbool false
        | ULess _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
          if Integer.lt i1 i2 then vbool true else vbool false
        | ULeq _, [{v= VInt i1; _}; {v= VInt i2; _}] ->
          if Integer.leq i1 i2 then vbool true else vbool false
        | NLess, [{v= VNode n1; _}; {v= VNode n2; _}] ->
          if n1 < n2 then vbool true else vbool false
        | NLeq, [{v= VNode n1; _}; {v= VNode n2; _}] ->
          if n1 <= n2 then vbool true else vbool false
        | MCreate, [v] -> (
            match get_inner_type ty with
            | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
            | _ -> failwith "runtime error: missing map key type" )
        | MGet, [{v= VMap m; _}; v] -> BddMap.find m v
        | MSet, [{v= VMap m; _}; vkey; vval] ->
          vmap (BddMap.update m vkey vval)
        | MMap, [{v= VClosure (c_env, f); _}; {v= VMap m; _}] ->
          let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
          let free = Syntax.free seen f.body in
          let env = build_env c_env free in
          vmap
            (BddMap.map ~op_key:(f.body, env)
               (fun v -> apply c_env f v)
               m)
        | ( MMerge
          , {v= VClosure (c_env, f); _}
            :: {v= VMap m1; _} :: {v= VMap m2; _} :: rest )
          -> (
              let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
              let env = build_env c_env (Syntax.free seen f.body) in
              (* TO DO:  Need to preserve types in VOptions here ? *)
              let f_lifted v1 v2 =
                match apply c_env f v1 with
                | {v= VClosure (c_env, f); _} -> apply c_env f v2
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
          , [ {v= VClosure (_c_env1, f1); _}
            ; {v= VClosure (c_env2, f2); _}
            ; {v= VMap m; _} ] ) ->
          let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
          let env = build_env c_env2 (Syntax.free seen f2.body) in
          let mtbdd =
            match ExpMap.find_opt f1.body !bddfunc_cache with
            | None -> (
              let open BddFunc in
                let bddf = BddFunc.create_value (oget f1.argty) in
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

end
