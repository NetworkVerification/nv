open Unsigned
open Syntax
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
let rec equal_val v1 v2 =
  match (v1.v, v2.v) with
  | VBool b1, VBool b2 -> b1 = b2
  | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
  | VMap m1, VMap m2 -> BddMap.equal m1 m2
  | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
  | VOption None, VOption None -> true
  | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
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
(* matches p b is Some env if v matches p and None otherwise; assumes no repeated variables in pattern *)
let rec matches p (v: Syntax.value) : Syntax.value Env.t option =
  match (p, v.v) with
  | PWild, v -> Some Env.empty
  | PVar x, _ -> Some (Env.bind x v)
  | PBool true, VBool true -> Some Env.empty
  | PBool false, VBool false -> Some Env.empty
  | PUInt32 i1, VUInt32 i2 ->
      if UInt32.compare i1 i2 = 0 then Some Env.empty else None
  | PTuple ps, VTuple vs -> matches_list ps vs
  | POption None, VOption None -> Some Env.empty
  | POption (Some p), VOption (Some v) -> matches p v
  | (PBool _ | PUInt32 _ | PTuple _ | POption _), _ -> None

and matches_list ps vs =
  match (ps, vs) with
  | [], [] -> Some Env.empty
  | p :: ps, v :: vs -> (
    match matches p v with
    | None -> None
    | Some env1 ->
      match matches_list ps vs with
      | None -> None
      | Some env2 -> Some (Env.updates env2 env1) )
  | _, _ -> None

let rec match_branches branches v =
  match branches with
  | [] -> None
  | (p, e) :: branches ->
    match matches p v with
    | Some env -> Some (env, e)
    | None -> match_branches branches v

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
  | EOp (op, es) -> interp_op env (oget e.ety) op es
  | EFun f -> value (VClosure (env, f))
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
  | ETuple es -> value (VTuple (List.map (interp_exp env) es))
  | ESome e -> value (VOption (Some (interp_exp env e)))
  | EMatch (e1, branches) ->
      let v = interp_exp env e1 in
      match match_branches branches v with
      | Some (env2, e) -> interp_exp (update_values env env2) e
      | None ->
          failwith
            ( "value " ^ value_to_string v
            ^ " did not match any pattern in match statement" )

and interp_op env ty op es =
  if arity op != List.length es then
    failwith
      (sprintf "operation %s has arity %d not arity %d"
         (op_to_string op) (arity op) (List.length es)) ;
  let vs = List.map (interp_exp env) es in
  match (op, vs) with
  | And, [{v= VBool b1}; {v= VBool b2}] -> VBool (b1 && b2) |> value
  | Or, [{v= VBool b1}; {v= VBool b2}] -> VBool (b1 || b2) |> value
  | Not, [{v= VBool b1}] -> VBool (not b1) |> value
  | UAdd, [{v= VUInt32 i1}; {v= VUInt32 i2}] ->
      VUInt32 (UInt32.add i1 i2) |> value
  | UEq, [v1; v2] ->
      (if equal_values v1 v2 then VBool true else VBool false)
      |> value
  | ULess, [{v= VUInt32 i1}; {v= VUInt32 i2}] ->
      (if UInt32.compare i1 i2 = -1 then VBool true else VBool false)
      |> value
  | ULeq, [{v= VUInt32 i1}; {v= VUInt32 i2}] ->
      ( if not (UInt32.compare i1 i2 = 1) then VBool true
      else VBool false )
      |> value
  | MCreate, [v] -> (
    match get_inner_type ty with
    | TMap (kty, _) -> VMap (BddMap.create ~key_ty:kty v) |> value
    | _ -> failwith "runtime error: missing map key type" )
  | MGet, [{v= VMap m}; v] -> BddMap.find m v
  | MSet, [{v= VMap m}; vkey; vval] ->
      VMap (BddMap.update m vkey vval) |> value
  | MMap, [{v= VClosure (c_env, f)}; {v= VMap m}] ->
      VMap (BddMap.map ~op_key:f.body (fun v -> apply c_env f v) m)
      |> value
  | MMerge, [{v= VClosure (c_env, f)}; {v= VMap m1}; {v= VMap m2}] ->
      (* TO DO:  Need to preserve types in VOptions here ? *)
      let f_lifted v1 v2 =
        match apply c_env f v1 with
        | {v= VClosure (c_env, f)} -> apply c_env f v2
        | _ -> failwith "internal error (interp_op)"
      in
      VMap (BddMap.merge ~op_key:f.body f_lifted m1 m2) |> value
  | ( MMapFilter
    , [ {v= VClosure (c_env1, f1)}
      ; {v= VClosure (c_env2, f2)}
      ; {v= VMap m} ] )
    -> (
      let bddf = BddFunc.create_value (oget f1.argty) in
      let env = Env.update Env.empty f1.arg bddf in
      let bddf = BddFunc.eval env f1.body in
      let f v = apply c_env2 f2 v in
      match bddf with
      | BBool bdd ->
          VMap (BddMap.map_when ~op_key:f2.body bdd f m) |> value
      | _ -> failwith "impossible" )
  | _, _ ->
      failwith
        (Printf.sprintf "bad operator application: %s"
           (Printing.op_to_string op))

and apply env f v = interp_exp (update_value env f.arg v) f.body

let interp e = interp_exp empty_env e

let interp_closure cl (args: value list) =
  interp (Syntax.apply_closure cl args)
