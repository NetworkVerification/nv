open Nv_datastructures
open Nv_lang

(* Expression and operator interpreters *)
(* matches p b is Some env if v matches p and None otherwise; assumes
   no repeated variables in pattern *)
let rec matches p (v: Syntax.value) env : Syntax.value Env.t option =
  let open Syntax in
  match (p, v.v) with
  | PWild, _ -> Some env
  | PVar x, _ -> Some (Env.update env x v)
  | PUnit, VUnit -> Some env
  | PBool true, VBool true
  | PBool false, VBool false -> Some env
  | PInt i1, VInt i2 ->
    if Nv_datastructures.Integer.equal i1 i2 then Some env else None
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
  let open Syntax in
  match v.v with
  | VInt i -> PInt i
  | VBool b -> PBool b
  | VOption (Some v) -> POption (Some (val_to_pat v))
  | VOption None -> POption None
  | VTuple vs ->
    PTuple (BatList.map val_to_pat vs)
  | VRecord map -> PRecord (Collections.StringMap.map val_to_pat map)
  | VNode n -> PNode n
  | VEdge (n1, n2) -> PEdge (PNode n1, PNode n2)
  | VUnit -> PUnit
  | VMap _
  | VClosure _ -> PWild

let rec match_branches branches v env =
  (* Syntax.iterBranches (fun (p,e) ->  Printf.printf "%s\n" (Printing.pattern_to_string p)) branches;
   * Printf.printf "val: %s\n" (Printing.value_to_string v); *)
  match Syntax.lookUpPat (val_to_pat v) branches with
  | Found e -> Some (env, e)
  | Rest ls -> match_branches_lst ls v env

(* We have an ExpMap in Collections that uses a slightly different
   comparison function (one which allows for hashing). I don't see
   a reason to redefine it here, but maybe the difference in comparison
   matters *)
(* module ExpMap = Map.Make (struct
    type t = exp

    let compare = Pervasives.compare
   end) *)

let build_env (env: Syntax.env) (free_vars: Nv_datastructures.Var.t BatSet.PSet.t) :
  Syntax.value BatSet.PSet.t =
  let base = BatSet.PSet.create Syntax.compare_values in
  BatSet.PSet.fold
    (fun v acc ->
       match Env.lookup_opt env.value v with
       | Some value -> BatSet.PSet.add value acc
       | None -> acc )
    free_vars base

let bddfunc_cache : bool Cudd.Mtbdd.t Collections.ExpMap.t ref = ref Collections.ExpMap.empty
