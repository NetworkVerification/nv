open Batteries
open Nv_datastructures
open Nv_lang
open Syntax
open Collections

(* Very simple dependency analysis for heavily-simplified NV programs. It
   assumes the following have been done: Inlining, Record Unrolling, Map Unrolling,
   Option Unboxing, Tuple Flattening, Renaming. In particular, we should encounter
   no records, maps, or options *)

type dependency =
  | ArgDep of int (* Argument number *)
  | VarDep of var (* Variable name *)
;;

module DepSet = BatSet.Make (struct
    type t = dependency
    let compare = compare
  end)
;;

type depresult =
  | DBase of DepSet.t
  | DTuple of depresult list
;;

type depmap = depresult VarMap.t
;;

let dependency_to_string d =
  match d with
  | ArgDep n -> Printf.sprintf "Arg%d" n
  | VarDep x -> Var.to_string x
;;

let rec depresult_to_string r =
  match r with
  | DBase set ->
    Printf.sprintf "{ %s}"
      (DepSet.fold (fun elt s -> (dependency_to_string elt) ^ "; " ^ s) set "")
  | DTuple lst ->
    Printf.sprintf "( %s)"
      (BatString.concat "; " @@ BatList.map depresult_to_string lst)
;;

let rec add_to_depresult (newdeps : DepSet.t) (r : depresult) =
  match r with
  | DBase s -> DBase (DepSet.union newdeps s)
  | DTuple lst -> DTuple (List.map (add_to_depresult newdeps) lst)
;;

let rec combine_depresults r1 r2 =
  match r1, r2 with
  | DBase s1, DBase s2 -> DBase (DepSet.union s1 s2)
  | DTuple lst1, DTuple lst2 -> DTuple (List.map2 combine_depresults lst1 lst2)
  | _ ->
    failwith @@ "Cannot combine different kinds of depresults: " ^
                depresult_to_string r1 ^ " and " ^ depresult_to_string r2
;;

let rec compress_depresult r =
  match r with
  | DBase _ -> r
  | DTuple lst ->
    let lst = List.map compress_depresult lst in
    List.fold_left combine_depresults (List.hd lst) (List.tl lst)
;;


let rec compute_dependencies_exp (acc : depmap) (e : exp) : depresult =
  match e.e with
  | EVar x ->
    (try VarMap.find x acc
     with | _ -> DBase (DepSet.singleton (VarDep x)))
  | EVal v ->
    begin
      match v.v with
      | VTuple vs -> DTuple (List.map (fun _ -> DBase DepSet.empty) vs)
      | _ -> DBase DepSet.empty
    end
  | ETy (exp, _) -> compute_dependencies_exp acc exp
  | EOp (op, es) -> compute_dependencies_op acc op es
  | ETuple lst -> DTuple (List.map (compute_dependencies_exp acc) lst)
  | ELet (x, e1, e2) ->
    let e1_deps = compute_dependencies_exp acc e1 in
    let acc = VarMap.add x e1_deps acc in (* TODO: Unroll any VarDeps? I don't think so. *)
    compute_dependencies_exp acc e2
  | EIf (test, tru, fls) ->
    let test_deps = compute_dependencies_exp acc test in
    let tru_deps = compute_dependencies_exp acc tru in
    let fls_deps = compute_dependencies_exp acc fls in
    let test_deps =
      match test_deps with
      | DBase s -> s
      | _ -> failwith "impossible"
    in
    combine_depresults tru_deps fls_deps
    |> add_to_depresult test_deps
  | EMatch (test, branches) ->
    let test_deps = compute_dependencies_exp acc test in
    let branch_deps =
      branches
      |> branchToList
      |> List.map (compute_dependencies_branch acc test_deps)
    in
    List.fold_left combine_depresults (List.hd branch_deps) (List.tl branch_deps)
  | ESome _ -> failwith "Options must be unboxed before doing dependency analysis"
  | EFun _ | EApp _ -> failwith "Must inline before doing dependency analysis"
  | ERecord _ | EProject _ -> failwith "Must unroll records before doing dependency analysis"

and compute_dependencies_branch acc test_deps (pat, body) : depresult =
  (* Printf.printf "On branch %s -> %s\n" (Printing.pattern_to_string pat) (Printing.exp_to_string body); *)
  (* Global deps represent parts of the input which all parts of the branch result
     depend on *)
  let rec get_deps_from_pat (acc, global_deps) test_deps p =
    match p with
    | PWild -> acc, global_deps
    | PVar x -> VarMap.add x test_deps acc, global_deps
    | PUnit
    | PBool _
    | PInt _
    | PNode _ ->
      let depset =
        match test_deps with
        | DBase s -> s
        | _ -> failwith "internal error (compute_dependencies_branch)"
      in
      (* We're matching on an actual value (or part of one), so
         the entire branch depends on the value *)
      acc, DepSet.union depset global_deps
    | PTuple ps ->
      let deps =
        match test_deps with
        | DTuple ts -> ts
        | _ -> failwith "internal error (compute_dependencies_branch)"
      in
      (* Printf.printf "Combining lists: [%s] [%s]\n"
         (BatString.concat ";" @@ List.map depresult_to_string deps)
         (BatString.concat ";" @@ List.map Printing.pattern_to_string ps)
         ; *)
      let lst = List.combine deps ps in
      List.fold_left (fun acc' (tdep, p) -> get_deps_from_pat acc' tdep p) (acc, global_deps) lst
    | POption _
    | PRecord _ -> failwith "Found option or record pattern during dependency computation"
    | PEdge _ -> failwith "Edge patterns should have been removed during tuple flattening"
  in
  let acc, global_deps =
    get_deps_from_pat (acc, DepSet.empty) test_deps pat
  in
  compute_dependencies_exp acc body
  |> add_to_depresult global_deps

and compute_dependencies_op acc op es : depresult =
  (* Printf.printf "CDO: %s, [%s]\n" (Printing.op_to_string op) (mst.map Printing.exp_to_string es); *)
  (* Common pattern in this function *)
  let get_dtuple (d : depresult) =
    match d with
    | DTuple lst -> lst
    | _ -> failwith "internal error (compute_dependencies_op)"
  in
  match op, es with
  | Not, [e1] -> compute_dependencies_exp acc e1
  | And, [e1; e2]
  | Or, [e1; e2]
  | UAdd _, [e1; e2]
  | USub _, [e1; e2]
  | ULess _, [e1; e2]
  | ULeq _, [e1; e2]
  | NLess, [e1; e2]
  | NLeq, [e1; e2] ->
    combine_depresults (compute_dependencies_exp acc e1) (compute_dependencies_exp acc e2)
  | Eq, [e1; e2] ->
    (* If our intermediate results were DTuples, we need to compress them to DBase *)
    combine_depresults
      (compress_depresult @@ compute_dependencies_exp acc e1)
      (compress_depresult @@ compute_dependencies_exp acc e2)
  | TGet (_, lo, hi), [e1] ->
    let deps = get_dtuple (compute_dependencies_exp acc e1) in
    if lo = hi then List.nth deps lo
    else DTuple (BatList.take (hi - lo + 1) (BatList.drop lo deps))
  | TSet (_, lo, hi), [e1; e2] ->
    let original_deps = compute_dependencies_exp acc e1 in
    let new_deps = compute_dependencies_exp acc e2 in
    let odeps = get_dtuple original_deps in
    if lo = hi then
      DTuple (List.modify_at lo (fun _ -> new_deps) odeps)
    else
      let hd, rest = BatList.takedrop lo odeps in
      let _, tl = BatList.takedrop (hi - lo + 1) rest in
      let ndeps = get_dtuple new_deps in
      DTuple (hd @ ndeps @ tl)
  | AtMost _, _ -> failwith "Not implemented"
  | (MCreate | MGet | MSet | MMap | MMapFilter | MMerge | MFoldNode | MFoldEdge), _ ->
    failwith "Map operations should be unrolled before dependency analysis"
  | _ -> failwith "Invalid number of arguments to op"
;;

let extract_args f =
  let rec extract_args acc count f =
    match f.e with
    | EFun {arg=x; body=body; _} ->
      extract_args
        (VarMap.add x (DBase (DepSet.singleton (ArgDep count))) acc)
        (count+1)
        body
    | _ -> acc, f
  in
  extract_args (VarMap.empty) 0 f
;;

let compute_dependencies (e : exp) =
  let acc, body = extract_args e in
  compute_dependencies_exp acc body

let get_attr_size net =
  match net.attr_type with
  | TTuple lst -> List.length lst
  | _ -> failwith "get_attr_size: Attribute must have tuple type"
;;
