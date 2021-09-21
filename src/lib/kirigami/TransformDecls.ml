open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter
open SrpRemapping
open Nv_utils

let remap_value parted_srp v =
  let { node_map; edge_map; _ } = parted_srp in
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  let make_edge e = avalue (vedge e, Some TEdge, v.vspan) in
  match v.v with
  | VNode n ->
    let new_node = VertexMap.find_default None n node_map in
    Option.map make_node new_node
  | VEdge e ->
    let new_edge = EdgeMap.find_default None e edge_map in
    Option.map make_edge new_edge
  | _ -> Some v
;;

let remap_value_inverted fragments v = List.map (fun f -> remap_value f v) fragments

let rec remap_exp exp_freqs parted_srp e =
  (* print_endline (Printing.exp_to_string e); *)
  (* don't bother tracking variables or values *)
  (match e.e with
  | EVar _ | EVal _ -> ()
  | _ -> exp_freqs := Map.modify_def 0 e Int.succ !exp_freqs);
  let f = remap_exp exp_freqs parted_srp in
  wrap
    e
    (match e.e with
    | EMatch (e1, bs) -> ematch (f e1) (remap_branches exp_freqs parted_srp bs)
    | EVal v ->
      (match remap_value parted_srp v with
      | Some v1 -> e_val v1
      | None ->
        print_endline
          ("Warning: remap_value given "
          ^ Printing.value_to_string v
          ^ ", which should be cut");
        e_val v)
    | EOp (op, es) -> remap_exp_op exp_freqs parted_srp op es
    | ESome e -> esome (f e)
    | ETuple es -> etuple (List.map f es)
    | EProject (e, l) -> eproject (f e) l
    | EFun fn -> efun { fn with body = f fn.body }
    | EApp (e1, e2) -> eapp (f e1) (f e2)
    | ELet (x, e1, e2) -> elet x (f e1) (f e2)
    | EIf (test, e1, e2) -> eif (f test) (f e1) (f e2)
    | ERecord _ -> failwith "remap_exp: records should be unrolled"
    | ETy (e, t) -> ety (f e) t
    | EVar _ -> e)

and remap_branches exp_freqs parted_srp bs =
  let { node_map; _ } = parted_srp in
  let f = remap_exp exp_freqs parted_srp in
  let update_branches old_bs =
    foldBranches
      (fun (p, e) bs ->
        match p with
        | PTuple [PNode n1; PNode n2] ->
          let n1' = VertexMap.find_default None n1 node_map in
          let n2' = VertexMap.find_default None n2 node_map in
          (match n1', n2' with
          | Some u, Some v -> (PTuple [PNode u; PNode v], f e) :: bs
          | _ -> bs)
        | PNode u ->
          (match VertexMap.find_default None u node_map with
          | Some u' -> (PNode u', f e) :: bs
          | None -> bs)
        | PEdge _ -> failwith "remap_branches: found unboxed edge"
        | _ -> (p, f e) :: bs)
      []
      old_bs
  in
  let pat_exps = update_branches bs in
  (* put the branches back in the same order by going from the back *)
  List.fold_right (fun (p, e) b -> addBranch p e b) (List.rev pat_exps) emptyBranch

and remap_exp_op exp_freqs parted_srp op es =
  let f = remap_exp exp_freqs parted_srp in
  let ty = (List.hd es).ety |> Option.get in
  (* check if the operation is over nodes *)
  (* if so, if any nodes are cut, the op simplifies to false *)
  match ty with
  | TNode ->
    (match op with
    | Eq | NLess | NLeq ->
      (* NOTE: won't be able to fix expressions where both sides are non-values *)
      let remap_node_exp n =
        if is_value n
        then Option.map e_val (remap_value parted_srp (to_value n))
        else Some (f n)
      in
      let es1 = List.map remap_node_exp es in
      if List.exists Option.is_none es1
      then ebool false
      else eop op (List.map Option.get es1)
    | _ -> failwith (Printf.sprintf "unexpected operator %s over nodes" (show_op op)))
  | TEdge -> failwith "remap_exp_op: found unboxed edge"
  | _ -> eop op (List.map f es)
;;

let remap_solve exp_freqs parted_srp solve =
  (* let exp_freqs = ref Map.empty in *)
  let init = remap_exp exp_freqs parted_srp solve.init in
  let trans = remap_exp exp_freqs parted_srp solve.trans in
  let merge = remap_exp exp_freqs parted_srp solve.merge in
  { solve with init; trans; merge }
;;

let rec remap_exp_inverted fragments e =
  let f = remap_exp_inverted fragments in
  List.map
    (wrap e)
    (match e.e with
    | EMatch (e1, bs) -> List.map2 ematch (f e1) (remap_branches_inverted fragments bs)
    | EVal v ->
      let vs = remap_value_inverted fragments v in
      let remap_val x =
        match x with
        | Some v1 -> e_val v1
        | None ->
          print_endline
            ("Warning: remap_value given "
            ^ Printing.value_to_string v
            ^ ", which should be cut");
          e_val v
      in
      List.map remap_val vs
    | EOp (op, es) -> remap_exp_op_inverted fragments op es
    | ESome e -> List.map esome (f e)
    | ETuple es -> List.map etuple (List.transpose (List.map f es))
    | EProject (e, l) -> List.map (fun e -> eproject e l) (f e)
    | EFun fn -> List.map (fun body -> efun { fn with body }) (f fn.body)
    | EApp (e1, e2) -> List.map2 eapp (f e1) (f e2)
    | ELet (x, e1, e2) -> List.map2 (elet x) (f e1) (f e2)
    | EIf (test, e1, e2) -> OCamlUtils.map3 eif (f test) (f e1) (f e2)
    | ERecord _ -> failwith "remap_exp: records should be unrolled"
    | ETy (e, t) -> List.map (fun e -> ety e t) (f e)
    | EVar _ -> List.make (List.length fragments) e)

and remap_branches_inverted fragments bs =
  let f = remap_exp_inverted fragments in
  let update_branches old_bs =
    foldBranches
      (fun (p, e) bs ->
        match p with
        | PTuple [PNode n1; PNode n2] ->
          (* remap the nodes acc. to the fragments *)
          let nodes =
            List.map
              (fun f ->
                ( VertexMap.find_default None n1 f.node_map
                , VertexMap.find_default None n2 f.node_map ))
              fragments
          in
          OCamlUtils.map3
            (fun (n1', n2') e bs ->
              match n1', n2' with
              | Some u, Some v -> (PTuple [PNode u; PNode v], e) :: bs
              | _ -> bs)
            nodes
            (f e)
            bs
        | PNode u ->
          let nodes =
            List.map (fun f -> VertexMap.find_default None u f.node_map) fragments
          in
          OCamlUtils.map3
            (fun u e bs ->
              match u with
              | Some u' -> (PNode u', e) :: bs
              | None -> bs)
            nodes
            (f e)
            bs
        | PEdge _ -> failwith "remap_branches: found unboxed edge"
        | _ -> List.map2 (fun e bs -> (p, e) :: bs) (f e) bs)
      (List.make (List.length fragments) [])
      old_bs
  in
  let pat_exps = update_branches bs in
  (* put the branches back in the same order by going from the back *)
  List.map
    (fun pe ->
      List.fold_right (fun (p, e) b -> addBranch p e b) (List.rev pe) emptyBranch)
    pat_exps
(* List.map (fun f -> remap_branches (ref Map.empty) f bs) fragments *)

and remap_exp_op_inverted fragments op es =
  let f = remap_exp_inverted fragments in
  let ty = (List.hd es).ety |> Option.get in
  (* check if the operation is over nodes *)
  (* if so, if any nodes are cut, the op simplifies to false *)
  match ty with
  | TNode ->
    (match op with
    | Eq | NLess | NLeq ->
      (* NOTE: won't be able to fix expressions where both sides are non-values *)
      let remap_node_exp n =
        if is_value n
        then List.map (Option.map e_val) (remap_value_inverted fragments (to_value n))
        else List.map Option.some (f n)
      in
      let es1s = List.map remap_node_exp es in
      List.map
        (fun es1 ->
          if List.exists Option.is_none es1
          then ebool false
          else eop op (List.map Option.get es1))
        es1s
    | _ -> failwith (Printf.sprintf "unexpected operator %s over nodes" (show_op op)))
  | TEdge -> failwith "remap_exp_op: found unboxed edge"
  | _ -> List.map (eop op) (List.transpose (List.map f es))
;;

let remap_solve_inverted fragments solve =
  let init = remap_exp_inverted fragments solve.init in
  let trans = remap_exp_inverted fragments solve.trans in
  let merge = remap_exp_inverted fragments solve.merge in
  (* put all 3 remappings together as a list of solves *)
  OCamlUtils.map3
    (fun init trans merge -> { solve with init; trans; merge })
    init
    trans
    merge
;;

(** Remap an and expression by dropping conjuncts that refer to cut nodes.
 ** The and statement is nested as follows:
 ** And (And (And x0 x1) x2) x3
 ** so we need to recurse in until we have dropped the right number of nodes.
 ** Since the nodes are remapped, we drop the higher-numbered nodes under
 ** the assumption that the other statements have been remapped to refer to
 ** the correct nodes now.
 **)
let rec remap_conjuncts nodes e =
  if nodes > 0
  then (
    match e.e with
    | EOp (And, [e2; _]) ->
      (* go deeper *)
      remap_conjuncts (nodes - 1) e2
    | EOp (And, _) -> failwith "and has wrong number of arguments"
    (* this case should be the last one *)
    | _ -> e)
  else e
;;

(** Assume the assert is of the form:
 ** assert foldNodes (fun u v acc -> acc && assertNode u v) sol true
 ** which simplifies after map unrolling to:
 ** assert (match (sol-proj-0, sol-proj-1, ..., sol-proj-n) with
 **  | UnrollingFoldVar-0, UnrollingFoldVar-1, ..., UnrollingFoldVar-n -> true &&
 **    (assertNode 0n UnrollingFoldVar-0) && (assertNode 1n UnrollingFoldVar-1)
 **    && ... && (assertNode n UnrollingFoldVar-n)
 ** After tuple flattening, the fold variables may be further subdivided, where
 ** for a k-tuple attribute, we have n*k variables:
 ** the 0..k projected variables will belong to node 0,
 ** the k..2k variables belong to node 1, and so on.
 **)
let transform_assert (e : exp) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  let { nodes; _ } = parted_srp in
  (* we need to remap before interpreting just to stop interpretation from filling
   * in all the nodes and simplifying statements we don't want it to simplify the
   * wrong way *)
  let e = remap_exp (ref Map.empty) parted_srp e in
  match e.e with
  | EMatch _ ->
    (* if there is only one branch, use interp to simplify;
     * we should be left with an EOp statement which we can prune *)
    let e1 = InterpPartialFull.interp_partial e in
    (* FIXME: sometimes interp_partial is too aggressive; maybe we want to instead just
     * simplify the match and the first conjunct ourselves and then handle the rest *)
    (match e1.e with
    (* we want to supply the *difference* between the current nodes and the
     * number of nodes in the original SRP, because we want to descend down
     * the chain of ands until there are only *nodes* many conjuncts left *)
    | EOp (And, _) -> remap_conjuncts (get_global_nodes parted_srp - nodes) e1
    (* NOTE: this case is a hack to handle when InterpPartialFull.interp_partial is
     * too aggressive: this might happen if one of the later conjuncts simplifies
     * down to true and gets eliminated: we then assume we can replace the
     * assertion with true if the remaining expression contains variables referencing
     * solve variables.
     * Unfortunately, this hack doesn't really solve the problem it's intended to fix,
     * so we've commented it out for now. *)
    (* | EOp (_, es) ->
     *   let names = List.map Var.name (List.flatten (List.map get_exp_vars es)) in
     *   if List.exists (fun s -> String.starts_with s "solve-sol-proj") names
     *   then (
     *     print_endline
     *       ("Warning: I was given: ["
     *       ^ Printing.exp_to_string e1
     *       ^ "] by the interpreter, which I assumed was a mistake, so I substituted"
     *       ^ " [true].\nIf I made a mistake, please file an issue!");
     *     ebool true)
     *   else e *)
    | _ ->
      print_endline
        ("Warning: while transforming the assert, I got something unexpected.\n\
          Please check that the assert is of the form \"assert foldNodes (fun u v acc -> \
          acc && assertNode u v) sol true\"\n\
          Interpretation returned the following (expected an and operation): "
        ^ Printing.exp_to_string e1
        ^ "\nIf this warning was false, please file an issue."
        ^ "\nIt's possible I reduced the expression too aggressively!");
      e)
  | _ -> e
;;

(** Helper function to extract the edge predicate
 *  from the interface expression.
 ** If the given interface has only a bare term t rather than a predicate function,
 ** construct a predicate function (fun x -> x = t).
*)
let interp_interface edge intfe =
  let u, v = edge in
  let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
  let edge = [node_value u; node_value v] in
  let intf_app = InterpPartial.interp_partial_fun intfe edge in
  match intf_app.e with
  | EFun _ -> intf_app
  | EVal { v = VClosure _; _ } -> intf_app
  | _ ->
    failwith
      ("expected intf value to be a function but got " ^ Printing.exp_to_string intf_app)
;;

let update_preds interface partitioned_srp =
  let intf edge preds =
    let p = interp_interface edge interface in
    p :: preds
  in
  SrpRemapping.map_predicates intf partitioned_srp
;;

let add_interface_to_partition solve partition =
  match solve.part with
  | Some { interface; _ } -> update_preds interface partition
  | None -> partition
;;

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve exp_freqs solve (partition : partitioned_srp)
    : partitioned_srp * solve
  =
  let partition' = add_interface_to_partition solve partition in
  partition', remap_solve exp_freqs partition' solve
;;

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve_inverted solve fragments : (partitioned_srp * solve) list =
  let fragments' = List.map (add_interface_to_partition solve) fragments in
  let solves = remap_solve_inverted fragments' solve in
  List.combine fragments' solves
;;
