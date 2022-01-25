open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter
open SrpRemapping

(** Remap an and expression by dropping conjuncts that refer to cut nodes.
 ** The and statement is nested as follows:
 ** And (And (And x0 x1) x2) x3
 ** so we need to recurse in and drop the nodes as specified by the bool list [nodes],
 ** which lists the conjuncts from right to left.
 ** remap_conjuncts x0 [false] --> true
 ** remap_conjuncts x0 [true] --> x0
 ** remap_conjuncts (And x0 x1) [false; true] --> x0
 ** remap_conjuncts (And x0 x1) [true; false] --> (And true x1)
 **)
let rec remap_conjuncts e nodes =
  match nodes with
  | [] -> e
  | keep :: tl ->
    (match e.e with
    | EOp (And, [e1; e2]) ->
      (* descend *)
      if keep then
        (* keep the current conjunct *)
        wrap e (eop And [remap_conjuncts e1 tl; e2])
      else
        remap_conjuncts e1 tl
    | EOp (And, _) -> failwith "and has wrong number of arguments"
    (* this case should be the last one *)
    | _ -> if keep then e else ebool true)
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
  match e.e with
  | EMatch _ ->
    (* if there is only one branch, use interp to simplify;
     * we should be left with an EOp statement which we can prune *)
    let e1 = InterpPartialFull.interp_partial e in
    (* FIXME: sometimes interp_partial is too aggressive; maybe we want to instead just
     * simplify the match and the first conjunct ourselves and then handle the rest *)
    (match e1.e with
    (* we supply a sequence of nodes in the original SRP, labelling which ones have been
     * cut and which have been kept. we will now remove any conjuncts referring to cut nodes. *)
     | EOp (And, _) -> remap_conjuncts e1 parted_srp.cut_mask
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
  (* TODO: does it make a difference to write the interface with type e -> x -> bool versus
     e -> (x -> bool) *)
  (* TODO: does it make a difference to use InterpPartial versus InterpPartialFull here *)
  let intf_app = InterpPartial.interp_partial_fun intfe edge in
  match intf_app.e with
  | EFun _ -> intf_app
  | EVal { v = VClosure _; _ } -> intf_app
  | _ ->
    failwith
      ("expected intf value to be a function but got " ^ Printing.exp_to_string intf_app)
;;

let get_predicates fragments interface =
  let cross_edges =
    List.fold_left
      (fun es f -> EdgeSet.union (EdgeSet.of_list (SrpRemapping.get_cross_edges f)) es)
      EdgeSet.empty
      fragments
  in
  let all_preds =
    EdgeSet.fold
      (fun e m -> EdgeMap.modify_def [] e (List.cons (interp_interface e interface)) m)
      cross_edges
      EdgeMap.empty
  in
  (* TODO: do we need to save the old predicates? *)
  let add_input_preds input_exp =
    { input_exp with
      preds = EdgeMap.find_default [] input_exp.edge all_preds @ input_exp.preds
    }
  in
  let add_output_preds (edge, preds) =
    edge, EdgeMap.find_default [] edge all_preds @ preds
  in
  let add_predicates fragment =
    { fragment with
      inputs =
        VertexMap.map
          (fun input_exps -> List.map add_input_preds input_exps)
          fragment.inputs
    ; outputs =
        VertexMap.map (fun outputs -> List.map add_output_preds outputs) fragment.outputs
    }
  in
  List.map add_predicates fragments
;;
