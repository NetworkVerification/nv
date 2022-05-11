open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang
open Nv_lang.Syntax
open Nv_lang.Collections
open Nv_interpreter
open Nv_utils.OCamlUtils
open SrpRemapping

(* Collect all variables from symbolics associated with each input of the fragment.
 * Implicitly assumes that variable names can be checked to determine the original variable
 * after performing transformations. *)
let update_vars_from_symbolics fragment (symbs : (var * ty_or_exp) list) =
  let get_edge_symbs edge =
    List.filter_map
      (fun (v, _) -> if SrpRemapping.is_hyp_var edge v then Some v else None)
      symbs
  in
  { fragment with
    inputs =
      VertexMap.map
        (fun ies ->
          List.map
            (fun (ie : input_exp) -> { ie with var_names = get_edge_symbs ie.edge })
            ies)
        fragment.inputs
  }
;;

(** Return a new set of declarations of all symbolics added by this partition. *)
let get_hyp_symbolics aty (part : fragment) =
  VertexMap.fold
    (fun _ input_exps ds ->
      List.fold_left
        (fun ds (ie : input_exp) ->
          List.map (fun v -> DSymbolic (v, Ty aty)) ie.var_names @ ds)
        ds
        input_exps)
    part.inputs
    []
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

(** For each of the given fragments, add its associated predicates from the given interface.
 ** Computes the predicate for each cross edge.
*)
let add_interface_predicates fragments interface =
  (* compute the set of all cross edges across fragments *)
  let cross_edges =
    List.fold_left
      (fun es f -> EdgeSet.union (EdgeSet.of_list (SrpRemapping.get_cross_edges f)) es)
      EdgeSet.empty
      fragments
  in
  (* for every cross edge, map it to a list of predicates *)
  let all_preds =
    EdgeSet.fold
      (fun e m -> EdgeMap.add e (interp_interface e interface) m)
      cross_edges
      EdgeMap.empty
  in
  (* TODO: do we need to save the old predicates? *)
  let add_input_preds input_exp =
    { input_exp with
      preds = match (EdgeMap.Exceptionless.find input_exp.edge all_preds) with
        | Some p -> p :: input_exp.preds
        | None -> input_exp.preds
    }
  in
  let add_output_preds (edge, preds) =
    edge, match (EdgeMap.Exceptionless.find edge all_preds) with
    | Some p -> p :: preds
    | None -> preds
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
      if keep
      then (* keep the current conjunct *)
        wrap e (eop And [remap_conjuncts e1 tl; e2])
      else remap_conjuncts e1 tl
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
let transform_assert (e : exp) (frag : SrpRemapping.fragment) : exp =
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
    | EOp (And, _) -> remap_conjuncts e1 frag.cut_mask
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

(** Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 ** that need to be added with it.
 ** NOTE: must run after Nv_transformations.RenameForSMT.rename_declarations in order to match symbolics
 ** correctly. *)
let transform_declaration frag decl : declaration option =
  (* get the list of all assumption symbolics which should appear *)
  let valid_edges = get_cross_edges frag in
  match decl with
  | DNodes _ -> Some (DNodes frag.nodes)
  | DEdges _ -> Some (DEdges frag.edges)
  (* drop any hypotheses that don't belong to this partition *)
  | DSymbolic (v, _) ->
    (match (SrpRemapping.var_to_edge v) with
    | Some e when not (List.exists ((=) e) valid_edges) -> None
    | _ -> Some decl)
  | DPartition _ -> None
  | DAssert e -> Some (DAssert (transform_assert e frag))
  | _ -> Some decl
;;

let transform_declarations decls frag =
  let symbs = get_symbolics decls in
  let frag = update_vars_from_symbolics frag symbs in
  let add_new_decl (part, decls) d =
    match transform_declaration part d with
    | Some d -> part, d :: decls
    | None -> part, decls
  in
  List.fold_left add_new_decl (frag, []) decls
;;
