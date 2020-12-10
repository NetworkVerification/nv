open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter
open SrpRemapping

let node_to_exp n = annot TNode (e_val (vnode n))
let edge_to_exp e = annot TEdge (e_val (vedge e))
let node_to_pat node = exp_to_pattern (node_to_exp node)
let edge_to_pat edge = exp_to_pattern (edge_to_exp edge)

let etrue = aexp (e_val (vbool true), Some TBool, Span.default)

let rec remap_pattern parted_srp p =
  let { node_map; edge_map; _ } = parted_srp in
  match p with
  | POption (Some p) -> POption (Some (remap_pattern parted_srp p))
  | PTuple ps -> PTuple (List.map (remap_pattern parted_srp) ps)
  | PNode n ->
    let node = VertexMap.find_default None n node_map in
    (match node with
    | Some n -> PNode n
    | None ->
      failwith ("pattern " ^ Printing.pattern_to_string p ^ " should have been cut!"))
  | PEdge (PNode n1, PNode n2) ->
    let edge = EdgeMap.find_default None (n1, n2) edge_map in
    (match edge with
    | Some (n1, n2) -> PEdge (PNode n1, PNode n2)
    | None ->
      failwith ("pattern " ^ Printing.pattern_to_string p ^ " should have been cut!"))
  | _ -> p
;;

let remap_value parted_srp v =
  let { node_map; edge_map; _ } = parted_srp in
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  let make_edge e = avalue (vedge e, Some TEdge, v.vspan) in
  match v.v with
  | VNode n ->
    let new_node = VertexMap.find_default None n node_map in
    (match new_node with
    | Some n -> make_node n
    | None -> failwith ("value " ^ Printing.value_to_string v ^ " should be cut!"))
  | VEdge e ->
    let new_edge = EdgeMap.find_default None e edge_map in
    (match new_edge with
    | Some e -> make_edge e
    | None -> failwith ("value " ^ Printing.value_to_string v ^ " should be cut!"))
  | _ -> v
;;

let rec remap_exp parted_srp e =
  let f = remap_exp parted_srp in
  let { node_map; _ } = parted_srp in
  let update_branches old_bs =
    foldBranches
      (fun (p, e) bs ->
        match p with
        | PEdge (PNode n1, PNode n2) ->
          let n1' = VertexMap.find_default None n1 node_map in
          let n2' = VertexMap.find_default None n2 node_map in
          (match n1', n2' with
          | Some u, Some v -> (PEdge (PNode u, PNode v), f e) :: bs
          | _ -> bs)
        | PNode u ->
          (match VertexMap.find_default None u node_map with
          | Some u' -> (PNode u', f e) :: bs
          | None -> bs)
        | _ -> (p, f e) :: bs)
      []
      old_bs
  in
  wrap
    e
    (match e.e with
    | EMatch (e1, bs) ->
      let pat_exps = update_branches bs in
      (* put the branches back in the same order by going from the back *)
      let branches =
        List.fold_right (fun (p, e) b -> addBranch p e b) (List.rev pat_exps) emptyBranch
      in
      ematch (f e1) branches
    | EVal v -> e_val (remap_value parted_srp v)
    | EOp (op, es) -> eop op (List.map f es)
    | ESome e -> esome (f e)
    | ETuple es -> etuple (List.map f es)
    | EProject (e, l) -> eproject (f e) l
    | EFun fn -> efun { fn with body = f fn.body }
    | EApp (e1, e2) -> eapp (f e1) (f e2)
    | ELet (x, e1, e2) -> elet x (f e1) (f e2)
    | EIf (test, e1, e2) -> eif (f test) (f e1) (f e2)
    | ERecord _ -> failwith "remap_exp: records should be unrolled"
    | ETy _ | EVar _ -> e)
;;

let remap_solve parted_srp solve =
  let init = remap_exp parted_srp solve.init in
  let trans = remap_exp parted_srp solve.trans in
  let merge = remap_exp parted_srp solve.merge in
  { solve with init; trans; merge }
;;

let remap_assert _parted_srp e =
  wrap
    e
    (match e.e with
    | EOp (op, _es) ->
      (match op with
      | TGet (_size, _lo, _hi) ->
        (* TODO: remap to true if the accessed term is a cut node *)
        e
      | _ -> e)
    | _ -> e)
;;

(* Create an annotated match statement *)
let amatch v t b = annot t (ematch (aexp (evar v, Some t, Span.default)) b)

(** Add match branches using the given map of old nodes to new nodes. *)
let match_of_node_map
    (m : Vertex.t option VertexMap.t)
    (f : Vertex.t -> Vertex.t -> exp)
    b
  =
  let add_node_branch old_node new_node branches =
    match new_node with
    | Some n -> addBranch (node_to_pat n) (f n old_node) branches
    | None -> branches
    (* if there is no new node, just map the old node to itself *)
    (* addBranch (node_to_pat old_node) (node_to_exp old_node) branches *)
  in
  VertexMap.fold add_node_branch m b
;;

(** Add match branches using the given map of old edges to new edges. *)
let match_of_edge_map (m : Edge.t option EdgeMap.t) b =
  let add_edge_branch old_edge new_edge branches =
    match new_edge with
    | Some e -> addBranch (edge_to_pat e) (edge_to_exp old_edge) branches
    | None -> branches
  in
  EdgeMap.fold add_edge_branch m b
;;

(* Apply and partially interpret the given transfer function t on the given edge e and attribute value x. *)
let apply_trans ty e t x =
  let u, v = e in
  let trans_app = apps t [node_to_exp u; node_to_exp v] in
  let trans_curried = annot (TArrow (ty, ty)) trans_app in
  (* partially interpret the transfer function *)
  InterpPartialFull.interp_partial (annot ty (eapp trans_curried x))
;;

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (init : exp) (trans : exp option) (merge : exp) ty parted_srp
    : Syntax.exp
  =
  let interp = InterpPartialFull.interp_partial in
  let ({ node_map; inputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  let node_var = Var.fresh "node" in
  (* function we recursively call to build up the new base node init *)
  let merge_input node node_exp input_exp =
    let ({ var; edge; _ } : SrpRemapping.input_exp) = input_exp in
    let input_exp = annot ty (evar var) in
    (* perform the input transfer on the input exp *)
    let trans_input_exp =
      Option.apply (Option.map (apply_trans ty edge) trans) input_exp
    in
    (* perform the merge function, using the given node and its current value with the input variable *)
    let curried_node =
      interp (annot (TArrow (TArrow (ty, ty), ty)) (eapp merge (node_to_exp node)))
    in
    let curried_node_exp = annot (TArrow (ty, ty)) (eapp curried_node node_exp) in
    interp (wrap node_exp (eapp curried_node_exp trans_input_exp))
  in
  (* we use both node names here since the inputs are organized acc. to new node name, while the old node name
   * is needed to interpret the old function *)
  let map_nodes new_node old_node =
    let interp_old_node =
      annot ty (InterpPartialFull.interp_partial_fun init [node_to_exp old_node])
    in
    match VertexMap.Exceptionless.find new_node inputs with
    | Some input_nodes ->
      List.fold_left
        (fun e input -> merge_input old_node e input)
        interp_old_node
        input_nodes
    | None -> interp_old_node
  in
  let branches = match_of_node_map node_map map_nodes emptyBranch in
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
  wrap
    init
    (efunc (funcFull node_var (Some TNode) (Some ty) (amatch node_var TNode branches)))
;;

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
 *)
let transform_trans (e : exp) (attr : ty) (parted_srp : SrpRemapping.partitioned_srp)
    : Syntax.exp
  =
  let ({ edge_map; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let x_var = Var.fresh "x" in
  (* Simplify the old expression to an expression just over the second variable *)
  let interp_trans edge =
    InterpPartialFull.interp_partial (annot attr (apps e [edge; annot attr (evar x_var)]))
  in
  let edge_map_match = match_of_edge_map edge_map emptyBranch in
  let branches = mapBranches (fun (pat, edge) -> pat, interp_trans edge) edge_map_match in
  let body =
    if isEmptyBranch branches then evar x_var else amatch edge_var TEdge branches
  in
  let x_lambda = efunc (funcFull x_var (Some attr) (Some attr) (annot attr body)) in
  let lambda =
    efunc (funcFull edge_var (Some TEdge) (Some (TArrow (attr, attr))) x_lambda)
  in
  wrap e lambda
;;

let transform_merge (e : exp) (ty : ty) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  let ({ node_map; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* the internal type after matching on the node *)
  let inner_ty = TArrow (ty, TArrow (ty, ty)) in
  let node_var = Var.fresh "node" in
  let interp_merge node =
    InterpPartialFull.interp_partial (annot inner_ty (eapp e node))
  in
  let branches =
    match_of_node_map node_map (fun _ old -> interp_merge (node_to_exp old)) emptyBranch
  in
  wrap
    e
    (efunc
       (funcFull node_var (Some TNode) (Some inner_ty) (amatch node_var TNode branches)))
;;

(* Check that the solution's value at a particular output vertex satisfies the predicate. *)
let add_output_pred
    (trans : exp option)
    (attr : ty)
    (sol : exp)
    (n : Vertex.t)
    (* (base_nodes : int) *)
      (edge, pred)
    acc
  =
  (* FIXME: figure out what this is after map unrolling *)
  let sol_x = annot attr (eop MGet [sol; node_to_exp n]) in
  (* let sol_x = annot attr (eop (TGet (base_nodes, n, n)) [sol]) in *)
  match pred with
  | Some p ->
    InterpPartialFull.interp_partial
      (annot
         TBool
         (eapp p (Option.apply (Option.map (apply_trans attr edge) trans) sol_x)))
    :: acc
  | None -> acc
;;

(* Check each output's solution in the sol variable. *)
let outputs_assert
    (trans : exp option)
    (sol : exp)
    (attr : ty)
    (parted_srp : SrpRemapping.partitioned_srp)
    : exp list
  =
  let ({ outputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* re-map every output to point to its corresponding predicate *)
  (* let base_nodes = VertexMap.cardinal node_map in *)
  let add_preds n outputs acc =
    List.fold_left
      (fun acc output -> add_output_pred trans attr sol n output acc)
      acc
      outputs
  in
  VertexMap.fold add_preds outputs []
;;

(** Collect all the conjuncts in the given expression. *)
let rec collect_conjuncts l e =
  (* print_endline (Printing.exp_to_string e); *)
  match e.e with
  | EOp (And, es) -> List.flatten (List.map (collect_conjuncts []) es) @ l
  | _ -> e :: l
  ;;

(** Replace subexpressions in a nested series of EOp Ands according to the
 ** given rubric list: if the head of the rubric is true, keep the subexpression;
 ** if it is false, replace the subexpression with true. *)
let rec prune_conjuncts rubric e =
  (* FIXME: we don't want to burrow down super deeply; if a nested foldNodes is used,
   * then we could end up with the wrong rubric length.
   * additionally, internal projected elements could be used together as part of a
   * single conjunct.
   * a better approach may be to determine the outermost And and only use a rubric that
   * covers the number of nodes in the global network, so we can just eliminate elements
   * that way *)
  print_endline (Nv_utils.OCamlUtils.list_to_string string_of_bool rubric);
  print_endline (Printing.exp_to_string e);
  match e.e with
  | EOp (And, [e2; e3]) -> (match rubric with
    | [] -> failwith "rubric shorter than number of conjuncts"
    | h :: t -> let e2' = if h then e2 else etrue in
      wrap e (eop And [e2'; prune_conjuncts t e3] ))
  | EOp (And, _) -> failwith "and has wrong number of arguments"
  (* this case should be the last one *)
  | _ -> (match rubric with
    | [] -> failwith "rubric shorter than number of conjuncts"
    | [b] -> if b then e else etrue
    | _ -> failwith "rubric longer than number of conjuncts")
  ;;

(** Assume the assert is of the form:
 ** assert foldNodes (fun u v acc -> assertNode u v && acc) sol true
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
let transform_assert (e : exp) (width : int) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  let { node_map; _ } = parted_srp in
  (* create a list of bool of length n * k; zip it against the conjuncts and replace any
   * for which the corresponding bool is false with the statement "true" *)
  let rubric = VertexMap.fold (fun _ v l -> (match v with
      | Some _ -> List.make width true
      | None -> List.make width false) @ l) node_map [] in
  (* TODO: drop expressions or simplify them to true if they reference nodes we don't have access to *)
  let e = (match e.e with
   | EMatch _ ->
     (* TODO: if there is only one branch, use interp to simplify;
      * we should be left with an EOp statement which we can prune *)
     (* NOTE: this will also lead to a simplification of the "true" at the start of the
      * statement, so our width should not be off by 1 *)
     let e1 = InterpPartialFull.interp_partial e in
     (match e1.e with
     | EOp (And, _) ->
       prune_conjuncts rubric e1
       (* let conjs = collect_conjuncts [] e1 in
        * if (List.length conjs) = width then
        *   print_endline "got all conjuncts"
        * else
        *   print_endline
        *     ("found and length different from what I expected: expected "
        *      ^ (string_of_int width) ^ ", got "
        *      ^ (string_of_int (List.length conjs))) *)
     | _ -> print_endline ("not an and: " ^ Printing.exp_to_string e1); e)
   | _ -> e) in
  remap_exp parted_srp e
;;

(** Helper function to extract the edge predicate
 *  from the interface expression.
*)
let interp_interface intfe e : exp option =
  (* print_endline ("interface exp: " ^ Printing.exp_to_string intfe); *)
  let u, v = e in
  let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
  let edge = [node_value u; node_value v] in
  let intf_app =
    InterpPartial.interp_partial_fun
      intfe
      edge
      (* [avalue (vedge e, Some Typing.edge_ty, Span.default)] *)
  in
  (* if intf_app is not an option, or if the value it contains is not a function,
   * fail *)
  match intf_app.e with
  | ESome exp -> Some exp
  | EVal { v = VOption o; _ } ->
    begin
      match o with
      | Some { v = VClosure (_env, func); _ } -> Some (efunc func)
      | Some _ -> failwith "expected a closure, got something else instead!"
      (* infer case *)
      | None -> None
    end
  (* ETuple case handles an unboxed option *)
  | ETuple [{ e = EVal { v = VBool b; _ }; _ }; o] -> if b then Some o else None
  | _ ->
    failwith
      ("expected intf value to be an option but got " ^ Printing.exp_to_string intf_app)
;;

let update_preds interface partitioned_srp =
  let intf_opt e = Option.bind interface (fun intfe -> interp_interface intfe e) in
  { partitioned_srp with
    inputs =
      VertexMap.map
        (fun input_exps ->
          List.map
            (fun input_exp -> { input_exp with pred = intf_opt input_exp.edge })
            input_exps)
        partitioned_srp.inputs
  ; outputs =
      VertexMap.map
        (fun outputs -> List.map (fun (edge, _) -> edge, intf_opt edge) outputs)
        partitioned_srp.outputs
  }
;;

let transform_var_names var_names partitioned_srp =
  (* TODO: eliminate certain var_names elements, depending on what the type is *)
  match Option.get var_names.ety with
  | TVar _ -> var_names
  | TTuple ts -> var_names
  | _ -> failwith "unexpected type"
;;

let collect_requires_and_symbolics ty partition
    : (exp, int) Map.t * (var * ty_or_exp) list
  =
  let add_requires _ input_exps (m, l) =
    List.fold_left
      (fun (m, l) { var; rank; pred; _ } ->
        ( (match pred with
          | Some p ->
            Map.add
              (InterpPartialFull.interp_partial
                 (annot TBool (eapp p (annot ty (evar var)))))
              rank
              m
          | None -> m)
        , (var, Ty ty) :: l ))
      (m, l)
      input_exps
  in
  VertexMap.fold add_requires partition.inputs (Map.empty, [])
;;

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve solve (partition : SrpRemapping.partitioned_srp)
    : solve * exp list * (var * ty_or_exp) list * (exp, int) Map.t
  =
  let ({ aty; var_names; init; trans; merge; interface; decomp } : solve) = solve in
  (* print_endline "in transform_solve"; *)
  let partition' = update_preds interface partition in
  let attr_type = aty |> Option.get in
  (* NOTE: we don't perform any kind of verification that the decomposition is sound;
   * if we've got it, we use it! *)
  let outtrans, intrans =
    match decomp with
    | Some (lt, rt) -> lt, rt
    (* default behaviour: perform the transfer on the output side *)
    | None -> Some trans, None
  in
  let init = remap_exp partition' init in
  let trans = remap_exp partition' trans in
  let merge = remap_exp partition' merge in
  (* let init = transform_init init intrans merge attr_type partition' in
   * let trans = transform_trans trans attr_type partition' in
   * let merge = transform_merge merge attr_type partition' in *)
  (* TODO: don't add this yet *)
  let assertions = [] in
  (* let assertions = outputs_assert outtrans var_names attr_type partition' in *)
  (* collect require and symbolic information *)
  let reqs, symbolics = collect_requires_and_symbolics attr_type partition' in
  ( { solve with
      init
    ; trans
    ; merge
    ; (* should this be erased, or kept as reference? *)
      interface = None
    ; decomp
    }
  , assertions
  , symbolics
  , reqs )
;;
