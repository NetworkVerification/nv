open Batteries
open Nv_utils
open OCamlUtils
open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open Dependency
open Nv_solution
open Nv_interpreter

(* Maps attribute elements to the set of other elements they depend on *)
type attrdepmap = IntSet.t IntMap.t

(* Maps function arguments to the attribute element they correspond to *)
type argmap = int IntMap.t

let attrdepmap_to_string m =
  Printf.sprintf "{ %s }" @@
  IntMap.fold
    (fun d deps acc ->
       Printf.sprintf "%s\n %d : { %s } " acc d @@
       IntSet.fold (fun d acc -> acc ^ "; " ^ string_of_int d) deps "")
    m ""
;;

let get_attr_size net =
  match net.attr_type with
  | TTuple lst -> List.length lst
  | _ -> failwith "get_attr_size: Attribute must have tuple type"
;;

let extract_dtuple depresult =
  match depresult with
  | DTuple lst ->
    begin
      List.map (function DBase s -> s | _ -> failwith "impossible") lst
    end
  | _ -> failwith "extract_dtuple: Not a DTuple"
;;

let extract_dbase depresult =
  match depresult with
  | DBase s -> s
  | _ -> failwith "extract_dtuple: Not a DBase"
;;

let transitive_closure (m : attrdepmap) : attrdepmap =
  let seen = ref IntSet.empty in
  let computed = ref IntMap.empty in
  let rec compute_one_index index =
    (* Memoization: see if we've already fully computed index's dependencies *)
    match IntMap.Exceptionless.find index !computed with
    | None ->
      (* Avoid infinite loops *)
      if IntSet.mem index !seen then IntSet.empty else
        begin
          seen := IntSet.add index !seen;
          let immediate_dependencies = IntMap.find index m in
          let transitive_dependencies =
            immediate_dependencies
            |> IntSet.elements
            |> List.map (fun n -> compute_one_index n)
            |> List.fold_left IntSet.union immediate_dependencies
          in
          computed := IntMap.add index transitive_dependencies !computed;
          transitive_dependencies
        end
    | Some s -> s
  in
  IntMap.iter
    (fun index _ ->
       seen := IntSet.empty;
       ignore @@ compute_one_index index)
    m
  ;
  !computed
;;

(* Given a map of argument numbers to attribute elements and dependencies of
   attribute elements on arguments, construct the dependencies of attribute
   elements on each other. *)
let process_dependencies (argmap : argmap) (deps : DepSet.t list) : IntSet.t list =
  let process_one_dependency d acc =
    match d with
    | VarDep _ -> acc
    | ArgDep n ->
      try
        let index = IntMap.find n argmap in
        IntSet.add index acc
      with
        Not_found -> acc
  in
  List.map (fun s -> DepSet.fold process_one_dependency s IntSet.empty) deps
;;

(* Given a network which has been fully transformed (i.e. satisfies the
   requirements listed in Dependency.ml), and whose attribute type is a tuple,
   this function determines which elements of the attribute depend on which other
   elements.
   The result maps each index in the tuple to the set of indices that it
   depends on; note that an index may depend on itself. *)
let attribute_dependencies (net : Syntax.network) : attrdepmap =
  let attr_size = get_attr_size net in
  (* Map the arguments to trans/merge/init to the corresponding attribute elements *)
  let init_argmap = IntMap.empty in
  let trans_argmap =
    (* First two arguments to trans are nodes, not attribute elements *)
    2--(attr_size+2)
    |> Enum.foldi (fun i argnum acc -> IntMap.add argnum i acc) IntMap.empty
  in
  let merge_argmap =
    (* First argument to merge is a node, not attribute element *)
    let first_n_args =
      1--(attr_size+1)
      |> Enum.foldi (fun i argnum acc -> IntMap.add argnum i acc) IntMap.empty
    in
    (attr_size+1)--(2*attr_size+1)
    |> Enum.foldi (fun i argnum acc -> IntMap.add argnum i acc) first_n_args
  in
  let init_deps = compute_dependencies net.init |> extract_dtuple |> process_dependencies init_argmap in
  let trans_deps = compute_dependencies net.trans |> extract_dtuple |> process_dependencies trans_argmap in
  let merge_deps = compute_dependencies net.merge |> extract_dtuple |> process_dependencies merge_argmap in
  let all_deps =
    OCamlUtils.map3i
      (fun n a b c -> n, IntSet.union a (IntSet.union b c))
      init_deps trans_deps merge_deps
  in
  List.fold_left (fun acc (i, s) -> IntMap.add i s acc) IntMap.empty all_deps
  |> transitive_closure
;;

(* Given a network, we first break down its assert function into its smallest
   conjuncts (which may be the whole thing, if it's not a conjunction). Then for
   each conjunct, we determine which elements of the attribute it depends upon. *)
let assert_dependencies (net : Syntax.network) =
  let attr_size = get_attr_size net in
  let assert_argmap =
    1--(attr_size+1)
    |> Enum.foldi (fun i argnum acc -> IntMap.add argnum i acc) IntMap.empty
  in
  let assertion = net.assertion |> oget in
  let starting_deps, body = extract_args assertion in
  let body = Nv_interpreter.InterpPartialFull.interp_partial body in
  let compute_final_dependencies conjunct =
    compute_dependencies_exp starting_deps conjunct |> extract_dbase
    |> List.singleton |> process_dependencies assert_argmap |> List.hd
  in
  (* Break down the assertion into its conjuncts. If it's not a conjunction this
     does nothing. *)
  let rec get_conjuncts acc e =
    match e.e with
    | EOp (And, es) ->
      List.fold_left get_conjuncts acc es
    | _ -> e::acc

  in
  List.map (fun c -> c, compute_final_dependencies c) (get_conjuncts [] body)
;;

(* If we're slicing away every attribute element (which can happpen if we're
   e.g. doing a fold), we also slice away every argument to the srp functions,
   which causes type errors later. In that case, add a dummy argument to each
   function *)
let add_dummy_arg args_to_add elements (body : exp) =
  if not (IntSet.is_empty elements) then body else
    let rec aux count body =
      if count = 0 then body else
        aux (count-1) @@
        aexp
          (efun ({arg= Var.fresh "SlicingUnitVar"; argty = Some (TTuple []); resty= body.ety; body=body}),
           Some (TArrow (TTuple [], oget body.ety)),
           body.espan)
    in
    aux args_to_add body
;;

let rewrite_fun (attr_ty : ty) (elts_to_keep : IntSet.t) (assertion : exp) (leading_args : int) (args_to_add : int) (f : exp) =
  (* Types of the elements of the original attribute *)
  let attr_tys =
    match attr_ty with | TTuple lst -> lst | _ -> failwith "impossible"
  in
  let attr_size = List.length attr_tys in
  (* Types of the elements of the sliced attribute *)
  let rec rewrite_fun_aux
      (e : exp)
      (count : int)
      (args : (var * ty option * bool) list) (* Bool is true iff we kept this argument *)
      (cont : exp -> exp) =
    match e.e with
    | EFun func ->
      if (count < leading_args) || (* This arg doesn't correspond to an attribute element *)
         IntSet.mem ((count - leading_args) mod attr_size) elts_to_keep (* This arg corresponds to an element that we're keeping *)
      then
        rewrite_fun_aux func.body (count + 1) ((func.arg, func.argty, true)::args)
          (fun e ->
             let ety = Some (TArrow (func.argty |> oget, e.ety |> oget)) in
             let result = aexp (efun {func with body=e; resty=e.ety}, ety, e.espan) in
             cont result)
      else
        rewrite_fun_aux func.body (count + 1) ((func.arg, func.argty, false)::args)
          (fun e -> cont e)
    | _ ->
      let bind_dummy_vars e =
        args
        |> List.filter (fun (_,_,b) -> not b)
        |> List.fold_left
          (fun acc (arg, argty, _) ->
             aexp
               (elet
                  arg
                  (aexp (e_val (Generators.default_value (oget argty)), argty, e.espan))
                  acc,
                acc.ety,
                acc.espan)
          )
          e
      in
      let finish = cont % (add_dummy_arg args_to_add elts_to_keep) % InterpPartialFull.interp_partial in
      match e.ety with
      | Some TBool -> (* This is the assert function. Return the input assert body *)
        assertion
        |> bind_dummy_vars
        |> finish
      | _ ->
        (* Not the assert function. Replace the input arguments with dummy variables
           and extract only the relevant elements of the result. *)

        (* Pattern that we match the result of the original function with in order
           to extract the relevant elements *)
        let pat =
          List.mapi
            (fun n _ -> if IntSet.mem n elts_to_keep then PVar (Var.fresh "SlicingVar") else PWild)
            attr_tys
        in
        let final_vars =
          List.filter_map (function | PVar v -> Some v | _ -> None) pat
        in
        (* The types of the elements of the attribute after slicing *)
        let sliced_attr_tys =
          List.filteri (fun n _ -> IntSet.mem n elts_to_keep) attr_tys
        in
        (* The actual tuple expression that the overall function returns *)
        let final_output =
          aexp
            ((etuple (List.rev_map2 (fun v ty -> aexp (evar v, Some ty, e.espan)) final_vars sliced_attr_tys)),
             Some (TTuple sliced_attr_tys),
             e.espan)
        in
        let final_match =
          ematch
            (bind_dummy_vars e)
            (addBranch (PTuple pat) final_output emptyBranch)
        in
        (aexp (final_match, Some (TTuple sliced_attr_tys), e.espan))
        |> finish
  in
  rewrite_fun_aux f 0 [] (fun e -> e)
;;

let map_back_val old_aty elements v =
  let old_aty_elts, v_elts =
    match old_aty, v.v with
    | TTuple tlst, VTuple vlst-> tlst, vlst
    | _ -> failwith "impossible"
  in
  let count = ref (-1) in
  (* Turn the smaller tuple (v) into a larger tuple of type old_aty elts by
     filling in every element we sliced out with a dummy value, and every
     element we didn't slice out with the corresponding element of v *)
  let new_val_elts =
    List.mapi
      (fun i ty ->
         if IntSet.mem i elements
         then (incr count; List.nth v_elts !count)
         else Generators.default_value ty)
      old_aty_elts
  in
  avalue (vtuple new_val_elts, Some old_aty, v.vspan)
;;

let map_back old_aty elements (sol : Solution.t) =
  let mask_type = Solution.mask_type_ty old_aty in
  let _, some_label = AdjGraph.VertexMap.choose sol.labels in
  {
    sol with
    labels = AdjGraph.VertexMap.map (map_back_val old_aty elements) sol.labels;
    (* Take advantage of the fact that the default bool value is false, and the
       values we want to mask are precisely those which use a default value *)
    mask = Some (map_back_val mask_type elements (Solution.value_to_mask some_label));
  }
;;

(* Create a new network whose attribute is a tuple whose elements correspond
   to those indicated by the IntSet.t, and which has asn as the body of
   its assert function. *)
let slice (net : Syntax.network) (asn_slice : exp) (elements : IntSet.t) =
  let slice_fun = rewrite_fun (net.attr_type) elements asn_slice in
  let sliced_init = slice_fun 1 (* First arg is node *) 0 net.init in
  let sliced_trans = slice_fun 2 (* First two args are edge nodes *) 1 net.trans in
  let sliced_merge = slice_fun 1 (* First arg is node *) 2 net.merge in
  let sliced_assert = slice_fun 1 (* First arg is node *) 1 (net.assertion |> oget) in
  let sliced_aty =
    match net.attr_type with
    | TTuple lst -> TTuple (List.filteri (fun i _ -> IntSet.mem i elements) lst)
    | _ -> failwith "impossible"
  in
  let sliced_net, cleanup_map_back =
    {net with attr_type=sliced_aty;
              init=sliced_init;
              trans=sliced_trans;
              merge=sliced_merge;
              assertion=Some(sliced_assert)}
    |> CleanupTuples.cleanup_net
  in
  sliced_net, (map_back net.attr_type elements) % cleanup_map_back
;;

let slice_network (net : Syntax.network) : (Syntax.network * (Solution.t -> Solution.t)) list =
  let attr_deps = attribute_dependencies net in
  let assert_deps = assert_dependencies net in
  let assert_deps_transitive =
    List.map
      (fun (e, immdeps) ->
         e,
         immdeps
         |> IntSet.elements
         |> List.map (fun k -> IntMap.find k attr_deps)
         |> List.fold_left IntSet.union immdeps
      )
      assert_deps
  in
  List.map (fun (a,es) -> slice net a es) assert_deps_transitive
