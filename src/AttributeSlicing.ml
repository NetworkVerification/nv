open Batteries
open OCamlUtils
open Syntax
open Collections
open Dependency

(* Maps attribute elements to the set of other elements they depend on *)
type attrdepmap = IntSet.t IntMap.t

(* Maps function arguments to the attribute element they correspond to *)
type argmap = int IntMap.t

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
  let body = InterpPartialFull.interp_partial body in
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

let slice (net : Syntax.network) : Syntax.network list =
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
  print_endline @@ "Transitive:\n" ^ BatString.concat "\n" @@
  List.map (fun (e, s) -> Printf.sprintf "%s:{ %s }" (Printing.exp_to_string e)
               (Collections.IntSet.fold
                  (fun n acc ->
                     Printf.sprintf "%s; %d" acc n) s "")) @@
  assert_deps_transitive;
  []
