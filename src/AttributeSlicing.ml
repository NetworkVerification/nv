open Batteries
open OCamlUtils
open Syntax
open Collections
open Dependency

(* Maps attribute elements to the set of other elements they depend on *)
type attrdepmap = IntSet.t IntMap.t

(* Maps function arguments to the attribute element they correspond to *)
type argmap = int IntMap.t

(* Given a network which has been fully transformed (i.e. satisfies the
   requirements listed in Dependency.ml), and whose attribute type is a tuple,
   this function determines which elements of the attribute depend on which other
   elements.
   The result maps each index in the tuple to the set of indices that it
   depends on; note that an index may depend on itself. *)
let attribute_dependencies (net : Syntax.network) : attrdepmap =
  let attr_size = (* Number of elements in the attribute *)
    match net.attr_type with
    | TTuple lst -> List.length lst
    | _ -> failwith "compute_attribute_dependencies: Attribute must have tuple type"
  in
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

  let extract depresult =
    match depresult with
    | DTuple lst ->
      begin
        List.map (function DBase s -> s | _ -> failwith "impossible") lst
      end
    | _ -> failwith "impossible"
  in
  (* Given a map of argument numbers to attribute elements and dependencies of
     attribute elements on arguments, construct the dependencies of attribute
     elements on each other. *)
  let process_dependencies argmap deps =
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
  in
  let init_deps = compute_dependencies_func net.init |> extract |> process_dependencies init_argmap in
  let trans_deps = compute_dependencies_func net.trans |> extract |> process_dependencies trans_argmap in
  let merge_deps = compute_dependencies_func net.merge |> extract |> process_dependencies merge_argmap in
  let all_deps =
    OCamlUtils.map3i
      (fun n a b c -> n, IntSet.union a (IntSet.union b c))
      init_deps trans_deps merge_deps
  in
  List.fold_left (fun acc (i, s) -> IntMap.add i s acc) IntMap.empty all_deps
