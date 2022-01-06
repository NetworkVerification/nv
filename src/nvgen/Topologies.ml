(* Utilities for generating topologies from scratch. *)
open Graph
open Nv_datastructures
open Nv_lang.Syntax
open Batteries

type topology =
  (* A fattree topology of n _pods_ (not nodes). *)
  | Fattree of int
  (* A full mesh topology of n nodes. *)
  | FullMesh of int
  (* A ring topology of n nodes. *)
  | Ring of int
  (* A star topology of n nodes, with node 0 in the center. *)
  | Star of int
[@@deriving show]

let star n = if n < 1 then raise (Failure "star must have at least 1 node") else Star n
let ring n = Ring n
let full_mesh n = FullMesh n

let parse_string s =
  let regexp = Str.regexp "\\([a-z]*\\)\\([0-9]*\\)" in
  if Str.string_match regexp s 0
  then (
    let top = Str.matched_group 1 s in
    let x = int_of_string (Str.matched_group 2 s) in
    (match top with
    | "star" -> Some (star x)
    | "mesh" -> Some (full_mesh x)
    | "ring" -> Some (ring x)
    | _ -> None))
  else None
;;

type fatLevel =
  | Core
  | Aggregation
  | Edge

let construct top : AdjGraph.t =
  match top with
  | FullMesh n ->
    let srcs = Nv_utils.OCamlUtils.list_seq n in
    let edges = List.cartesian_product srcs srcs in
    (* delete self-loops *)
    let lf_edges = List.filter (fun (u,v) -> u != v) edges in
    AdjGraph.of_edges lf_edges
  | Ring n ->
    let srcs = Nv_utils.OCamlUtils.list_seq n in
    let edges = List.map (fun x -> x, (x + 1) mod n) srcs in
    AdjGraph.of_edges edges
  | Star n ->
    let srcs = Nv_utils.OCamlUtils.list_seq n in
    let edges = List.map (fun n -> List.hd srcs, n) (List.tl srcs) in
    AdjGraph.of_edges edges
  | Fattree _k -> failwith "todo"
;;

let to_decls g = [DNodes (AdjGraph.nb_vertex g); DEdges (AdjGraph.edges g)]
