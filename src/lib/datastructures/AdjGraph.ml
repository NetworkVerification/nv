open Graph
open Nv_utils.PrimitiveCollections

(*** Module definitions ***)

module Vertex = struct
  type t = int [@@deriving eq, ord] (* Really should be Syntax.node, but that causes a dependency loop *)

  (* let compare = Stdlib.compare *)
  (* let equal a b = compare a b = 0 *)
  let hash = Hashtbl.hash
  let to_string = string_of_int
end

include Persistent.Digraph.Concrete (Vertex)

module Edge = struct
  include E

  let equal a b = compare a b = 0
  let to_string e =
    Printf.sprintf "%s~%s" (Vertex.to_string (src e)) (Vertex.to_string (dst e))
  ;;
end

module VertexMap = BetterMap.Make (Vertex)
module VertexSet = BetterSet.Make (Vertex)
module VertexSetSet = BetterSet.Make (VertexSet)
module VertexSetMap = BetterMap.Make (VertexSet)
module EdgeMap = BetterMap.Make (Edge)
module EdgeSet = BetterSet.Make (Edge)

module Labelled (E: Graph.Sig.ORDERED_TYPE_DFT) = struct
  include Graph.Persistent.Digraph.ConcreteLabeled(Vertex)(E)
end

(*** Printing ***)

let to_string g =
  Printf.sprintf
    "Vertices: {%s}\nEdges: {%s}"
    (fold_vertex (fun v acc -> acc ^ Vertex.to_string v ^ ";") g "")
    (fold_edges_e (fun e acc -> acc ^ Edge.to_string e ^ ";") g "")
;;

(*** Vertex/Edge Utilities ***)

let vertices (g : t) = List.rev (fold_vertex List.cons g [])
let edges (g : t) = BatList.rev (fold_edges_e List.cons g [])

(*** Graph Creation **)

(** Add all the vertices in the list to the given graph. *)
let add_vertices vs g = List.fold_left add_vertex g vs

(** Add all the edges in the list to the given graph. *)
let add_edges (es : (Vertex.t * Vertex.t) list) g : t =
  BatList.fold_left add_edge_e g es
;;

module DrawableGraph = struct
  let graph_dot_file =
    let counter = ref (-1) in
    fun (k : int) (file : string) ->
      incr counter;
      file ^ "-" ^ string_of_int k ^ "-" ^ string_of_int !counter
  ;;

  module G = Graph.Persistent.Digraph.Concrete (Vertex)

  module Dot = Graph.Graphviz.Dot (struct
    include G

    let edge_attributes _ = [`Color 3711; `Dir `None]
    let default_edge_attributes _ = []
    let get_subgraph _ = None

    let vertex_attributes v =
      let label = Vertex.to_string v in
      [`Shape `Circle; `Label label; `Fontsize 11]
    ;;

    let vertex_name v = Vertex.to_string v
    let default_vertex_attributes _ = []

    let graph_attributes _ =
      [`Center true; `Nodesep 0.45; `Ranksep 0.45; `Size (82.67, 62.42)]
    ;;
  end)

  let drawGraph (g : t) (dotfile : string) =
    let chan = open_out (dotfile ^ ".dot") in
    Dot.output_graph chan g;
    let _ = Sys.command ("dot -Tjpg " ^ dotfile ^ ".dot -o " ^ dotfile ^ ".jpg") in
    close_out chan
  ;;
end
