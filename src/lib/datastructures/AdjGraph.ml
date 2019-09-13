open Graph
open Nv_utils.PrimitiveCollections

(*** Module definitions ***)

module Vertex = struct
  type t = int (* Really should be Syntax.node, but that causes a dependency loop *)

  let compare = Pervasives.compare
  let equal = (fun a b -> compare a b = 0)
  let hash = Hashtbl.hash
  let to_string = string_of_int
end

include Persistent.Digraph.Concrete(Vertex)

module Edge = struct
  include E
  let to_string e =
    Printf.sprintf "%s~%s" (Vertex.to_string (src e)) (Vertex.to_string (dst e))
end

module VertexMap = BetterMap.Make(Vertex)
module VertexSet = BetterSet.Make(Vertex)
module VertexSetSet = BetterSet.Make(VertexSet)
module VertexSetMap = BetterMap.Make(VertexSet)
module EdgeMap = BetterMap.Make(Edge)
module EdgeSet = BetterSet.Make(Edge)

(*** Printing ***)

let to_string g =
  Printf.sprintf "Vertices: {%s}\nEdges: {%s}"
    (fold_vertex (fun v acc -> acc ^ Vertex.to_string v ^ ";") g "")
    (fold_edges_e (fun e acc -> acc ^ Edge.to_string e ^ ";") g "")

(*** Vertex/Edge Utilities ***)

let fold_vertices (f: Vertex.t -> 'a -> 'a) (i : int) (acc: 'a) : 'a =
  let rec loop j =
    if i = j then acc
    else f j (loop (j + 1))
  in
  loop 0

let vertices (g: t) = fold_vertex VertexSet.add g VertexSet.empty

let edges (g: t) = BatList.rev (fold_edges_e List.cons g [])

(*** Graph Creation **)

let create n = fold_vertices (fun v g -> add_vertex g v) n empty

let of_edges (l: (Vertex.t * Vertex.t) list) : t =
  BatList.fold_left (fun g e -> add_edge_e g e) empty l

(*** Min-cut computation ***)

(* FIXME: ocamlgraph apparently has implmentations of all these functions,
   even including min-cut. However, apparently they were giving different
   results. We should look into that to make sure the differences are legitimate,
   then remove this and switch to ocamlgraph's min-cut. *)

(* return an EdgeMap where each edge key has a map of edge neighbors *)
let edges_map (g: t) (f: Edge.t -> 'a) : 'a EdgeMap.t =
  fold_edges_e (fun e a -> EdgeMap.add e (f e) a) g EdgeMap.empty


let bfs (g: t) (rg : int EdgeMap.t) (s: Vertex.t) (t: Vertex.t) =
  let visited = VertexSet.singleton s in
  let path = VertexMap.empty |> VertexMap.add s s in
  let q = Queue.create () in
  Queue.push s q;
  let rec loop path visited =
    if not (Queue.is_empty q) then
      begin
        let u = Queue.pop q in
        let vs = succ g u in
        let visited, path =
          BatList.fold_left (fun (accvs, accpath) (v: Vertex.t) ->
              if ((not (VertexSet.mem v accvs)) && (EdgeMap.find (u,v) rg > 0)) then
                begin
                  Queue.push v q;
                  (VertexSet.add v accvs, VertexMap.add v u accpath)
                end
              else
                (accvs, accpath)) (visited, path) vs
        in
        loop path visited
      end
    else (path, visited)
  in
  let path, visited = loop path visited in
  (VertexSet.mem t visited, path)

let dfs (g: t) (rg : int EdgeMap.t) (s: Vertex.t) =
  let rec loop u visited =
    let visited = VertexSet.add u visited in
    let vs = succ g u in
    BatList.fold_left (fun accvs v ->
        if ((EdgeMap.find (u,v) rg > 0) && (not (VertexSet.mem v accvs))) then
          loop v accvs
        else accvs) visited vs
  in
  loop s VertexSet.empty

let min_cut g s t =
  let rg = ref (edges_map g (fun _ -> 1)) in
  let rec loop reach path =
    if reach then
      begin
        let path_flow = ref max_int in
        let u = ref t in
        while (!u <> s) do
          let v = !u in
          u := VertexMap.find !u path;
          path_flow := min !path_flow (EdgeMap.find (!u, v) !rg)
        done;
        u := t;
        while (!u <> s) do
          let v = !u in (*current node*)
          u := VertexMap.find !u path; (*parent node*)
          rg := EdgeMap.modify (!u, v) (fun n -> n - !path_flow) !rg;
          rg := EdgeMap.modify (v, !u) (fun n -> n + !path_flow) !rg
        done;
        let reach, path = bfs g !rg s t in
        loop reach path
      end
  in
  let reach, path = bfs g !rg s t in
  loop reach path;

  let visited = dfs g !rg s in
  let cut = EdgeMap.fold (fun (u,v) _ cutset ->
      if (VertexSet.mem u visited) && (not (VertexSet.mem v visited)) then
        (EdgeSet.add (u,v) cutset)
      else
        cutset) !rg EdgeSet.empty
  in
  (cut, visited, VertexSet.diff (vertices g) visited)

module DrawableGraph = struct

  let graph_dot_file =
    let counter = ref (-1) in
    fun (k: int) (file: string) ->
      incr counter;
      file ^ "-" ^ (string_of_int k) ^ "-" ^ (string_of_int !counter)

  module G = Graph.Persistent.Digraph.Concrete (Vertex)

  module Dot = Graph.Graphviz.Dot(struct
      include G
      let edge_attributes _ =
        [`Color 3711; `Dir `None]
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_attributes v =
        let label = Vertex.to_string v in
        [`Shape `Circle; `Label label; `Fontsize 11;]
      let vertex_name v = Vertex.to_string v
      let default_vertex_attributes _ = []
      let graph_attributes _ = [`Center true; `Nodesep 0.45;
                                `Ranksep 0.45; `Size (82.67, 62.42)]
    end)

  let drawGraph (g: t) (dotfile: string)  =
    let chan = open_out (dotfile ^ ".dot") in
    Dot.output_graph chan g;
    let _ = Sys.command ("dot -Tjpg " ^ dotfile ^
                         ".dot -o " ^ dotfile ^ ".jpg") in
    close_out chan
end
