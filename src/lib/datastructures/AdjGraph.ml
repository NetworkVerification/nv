open Graph

module Vertex = struct
  type t = int (* Really should be Syntax.node, but that causes a dependency loop *)

  let to_string i =
    Printf.sprintf "%d" i

  let compare = Pervasives.compare
  let equal = (fun a b -> compare a b = 0)
  let hash = Hashtbl.hash
end

include Persistent.Graph.Concrete(Vertex)

module VertexMap = BatMap.Make (Vertex)
module VertexSet = BatSet.Make(Vertex)
module VertexSetSet : BatSet.S with type elt = VertexSet.t = BatSet.Make(VertexSet)
module VertexSetMap : BatMap.S with type key = VertexSet.t = BatMap.Make(VertexSet)

let create_vertices (i: int) =
  let open Batteries in
  (* enumerate ints *)
  let e = 0 -- i in
    BatEnum.fold (fun acc v -> VertexSet.add v acc) VertexSet.empty e

module Edge = E

let printEdge (e : Edge.t) =
  Printf.sprintf "<%d,%d>" (Edge.src e) (Edge.dst e);

module EdgeSet = BatSet.Make(Edge)
module EdgeMap = BatMap.Make(Edge)

let vertex_map_to_string elem_to_string m =
  let kvs = VertexMap.fold (fun k v l -> (k, v) :: l) m [] in
  BatList.fold_left
    (fun s (k, v) -> (Vertex.to_string k) ^ ":" ^ elem_to_string v ^ s)
    "" kvs

let print_vertex_map elem_to_string m =
  VertexMap.iter
    (fun k v ->
      print_endline (Vertex.to_string k ^ ":" ^ elem_to_string v) )
    m

(* vertices and edges *)
let get_vertices (g: t) =
  fold_vertex VertexSet.add g VertexSet.empty

let fold_vertices (f: Vertex.t -> 'a -> 'a) i (acc: 'a) : 'a =
  let rec loop j =
    if i = j then acc
    else f j (loop (j + 1))
  in
  loop 0

let create i =
  fold_vertices (fun v g -> add_vertex g v) i empty

(* a vertex v does not belong to a graph's set of vertices *)
exception BadVertex of Vertex.t

let good_vertex g v = 
  if not (mem_vertex g v)
  then (Printf.printf "bad: %s" (Vertex.to_string v); raise (BadVertex v))

(* out-neighbors of v in g *)
let neighbors = succ

let edges (g: t) =
  BatList.rev
    (fold_edges_e List.cons g [])

let of_edges (l: (Vertex.t * Vertex.t) list) : t =
  let g = empty in
    BatList.fold_left (fun g (u, v) -> add_edge g u v) g l

(* return a VertexMap where each vertex key has a map of edge neighbors *)
let edges_map (g: t) (f: Edge.t -> 'a) =
  (* create an EdgeMap containing all neighbors of u *)
  let my_edges v neighbors a =
    BatList.fold_left (fun a w -> EdgeMap.add (v, w) (f (v, w)) a) a neighbors
  in
  fold_vertex (fun v a -> my_edges v (neighbors g v) a) g EdgeMap.empty

let rec add_edges g edges =
  match edges with
  | [] -> g
  | e :: edges -> add_edges (add_edge_e g e) edges

let good_graph g =
  BatList.iter
    (fun (v, w) -> good_vertex g v ; good_vertex g w)
    (edges g)

let print g =
  Printf.printf "%d\n" (nb_vertex g) ;
  BatList.iter
    (fun (v, w) ->
      Printf.printf "%s -> %s\n" (Vertex.to_string v) (Vertex.to_string w)
      )
    (edges g)

let to_string g =
  let b = Buffer.create 80 in
  let rec add_edges es =
    match es with
    | [] -> ()
    | (v, w) :: rest ->
        Buffer.add_string b
          (Printf.sprintf "%s -> %s\n" (Vertex.to_string v) (Vertex.to_string w)) ;
        add_edges rest
  in
  Buffer.add_string b (string_of_int (nb_vertex g) ^ "\n") ;
  add_edges (edges g) ;
  Buffer.contents b

let bfs (g: t) (rg : int EdgeMap.t) (s: Vertex.t) (t: Vertex.t) =
  let visited = VertexSet.singleton s in
  let path = VertexMap.empty |> VertexMap.add s s in
  let q = Queue.create () in
  Queue.push s q;
  let rec loop path visited =
    if not (Queue.is_empty q) then
      begin
        let u = Queue.pop q in
        let vs = neighbors g u in
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
    let vs = neighbors g u in
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
  (cut, visited, VertexSet.diff (get_vertices g) visited)

module DrawableGraph = struct

  let graph_dot_file =
    let counter = ref (-1) in
    fun (k: int) (file: string) ->
    incr counter;
    file ^ "-" ^ (string_of_int k) ^ "-" ^ (string_of_int !counter)

  module G = Graph.Persistent.Graph.Concrete (Vertex)

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