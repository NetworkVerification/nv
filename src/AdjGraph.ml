module Vertex = struct
  type t = Integer.t

  let printVertex i =
    Printf.sprintf "%d" (Integer.to_int i)

  let compare = Integer.compare
  let equal = Integer.equal
  let hash = Hashtbl.hash 
end

module VertexMap = BatMap.Make (Vertex)
module VertexSet = BatSet.Make(Vertex)
module VertexSetSet : BatSet.S with type elt = VertexSet.t = BatSet.Make(VertexSet)
module VertexSetMap : BatMap.S with type key = VertexSet.t = BatMap.Make(VertexSet)

module Edge = struct
  type t = Vertex.t * Vertex.t

  let compare (v1, w1) (v2, w2) =
    if Integer.compare v1 v2 <> 0 then Integer.compare v1 v2
    else Integer.compare w1 w2
end

let printEdge (e : Edge.t) =
  Printf.sprintf "<%d,%d>\n" (Integer.to_int (fst e)) (Integer.to_int (snd e)); 
            
module EdgeSet = BatSet.Make(Edge)
module EdgeMap = BatMap.Make(Edge)
            
(* OCaml 4.06 contains find_opt and update built in. upgrade compiler. *)
let find_opt v m =
  try Some (VertexMap.find v m) with Not_found -> None

let update v f m =
  match f (find_opt v m) with
  | None -> VertexMap.remove v m
  | Some ns -> VertexMap.add v ns m

let vertex_map_to_string elem_to_string m =
  let kvs = VertexMap.fold (fun k v l -> (k, v) :: l) m [] in
  List.fold_left
    (fun s (k, v) -> Integer.to_string k ^ ":" ^ elem_to_string v ^ s)
    "" kvs

let print_vertex_map elem_to_string m =
  VertexMap.iter
    (fun k v ->
      print_endline (Integer.to_string k ^ ":" ^ elem_to_string v) )
    m

(* a graph as ajacency list * # of vertices *)
type t = Vertex.t list VertexMap.t * Integer.t

(* create a graph with i vertices *)
let create i = (VertexMap.empty, i)

(* vertices and edges *)
let num_vertices (m, i) = i

(* let get_vertices (m, i) = *)
(*   VertexMap.fold (fun k _ acc -> VertexSet.add k acc) *)
(*                  m VertexSet.empty *)

let fold_vertices (f: Vertex.t -> 'a -> 'a) i (acc: 'a) : 'a =
  let rec loop j =
    if i = j then acc
    else f j (loop (Integer.succ j))
  in
  loop (Integer.create ~value:0 ~size:32)

                        
(* get_vertices now returns all the vertices in the graph, not just
   the ones that have an outgoing edge.*)
let get_vertices (m, i) =
  let rec loop j =
    if i = j then VertexSet.empty
    else VertexSet.add j (loop (Integer.succ j))
  in
  loop (Integer.create ~value:0 ~size:32)

let edges (m, i) =
  let my_edges v neighbors =
    List.fold_left (fun a w -> (v, w) :: a) [] neighbors
  in
  List.rev
    (VertexMap.fold
       (fun v neighbors a -> my_edges v neighbors @ a)
       m [])

(* a vertex v does not belong to a graph's set of vertices *)
exception BadVertex of Integer.t

let good_vertex (m, i) v =
  if Integer.compare v (Integer.of_int 0) < 0 || not (Integer.compare i v > 0)
  then raise (BadVertex v)

let good_graph g =
  List.iter
    (fun (v, w) -> good_vertex g v ; good_vertex g w)
    (edges g)

(* add_edge g e adds directed edge e to g *)
let add_edge (m, i) (v, w) =
  good_vertex (m, i) v ;
  good_vertex (m, i) w ;
  let f adj =
    match adj with
    | None -> Some [w]
    | Some ns -> if List.mem w ns then adj else Some (w :: ns)
  in
  (update v f m, i)

let rec add_edges g edges =
  match edges with
  | [] -> g
  | e :: edges -> add_edges (add_edge g e) edges

(* add_edge g e adds directed edge e to g *)
let remove_edge (m, i) (v, w) =
  good_vertex (m, i) v ;
  good_vertex (m, i) w ;
  let f adj =
    match adj with
    | None -> adj
    | Some ns ->
      match
        List.filter (fun a -> not (Integer.compare a w = 0)) ns
      with
      | [] -> None
      | ns' -> Some ns'
  in
  (update v f m, i)

(* neighbors of v in g *)
let neighbors (m, i) v =
  good_vertex (m, i) v ;
  match find_opt v m with None -> [] | Some ns -> ns

let print g =
  Printf.printf "%d\n" (Integer.to_int (num_vertices g)) ;
  List.iter
    (fun (v, w) ->
      Printf.printf "%d -> %d\n" (Integer.to_int v) (Integer.to_int w)
      )
    (edges g)

let to_string g =
  let b = Buffer.create 80 in
  let rec add_edges es =
    match es with
    | [] -> ()
    | (v, w) :: rest ->
        Buffer.add_string b
          (Printf.sprintf "%d -> %d\n" (Integer.to_int v)
             (Integer.to_int w)) ;
        add_edges rest
  in
  Buffer.add_string b (Integer.to_string (num_vertices g) ^ "\n") ;
  add_edges (edges g) ;
  Buffer.contents b

open Graph

module BoolOrdered = struct
  type t = bool
  let default = false
  let compare = compare
end

module DrawableGraph = struct

  let graph_dot_file =
    let counter = ref (-1) in
    fun (k: int) (file: string) ->
    incr counter;
    file ^ "-" ^ (string_of_int k) ^ "-" ^ (string_of_int !counter)
  
  module G = Graph.Persistent.Graph.Concrete (Vertex)
           
  let createGraph ((m,i): t)  =
    VertexMap.fold (fun u es acc ->
        List.fold_left (fun acc v ->
            G.add_edge_e acc (G.E.create u () v)) acc es) m G.empty

  module Dot = Graph.Graphviz.Dot(struct
                   include G
                   let edge_attributes e =
                       [`Color 3711; `Dir `None]
                   let default_edge_attributes _ = []
                   let get_subgraph _ = None
                   let vertex_attributes v =
                     let label = Vertex.printVertex v in
                     [`Shape `Circle; `Label label; `Fontsize 11;]
                   let vertex_name v = string_of_int (Integer.to_int v)
                   let default_vertex_attributes _ = []
                   let graph_attributes _ = [`Center true; `Nodesep 0.45; 
                                             `Ranksep 0.45; `Size (82.67, 62.42)]
                 end)

  let drawGraph (g: t) (dotfile: string)  =
    let chan = open_out (dotfile ^ ".dot") in
    Dot.output_graph chan (createGraph g);
    let _ = Sys.command ("dot -Tjpg " ^ dotfile ^
                           ".dot -o " ^ dotfile ^ ".jpg") in
    close_out chan
end
