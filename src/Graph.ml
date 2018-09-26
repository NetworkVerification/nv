open Unsigned

module Vertex = struct
  type t = UInt32.t

  let printVertex i =
    Printf.sprintf "%d" (UInt32.to_int i)

  let compare = UInt32.compare
end

module VertexMap = Map.Make (Vertex)
module VertexSet = Set.Make(Vertex)

module Edge = struct
  type t = Vertex.t * Vertex.t

  let compare (v1, w1) (v2, w2) =
    if UInt32.compare v1 v2 != 0 then UInt32.compare v1 v2
    else UInt32.compare w1 w2
end

module EdgeSet = Set.Make(Edge)
            
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
    (fun s (k, v) -> UInt32.to_string k ^ ":" ^ elem_to_string v ^ s)
    "" kvs

let print_vertex_map elem_to_string m =
  VertexMap.iter
    (fun k v ->
      print_endline (UInt32.to_string k ^ ":" ^ elem_to_string v) )
    m

(* a graph as ajacency list * # of vertices *)
type t = Vertex.t list VertexMap.t * UInt32.t

(* create a graph with i vertices *)
let create i = (VertexMap.empty, i)

(* vertices and edges *)
let num_vertices (m, i) = i

(* let get_vertices (m, i) = *)
(*   VertexMap.fold (fun k _ acc -> VertexSet.add k acc) *)
(*                  m VertexSet.empty *)

(* get_vertices now returns all the vertices in the graph, not just
   the ones that have an outgoing edge.*)
let get_vertices (m, i) =
  let rec loop j =
    if i = j then VertexSet.empty
    else VertexSet.add j (loop (UInt32.add j UInt32.one))
  in
  loop UInt32.zero

let edges (m, i) =
  let my_edges v neighbors =
    List.fold_left (fun a w -> (v, w) :: a) [] neighbors
  in
  List.rev
    (VertexMap.fold
       (fun v neighbors a -> my_edges v neighbors @ a)
       m [])

(* a vertex v does not belong to a graph's set of vertices *)
exception BadVertex of UInt32.t

let good_vertex (m, i) v =
  if UInt32.compare v UInt32.zero < 0 || not (UInt32.compare i v > 0)
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
        List.filter (fun a -> not (UInt32.compare a w = 0)) ns
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
  Printf.printf "%d\n" (UInt32.to_int (num_vertices g)) ;
  List.iter
    (fun (v, w) ->
      Printf.printf "%d -> %d\n" (UInt32.to_int v) (UInt32.to_int w)
      )
    (edges g)

let to_string g =
  let b = Buffer.create 80 in
  let rec add_edges es =
    match es with
    | [] -> ()
    | (v, w) :: rest ->
        Buffer.add_string b
          (Printf.sprintf "%d -> %d\n" (UInt32.to_int v)
             (UInt32.to_int w)) ;
        add_edges rest
  in
  Buffer.add_string b (UInt32.to_string (num_vertices g) ^ "\n") ;
  add_edges (edges g) ;
  Buffer.contents b
