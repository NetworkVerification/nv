open Unsigned
open Syntax

type srp = {
  graph : Graph.t;
  env : Interp.Env.t;
  trans : func;
  merge : func;
}

(******************)
(* SRP Simulation *)
(******************)

exception Simulation_error of string 
let error s = raise (Simulation_error s)

(* Simulation States *)
(* Invariant: All valid graph vertices are associated with an attribute initially (and always) *) 
type state = value Graph.VertexMap.t

(* initial_state g [(x1,a1),...] d n creates a state s where 
    vertices xi have attributes ai and all other vertices have attribute d *)
let create_state g init default =
  let rec default_all i m =
    if UInt32.compare i (Graph.num_vertices g) < 0 then
      default_all (UInt32.succ i) (Graph.VertexMap.add i default m)
    else
      m
  in
  let rec initialize init m =
    match init with
	[] -> m
      | (n,a)::init' ->
	Graph.good_vertex g n;
	Graph.VertexMap.add n a m
  in
  initialize init (default_all UInt32.zero Graph.VertexMap.empty)    
    
let state_to_string s = Graph.vertex_map_to_string Printing.value_to_string s

let print_state s = Graph.print_vertex_map Printing.value_to_string s

let get_attribute v s =
  let find_opt v m = try Some (Graph.VertexMap.find v m) with Not_found -> None in
  match find_opt v s with
    | None -> error ("no attribute at vertex " ^ UInt32.to_string v)
    | Some a -> a
  
let simulate_step {graph=g;env=env;trans=trans;merge=merge} s x =
  let do_neighbor initial_attribute (s,todo) n =
    let neighbor = VUInt32 n in
    let origin = VUInt32 x in
    let edge = VTuple [origin; neighbor] in
    let n_incoming_attribute = Interp.apply env trans [edge; initial_attribute] in
    let n_old_attribute = get_attribute n s in
    let n_new_attribute = Interp.apply env merge [neighbor; n_old_attribute; n_incoming_attribute] in
    if Syntax.equal_val n_old_attribute n_new_attribute then
      (s,todo)
    else
      (Graph.VertexMap.add n n_new_attribute s, n::todo)
  in
  let initial_attribute = get_attribute x s in
  let neighbors = Graph.neighbors g x in
  List.fold_left (do_neighbor initial_attribute) (s,[]) neighbors

(* simulate srp s q simulates srp starting with initial s and queue q *)
let rec simulate_init srp s q =
  match q with
      [] -> s
    | next::rest ->
      let (s', more) = simulate_step srp s next in
      simulate_init srp s' (more @ rest)
	
(* simulate for at most k steps *)    
let simulate_bound srp s q k =
  let rec loop s q k =
    if k <= 0 then
      s
    else
      match q with
	  [] -> s
	| next::rest ->
	  let (s', more) = simulate_step srp s next in
	  loop s' (more @ rest) (k-1)
  in
  loop s q k
	
(* simulate for at most k steps *)    
let simulate srp init default =
  let rec loop s q =
      match q with
	  [] -> s
	| next::rest ->
	  let (s', more) = simulate_step srp s next in
	  loop s' (more @ rest)
  in
  let q = List.map (fun (v,a) -> v) init in
  loop (create_state srp.graph init default) q
