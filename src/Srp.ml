open Unsigned
open Syntax

type srp = {
  graph : Graph.t;
  trans : Syntax.closure;
  merge : Syntax.closure;
}

(******************)
(* SRP Simulation *)
(******************)

exception Simulation_error of string 
let error s = raise (Simulation_error s)

(* Simulation States *)
(* Solution Invariant: All valid graph vertices are associated with an attribute initially (and always) *) 
type solution = value Graph.VertexMap.t
type queue = Graph.Vertex.t list
type state = solution * queue


    (*
(* initial_state node_num [(x1,a1),...] d creates a state s where 
    vertices xi have attributes ai and all other vertices have attribute d *)
let create_state node_num init default =
  let good_node n = (UInt32.compare UInt32.zero n <= 0) && (UInt32.compare n node_num < 0) in
  let rec default_all i m =
    if good_node i then
      default_all (UInt32.succ i) (Graph.VertexMap.add i default m)
    else
      m
  in
  let rec initialize init (m,q) =
    match init with
	[] -> (m,q)
      | (n,a)::init' ->
	if good_node n then
	  initialize init' (Graph.VertexMap.add n a m, n::q)
	else
	  error (Printf.sprintf "attempting to initialize node %d for simulation but graph only has %d nodes"
		   (UInt32.to_int n) (UInt32.to_int node_num))
  in
  initialize init ((default_all UInt32.zero Graph.VertexMap.empty), [])

  *)

let create_state n cl =
  let rec loop n q m =
    if UInt32.compare n UInt32.zero > 0 then
      let next_n = UInt32.pred n in
      let next_q = next_n::q in
      let next_m = Graph.VertexMap.add next_n (Interp.interp_closure cl [VUInt32 next_n]) m in
      loop next_n next_q next_m
    else
      (m,q)
  in
  loop n [] Graph.VertexMap.empty

type info = {
  mutable env : Syntax.value Env.t;                  (* environment *)
  mutable m : Syntax.closure option;                 (* merge *)
  mutable t : Syntax.closure option;                 (* trans *)
  mutable ns : UInt32.t option;                      (* nodes *)
  mutable es : (UInt32.t * UInt32.t) list option;    (* edges *)
  mutable init : Syntax.closure option;              (* initial state *)
}
    
let declarations_to_state ds =
  let info = {
    env=Env.empty;
    m=None;
    t=None;
    ns=None;
    es=None;
    init=None;
  } in
  let if_none opt f msg =
    match opt with
      | None -> f () 
      | Some f -> error msg
  in
  let process_declaration d =
    match d with
      | DLet (x,e) ->
	let env = info.env in
	let v = Interp.interp_env env e in
	info.env <- Env.update env x v
	  
      | DMerge e ->
	let get_merge () =
	  match Interp.interp_env info.env e with
	    | VClosure cl -> info.m <- Some cl
	    | _ -> error "merge was not evaluated to a closure"
	in
	if_none info.m get_merge "multiple merge functions"

      | DTrans e ->
	let get_trans () =
	  match Interp.interp_env info.env e with
	    | VClosure cl -> info.t <- Some cl
	    | _ -> error "trans was not evaluated to a closure"
	in
	if_none info.t get_trans "multiple trans functions"

      | DNodes n ->
	if_none info.ns (fun () -> info.ns <- Some n) "multiple nodes declarations"

      | DEdges es ->
	if_none info.es (fun () -> info.es <- Some es) "multiple edges declarations"

      | DInit e ->
	let get_initializer () =
	  match Interp.interp_env info.env e with
	    | VClosure cl -> info.init <- Some cl
	    | _ -> error "init was not evaluated to a closure"
	in
	if_none info.init get_initializer "multiple initialization declarations"
  in
  List.iter process_declaration ds;
  match info with
    | {env=_;
       m=Some mf;
       t=Some tf;
       ns=Some n;
       es=Some es;
       init=Some cl;
      } -> let srp = {graph=Graph.add_edges (Graph.create n) es;
		      trans=tf;
		      merge=mf;} in
	   let state = create_state n cl in
	   (srp, state)
	     
    | {env=_;
       m=None;
       t=_;
       ns=_;
       es=_;
       init=_;
      } -> error "missing merge function"

    | {env=_;
       m=_;
       t=None;
       ns=_;
       es=_;
       init=_;
      } -> error "missing trans function"

    | {env=_;
       m=_;
       t=_;
       ns=None;
       es=_;
       init=_;
      } -> error "missing nodes declaration"

    | {env=_;
       m=_;
       t=_;
       ns=_;
       es=None;
       init=_;
      } -> error "missing edges declaration"

    | {env=_;
       m=_;
       t=_;
       ns=_;
       es=_;
       init=None;
      } -> error "missing init declaration"
    
let solution_to_string s = Graph.vertex_map_to_string Printing.value_to_string s

let print_solution s = Graph.print_vertex_map Printing.value_to_string s

let get_attribute v s =
  let find_opt v m = try Some (Graph.VertexMap.find v m) with Not_found -> None in
  match find_opt v s with
    | None -> error ("no attribute at vertex " ^ UInt32.to_string v)
    | Some a -> a
  
let simulate_step {graph=g;trans=trans;merge=merge} s x =
  let do_neighbor initial_attribute (s,todo) n =
    let neighbor = VUInt32 n in
    let origin = VUInt32 x in
    let edge = VTuple [origin; neighbor] in
    let n_incoming_attribute = Interp.interp_closure trans [edge; initial_attribute] in
    let n_old_attribute = get_attribute n s in
    let n_new_attribute = Interp.interp_closure merge [neighbor; n_old_attribute; n_incoming_attribute] in
    if Interp.equal_val n_old_attribute n_new_attribute then
      (s,todo)
    else
      (Graph.VertexMap.add n n_new_attribute s, n::todo)
  in
  let initial_attribute = get_attribute x s in
  let neighbors = Graph.neighbors g x in
  List.fold_left (do_neighbor initial_attribute) (s,[]) neighbors

(* simulate srp s q simulates srp starting with initial state (s,q) *)
let rec simulate_init srp (s,q) =
  match q with
      [] -> s
    | next::rest ->
      let (s', more) = simulate_step srp s next in
      simulate_init srp (s',(more @ rest))
	
(* simulate for at most k steps *)    
let simulate_init_bound srp (s,q) k =
  let rec loop s q k =
    if k <= 0 then
      (s,q)
    else
      match q with
	  [] -> (s,[])
	| next::rest ->
	  let (s', more) = simulate_step srp s next in
	  loop s' (more @ rest) (k-1)
  in
  loop s q k

let simulate_declarations ds =
  let (srp,state) = declarations_to_state ds in
  simulate_init srp state

let simulate_declarations_bound ds k =
  let (srp,state) = declarations_to_state ds in
  simulate_init_bound srp state k
