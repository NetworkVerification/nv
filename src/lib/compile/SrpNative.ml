(** Simulates an SRP compiled to a native OCaml progam *)
open Nv_utils
open Unsigned
open Nv_solution
open Nv_lang
open Nv_datastructures
open Nv_lang.Collections
open Symbolics

(** Type of SRP network *)
module type NATIVE_SRP =
sig
  (** Communication between SRPs and NV *)
  val record_fns: (int * int) -> 'a -> 'b
  val record_cnstrs: int -> 'c
end

(** Simulator signature*)
module type SrpSimulationSig =
sig
  (** Takes as input the attribute type id, the name of the variable storing the solutions,
   ** the init trans and merge functions and computes the solutions.*)
  val simulate_solve: int -> string -> (int -> 'a) -> ((int*int) -> 'a -> 'a)
    -> (int -> 'a -> 'a -> 'a) -> CompileBDDs.t

  (** List of solutions, each entry is the name of the SRP and the *)
  val solved : ((string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list) ref
end

(** To complete the SRPs we add values for the symbolic values and a simulator*)
module type CompleteSRPSig = functor (S:PackedSymbolics) (SIM:SrpSimulationSig) -> NATIVE_SRP

(** Reference to a NATIVE_SRP module *)
let (srp : (module CompleteSRPSig) option ref) = ref None

(** Getter function for [srp]*)
let get_srp () =
  match !srp with
  | Some srp -> srp
  | None -> failwith "No srp loaded"


(******************)
(* SRP Simulator *)
(******************)


module type Topology =
sig
  val graph : AdjGraph.t
end

module SrpSimulation (G:Topology): SrpSimulationSig =
struct

  (* Simulation States *)
  (* Solution Invariant: All valid graph vertices are associated with an
     attribute initially (and always) *)
  type 'a solution = 'a AdjGraph.VertexMap.t

  (* The extended solution of a node includes the route selected + the messages received from each neighbor*)
  type 'a extendedSolution = ('a solution * 'a) AdjGraph.VertexMap.t

  type queue = AdjGraph.Vertex.t QueueSet.queue

  type 'a state = 'a extendedSolution * queue

  let create_state (n : int) init: 'a state =
    let rec loop n (q: queue) m =
      if Pervasives.compare n 0 > 0 then
        let next_n = n - 1 in
        let next_q = QueueSet.add q next_n in
        let init_n = init next_n in
        let next_m =
          AdjGraph.VertexMap.add next_n
            (AdjGraph.VertexMap.singleton next_n init_n, init_n)
            m
        in
        loop next_n next_q next_m
      else (m, q)
    in
    loop n (QueueSet.empty Pervasives.compare) AdjGraph.VertexMap.empty

  exception Require_false

  let get_attribute (v: AdjGraph.VertexMap.key) (s : 'a extendedSolution) =
    match AdjGraph.VertexMap.Exceptionless.find v s with
    | None -> failwith ("no attribute at vertex " ^ string_of_int v)
    | Some a -> a

  let attr_equal = ref (fun _ _ -> true)

  let simulate_step trans merge (s : 'a extendedSolution) (origin : int) =
    let do_neighbor (_, initial_attribute) (s, todo) neighbor =
      let edge = (origin, neighbor) in
      (* Compute the incoming attribute from origin *)
      let n_incoming_attribute = trans edge initial_attribute in
      let (n_received, n_old_attribute) = get_attribute neighbor s in
      match AdjGraph.VertexMap.Exceptionless.find origin n_received with
      | None ->
        (* If this is the first message from this node then add it to the received messages of n*)
        let new_entry = AdjGraph.VertexMap.add origin n_incoming_attribute n_received in
        (*compute new merge and decide whether best route changed and it needs to be propagated*)
        let n_new_attribute = merge neighbor n_old_attribute n_incoming_attribute in
        if (n_old_attribute = n_new_attribute)
        then (AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s, todo)
        else (AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s, neighbor :: todo)
      | Some old_attribute_from_x ->
        (* if n had already received a message from origin then we may need to recompute everything*)
        (* Withdraw route received from origin *)
        let n_received = AdjGraph.VertexMap.remove origin n_received in

        (* Merge the old route from with the new route from origin *)
        let compare_routes = merge neighbor old_attribute_from_x n_incoming_attribute in

        (* This is a hack because merge may not be selective *)
        let dummy_new = merge neighbor n_incoming_attribute n_incoming_attribute in

        (*if the merge between new and old route from origin is equal to the new route from origin*)
        if (compare_routes = dummy_new) then
          (*we can incrementally compute in this case*)
          let n_new_attribute = merge neighbor n_old_attribute n_incoming_attribute in
          let new_entry = AdjGraph.VertexMap.add origin n_incoming_attribute n_received in
          (*update the todo list if the node's solution changed.*)
          if (n_old_attribute = n_new_attribute)
          then (AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s, todo)
          else (AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s, neighbor :: todo)
        else
          (* In this case, we need to do a full merge of all received routes *)
          let best = AdjGraph.VertexMap.fold (fun _ v acc -> merge neighbor v acc)
              n_received n_incoming_attribute
          in
          let newTodo = if n_old_attribute = best then todo else neighbor :: todo in
          (*add the new received route for n from origin*)
          let n_received = AdjGraph.VertexMap.add origin n_incoming_attribute n_received in
          (AdjGraph.VertexMap.add neighbor (n_received, best) s, newTodo)

    in
    let initial_attribute = get_attribute origin s in
    let neighbors = AdjGraph.succ G.graph origin in
    BatList.fold_left (do_neighbor initial_attribute) (s, []) neighbors

  (* simulate_init s q simulates srp starting with initial state (s,q) *)
  let rec simulate_init trans merge ((s, q): 'a state) =
    match QueueSet.pop q with
    | None -> s
    | Some (next, rest) ->
      let s', more = simulate_step trans merge s next in
      simulate_init trans merge (s', QueueSet.add_all rest more)

  (* simulate for at most k steps *)
  let simulate_init_bound trans merge ((s, q): 'a state) k =
    let rec loop s q k =
      if k <= 0 then (s, q)
      else
        match QueueSet.pop q with
        | None -> (s, q)
        | Some (next, rest) ->
          let s', more = simulate_step trans merge s next in
          loop s' (QueueSet.add_all rest more) (k - 1)
    in
    loop s q k

  (* List holding the solutions of solved SRPs*)
  let solved = ref []

  let simulate_solve attr_ty_id name init trans merge =
    let s = create_state (AdjGraph.nb_vertex G.graph) init in
    let vals = simulate_init trans merge s |> AdjGraph.VertexMap.map (fun (_,v) -> v) in
    let default = AdjGraph.VertexMap.choose vals |> snd in
    let bdd_base = NativeBdd.create ~key_ty_id:(CompileBDDs.get_type_id TNode)
        ~val_ty_id:attr_ty_id default
    in
    let bdd_full = AdjGraph.VertexMap.fold (fun n v acc -> NativeBdd.update attr_ty_id acc n v) vals bdd_base in
    solved := (name, (Obj.magic bdd_full, CompileBDDs.get_type attr_ty_id)) :: !solved;
    bdd_full
end

(** Given the attribute type of the network constructs an OCaml function
      that takes as input an OCaml value and creates a similar NV value.*)
let ocaml_to_nv_value record_fns (attr_ty: Syntax.ty) : 'a -> Syntax.value =
    Embeddings.embed_value record_fns (TMap(TNode, attr_ty))

let build_solution record_fns (vals, ty) =
  let open Solution in
  ocaml_to_nv_value record_fns ty vals

let build_solutions graph record_fns sols =
  let open Solution in
  {
    symbolics = []; (*TODO: but it's not important for simulation.*)
    assertions = [];
    solves = List.map (fun (name, sol) -> (Var.create name, { sol_val = build_solution record_fns sol; mask = None; attr_ty = snd sol})) sols;
    nodes = graph;
  }
