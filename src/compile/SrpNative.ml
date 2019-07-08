(** Simulates an SRP compiled to a native OCaml progam *)
open Collections
open Unsigned
open Solution
open Syntax
open Slicing

(** Type of SRP network *)
module type NATIVE_SRP =
  sig
    type attribute
    val graph: AdjGraph.t
    val init : int -> attribute
    val trans: int * int -> attribute -> attribute
    val merge: int -> attribute -> attribute -> attribute
    val assertion: (int -> attribute -> bool) option
    (* val require: bool *)
  end

(* TODO: probably move in the compiler file*)
let rec proj_unsafe (attr_ty : Syntax.ty) (v : 'a) = failwith "todo"

(** Reference to a NATIVE_SRP module *)
let srp = ref None

(** Getter function for [srp]*)
let get_srp () : (module NATIVE_SRP) =
  match !srp with
  | Some srp -> srp
  | None -> failwith "No srp loaded"

(******************)
(* SRP Simulation *)
(******************)

module type SrpSimulationSig =
sig
  val simulate_srp: unit -> unit
end

module S = Map.Make (Integer)
module SrpSimulation (Srp : NATIVE_SRP) : SrpSimulationSig =
  struct
    open Srp
    exception Simulation_error of string

    (* Simulation States *)
    (* Solution Invariant: All valid graph vertices are associated with an attribute initially (and always) *)
    type solution = attribute AdjGraph.VertexMap.t

    type queue = AdjGraph.Vertex.t QueueSet.queue

    type state = solution * queue

    let create_state (n : int) : state =
      let rec loop n (q: queue) m =
        if Pervasives.compare n 0 > 0 then
          let next_n = n - 1 in
          let next_q = QueueSet.add q next_n in
          let next_m =
            AdjGraph.VertexMap.add next_n (init next_n) m
          in
          loop next_n next_q next_m
        else (m, q)
      in
      loop n (QueueSet.empty Pervasives.compare) AdjGraph.VertexMap.empty

    exception Require_false

    let srp_to_state () =
      create_state (AdjGraph.num_vertices graph)

    let solution_to_string s = failwith "to be implemented"

    let get_attribute (v: AdjGraph.VertexMap.key) (s : solution) =
      let find_opt v m =
        try Some (AdjGraph.VertexMap.find v m) with Not_found -> None
      in
      match find_opt v s with
      | None -> failwith ("no attribute at vertex " ^ string_of_int v)
      | Some a -> a

    let simulate_step (s : solution) (origin : int) =
      let do_neighbor (initial_attribute : attribute) (s, todo) neighbor =
        let edge = (neighbor, origin) in
        let n_incoming_attribute = trans edge initial_attribute in
        let n_old_attribute = get_attribute neighbor s in
        let n_new_attribute = merge neighbor n_old_attribute n_incoming_attribute in
        if n_old_attribute = n_new_attribute
        then (s, todo)
        else (AdjGraph.VertexMap.add neighbor n_new_attribute s, neighbor :: todo)
      in
      let initial_attribute = get_attribute origin s in
      let neighbors = AdjGraph.neighbors graph origin in
      BatList.fold_left (do_neighbor initial_attribute) (s, []) neighbors

    (* simulate_init s q simulates srp starting with initial state (s,q) *)
    let rec simulate_init ((s, q): state) =
      match QueueSet.pop q with
      | None -> s
      | Some (next, rest) ->
          let s', more = simulate_step s next in
          simulate_init (s', QueueSet.add_all rest more)

    (* simulate for at most k steps *)
    let simulate_init_bound ((s, q): state) k =
      let rec loop s q k =
        if k <= 0 then (s, q)
        else
          match QueueSet.pop q with
          | None -> (s, q)
          | Some (next, rest) ->
              let s', more = simulate_step s next in
              loop s' (QueueSet.add_all rest more) (k - 1)
      in
      loop s q k

    let check_assertion node v =
      match assertion with
      | None -> true
      | Some a ->
          if a node v then
            true
          else
            false

    let check_assertions vals =
      AdjGraph.VertexMap.fold (fun n v acc -> (check_assertion n v) && acc) vals true

    let simulate_srp () =
      let s = srp_to_state () in
      let vals = simulate_init s in
      let asserts = check_assertions vals in
      if asserts then
        Printf.printf "success\n"
      else
        Printf.printf "assertion failed\n"
      (* {labels= vals; symbolics= syms; assertions= Some asserts} *)
  end
