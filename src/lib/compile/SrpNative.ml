(** Simulates an SRP compiled to a native OCaml progam *)
open Nv_utils
open Unsigned
open Nv_solution
open Nv_lang
open Nv_datastructures
open Nv_lang.Collections
(* open Slicing *)

(** Type of SRP network *)
module type NATIVE_SRP =
  sig
    type attribute
    val graph: AdjGraph.t
    val init : int -> attribute
    val trans: int * int -> attribute -> attribute
    val merge: int -> attribute -> attribute -> attribute
    val assertion: (int -> attribute -> bool) option

    val record_fns: string -> 'a -> 'b
    (* val require: bool *)
  end

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
  val simulate_srp: Syntax.ty -> Nv_solution.Solution.t
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

    let check_assertion a node v m =
      AdjGraph.VertexMap.add node (a node v) m

    let check_assertions vals =
      match assertion with
        | None -> None
        | Some a ->
          Some (AdjGraph.VertexMap.fold (fun n v acc -> (check_assertion a n v acc))
                  vals AdjGraph.VertexMap.empty)

    let rec proj_unsafe (attr_ty : Syntax.ty) (v : 'a) : Syntax.value =
      match attr_ty with
        | TUnit ->
          Syntax.vunit ()
        | TBool ->
          Syntax.vbool (Obj.magic v)
        | TInt _ ->
          Syntax.vint (Obj.magic v |> Integer.of_int)
        | TOption ty ->
          (match Obj.magic v with
            | None -> Syntax.voption None
            | Some v' -> Syntax.voption (Some (proj_unsafe ty v')))
        | TArrow _ -> failwith "Function computed as value"
        | TTuple ts ->
          let vrec = Obj.magic v in
          let n = BatList.length ts in
            Syntax.vtuple
              (BatList.mapi (fun i t ->
                let projv = Obj.magic (record_fns (Printf.sprintf "p%d__%d" i n) vrec) in
                  proj_unsafe t projv) ts)
        | TMap _ -> failwith "tmap"
        | TRecord _ -> failwith "Trecord"
        | TNode -> failwith "Tnode"
        | TEdge -> failwith "Tedge"


    (* | TMap of Nv_lang.Syntax.ty * Nv_lang.Syntax.ty
     * | TRecord of Nv_lang.Syntax.ty Nv_utils.PrimitiveCollections.StringMap.t
     * | TNode
     * | TEdge *)


    let simulate_srp attr_ty =
      let s = srp_to_state () in
      let vals = simulate_init s in
      let asserts = check_assertions vals in
      let open Solution in
        { labels =(*  AdjGraph.VertexMap.map (fun v ->
               * let v' = proj_unsafe attr_ty v in
               *   (Nv_lang.Printing.value_to_string v');
                   *   v') vals; *)
            AdjGraph.VertexMap.empty;
          symbolics = VarMap.empty; (*TODO: but it's not important for simulation.*)
          assertions = asserts}
  end
