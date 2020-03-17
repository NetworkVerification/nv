open Nv_lang
open Nv_datastructures
open Nv_solution
open Nv_utils
open Nv_interpreter
open Nv_lang.Syntax
open Nv_lang.Collections
open OCamlUtils

type srp =
  { graph: AdjGraph.t
  ; trans: Syntax.closure
  ; merge: Syntax.closure
  ; assertion: Syntax.closure option }

(******************)
(* SRP Simulation *)
(******************)

(* module S = Map.Make (Integer) *)

exception Simulation_error of string

(* Simulation States *)
(* Solution Invariant: All valid graph vertices are associated with an attribute initially (and always) *)
type solution = value AdjGraph.VertexMap.t

type extendedSolution = (solution * value) AdjGraph.VertexMap.t
type queue = AdjGraph.Vertex.t QueueSet.queue

type state = extendedSolution * queue

let create_state n cl : state =
  let rec loop n (q: queue) m =
    if Pervasives.compare n 0 > 0 then
      let next_n = n - 1 in
      let next_q = QueueSet.add q next_n in
      let init_n = Interp.interp_closure cl [vnode next_n] in
      let next_m =
        AdjGraph.VertexMap.add next_n
          (AdjGraph.VertexMap.singleton next_n init_n, init_n)
          m
      in
      loop next_n next_q next_m
    else (m, q)
  in
  loop n (QueueSet.empty Pervasives.compare) AdjGraph.VertexMap.empty

type info =
  { mutable env: Syntax.env; (* environment *)
    mutable syms: value VarMap.t; (* Defined symbolics *)
    mutable merge: Syntax.closure option;
    mutable trans: Syntax.closure option;
    mutable init: Syntax.closure option;
    mutable assertion: Syntax.closure option;
    nodes: int;
    edges: Syntax.edge list;
  }

exception Require_false

let net_to_srp net ~throw_requires =
  let info =
    { env= empty_env
    ; merge= None
    ; trans= None
    ; assertion= None
    ; nodes= AdjGraph.nb_vertex net.Syntax.graph
    ; edges= AdjGraph.edges net.Syntax.graph
    ; init= None
    ; syms= VarMap.empty }
  in
  (* let if_none opt f msg = *)
  (*   match opt with None -> f () | Some f -> Console.error msg *)
  (* in *)
  let get_func e =
    match (Interp.interp_exp info.env e).v with
    | VClosure cl -> Some cl
    | _ -> failwith "must evaluate to a closure"
  in
  (* process symbolics *)
  BatList.iter (fun (x, ty_exp) ->
      let env = info.env in
      let e = match ty_exp with
        | Exp e -> e
        | Ty ty -> e_val (Generators.default_value ty)
      in
      let v = Interp.interp_exp env e in
      info.env <- update_value env x v ;
      info.syms <- VarMap.add x v info.syms) (net.symbolics);
  (* process let definitions *)
  BatList.iter (fun (x, _, e) ->
      let env = info.env in
      let v = Interp.interp_exp env e in
      info.env <- update_value env x v) net.defs;
  info.init <- get_func net.Syntax.init;
  info.merge <- get_func net.Syntax.merge;
  info.trans <- get_func net.Syntax.trans;
  info.assertion <- (match net.Syntax.assertion with
      | Some a -> get_func a
      | None -> None);
  (* process requires *)
  BatList.iter (fun e ->
      match (Interp.interp_exp info.env e).v with
      | VBool true -> ()
      | _ ->
        if throw_requires then raise Require_false
        else
          Console.warning
            "requires condition not satisified by initial state" ) net.requires;
  match info with
  | { env= _; merge = Some merge; trans = Some trans; init = Some init;
      nodes; edges; assertion; _} ->
    let srp =
      { graph = List.fold_left AdjGraph.add_edge_e (AdjGraph.create nodes) edges;
        trans; merge; assertion; }
    in
    (srp, init, info.syms)
  | _ -> failwith "impossible"

let net_to_state net ~throw_requires =
  let srp, init, syms = net_to_srp net ~throw_requires in
  let state = create_state (AdjGraph.nb_vertex srp.graph) init in
  (srp, state, syms)

let solution_to_string s =
  AdjGraph.VertexMap.to_string Printing.value_to_string s

let get_attribute v s =
  match AdjGraph.VertexMap.Exceptionless.find v s with
  | None -> failwith ("no attribute at vertex " ^ string_of_int v)
  | Some a -> a

let simulate_step ({graph= g; trans; merge; _} : srp) s x =
  (* Printf.printf "x is:%d\n" x; *)
  let do_neighbor (_, initial_attribute) (s, todo) n =
    let neighbor = vnode n in
    let edge = vedge (x, n) in
    (* Printf.printf "n is:%d\n" n; *)
    let n_incoming_attribute =
      Interp.interp_closure trans [edge; initial_attribute]
    in
    let (n_received, n_old_attribute) = get_attribute n s in
    match AdjGraph.VertexMap.Exceptionless.find x n_received with
    | None ->
      (* if this is the first message from this node then add it to the received messages of n*)
      let new_entry = AdjGraph.VertexMap.add x n_incoming_attribute n_received in
      (*compute new merge and decide whether best route changed and it needs to be propagated*)
      let n_new_attribute =
        Interp.interp_closure merge
          [neighbor; n_old_attribute; n_incoming_attribute]
      in
      if equal_values ~cmp_meta:false n_old_attribute n_new_attribute
      then (AdjGraph.VertexMap.add n (new_entry, n_new_attribute) s, todo)
      else (AdjGraph.VertexMap.add n (new_entry, n_new_attribute) s, n :: todo)
    | Some old_attribute_from_x ->
      (*withdraw the route received from x*)
      let n_received = AdjGraph.VertexMap.remove x n_received in
      let compare_routes =
        Interp.interp_closure merge [neighbor; old_attribute_from_x; n_incoming_attribute]
      in
      (* Printf.printf "compare_routes is:%s\n" (Printing.value_to_string compare_routes); *)
      let dummy_new =
        Interp.interp_closure merge [neighbor; n_incoming_attribute; n_incoming_attribute]
      in
      (* Printf.printf "compare_routes is:%s\n" (Printing.value_to_string dummy_new); *)
      (*if the merge between new and old routes is equal to the new route then we can incrementally merge it*)
      if (equal_values ~cmp_meta:false compare_routes dummy_new) then
        let n_new_attribute =
          Interp.interp_closure merge [neighbor; n_old_attribute; n_incoming_attribute]
        in
        let new_entry = AdjGraph.VertexMap.add x n_incoming_attribute n_received in
        if equal_values ~cmp_meta:false n_old_attribute n_new_attribute
        then (AdjGraph.VertexMap.add n (new_entry, n_new_attribute) s, todo)
        else (AdjGraph.VertexMap.add n (new_entry, n_new_attribute) s, n :: todo)
      else
        let best = AdjGraph.VertexMap.fold (fun _ v acc -> Interp.interp_closure merge [neighbor; v; acc])
            n_received n_incoming_attribute
        in
        let newTodo = if equal_values ~cmp_meta:false n_old_attribute best then todo else n :: todo in
        (*also update the received messages for n*)
        let n_received = AdjGraph.VertexMap.add x n_incoming_attribute n_received in
        (AdjGraph.VertexMap.add n (n_received, best) s, newTodo)
  in
  let initial_attribute = get_attribute x s in
  let neighbors = AdjGraph.succ g x in
  List.fold_left (do_neighbor initial_attribute) (s, []) neighbors

(* simulate srp s q simulates srp starting with initial state (s,q) *)
let rec simulate_init srp ((s, q): state) =
  match QueueSet.pop q with
  | None -> s
  | Some (next, rest) ->
    let s', more = simulate_step srp s next in
    simulate_init srp (s', QueueSet.add_all rest more)

(* simulate for at most k steps *)
let simulate_init_bound srp ((s, q): state) k =
  let rec loop s q k =
    if k <= 0 then (s, q)
    else
      match QueueSet.pop q with
      | None -> (s, q)
      | Some (next, rest) ->
        let s', more = simulate_step srp s next in
        loop s' (QueueSet.add_all rest more) (k - 1)
  in
  loop s q k

let check_assertion (srp : srp) node v =
  match srp.assertion with
  | None -> true
  | Some a ->
    let v = Interp.interp_closure a [vnode node; v] in
    match v.v with
    | VBool b -> b
    | _ -> failwith "internal error (check_assertion)"

let check_assertions srp vals =
  AdjGraph.VertexMap.mapi (fun n v -> check_assertion srp n v) vals

let simulate_net (net: Syntax.network) : Nv_solution.Solution.t =
  let srp, state, syms =
    net_to_state net ~throw_requires:true
  in
  let vals = simulate_init srp state |> AdjGraph.VertexMap.map snd in
  let asserts =
    check_assertions srp vals
    |> AdjGraph.VertexMap.bindings
    |> List.sort (fun (i, _) (i2, _)-> i2-i)
    |> List.map snd
  in
  {labels= vals; symbolics= syms; assertions= asserts; solves = VarMap.empty}

let simulate_net_bound net k : (Nv_solution.Solution.t * queue) =
  let srp, state, syms =
    net_to_state net ~throw_requires:true
  in
  let vals, q = simulate_init_bound srp state k in
  let vals = AdjGraph.VertexMap.map snd vals in
  let asserts = check_assertions srp vals
                |> AdjGraph.VertexMap.bindings
                |> List.sort (fun (i, _) (i2, _)-> i2-i)
                |> List.map snd
  in
  ({labels= vals; symbolics= syms; assertions= asserts; solves = VarMap.empty}, q)

let simulate_solve graph env (solve : Syntax.solve) : value AdjGraph.VertexMap.t =
  let get_func e =
    match (Interp.interp_exp env e).v with
    | VClosure cl -> cl
    | _ -> failwith "must evaluate to a closure"
  in
  let trans, merge, init =
    get_func solve.trans, get_func solve.merge, get_func solve.init
  in
  let srp = {graph; trans; merge; assertion = None} in
  let state = create_state (AdjGraph.nb_vertex graph) init in
  simulate_init srp state
  |> AdjGraph.VertexMap.map snd
