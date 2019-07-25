open Nv_core
open Nv_datastructures
open Nv_solution
open Nv_utils
open Nv_interpreter
open Nv_core.Syntax
open Nv_core.Collections

type srp =
  { graph: AdjGraph.t
  ; trans: Syntax.closure
  ; merge: Syntax.closure
  ; assertion: Syntax.closure option }

(******************)
(* SRP Simulation *)
(******************)

module S = Map.Make (Nv_datatypes.Integer)

exception Simulation_error of string

(* Simulation States *)
(* Solution Invariant: All valid graph vertices are associated with an attribute initially (and always) *)
type solution = value AdjGraph.VertexMap.t

type queue = AdjGraph.Vertex.t QueueSet.queue

type state = solution * queue

let create_state n cl : state =
  let rec loop n (q: queue) m =
    if Pervasives.compare n 0 > 0 then
      let next_n = n - 1 in
      let next_q = QueueSet.add q next_n in
      let next_m =
        AdjGraph.VertexMap.add next_n
          (Interp.interp_closure cl [vnode next_n])
          m
      in
      loop next_n next_q next_m
    else (m, q)
  in
  loop n (QueueSet.empty Pervasives.compare) AdjGraph.VertexMap.empty

type info =
  { mutable env: Syntax.env
  ; (* environment *)
    mutable m: Syntax.closure option
  ; (* merge *)
    mutable t: Syntax.closure option
  ; (* assert *)
    mutable a: Syntax.closure option
  ; (* trans *)
    mutable ns: Syntax.node option
  ; (* nodes *)
    mutable es: Syntax.edge list option
  ; (* edges *)
    mutable init: Syntax.closure option (* initial state *)
  ; mutable syms: value VarMap.t }

exception Require_false

let net_to_srp net ~throw_requires =
  let info =
    { env= empty_env
    ; m= None
    ; t= None
    ; a= None
    ; ns= None
    ; es= None
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
  info.m <- get_func net.Syntax.merge;
  info.t <- get_func net.Syntax.trans;
  info.a <- (match net.Syntax.assertion with
             | Some a -> get_func a
             | None -> None);
  info.ns <- Some (AdjGraph.num_vertices net.Syntax.graph);
  info.es <- Some (AdjGraph.edges net.Syntax.graph);
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
  | { env= _
    ; m= Some mf
    ; t= Some tf
    ; a
    ; ns= Some n
    ; es= Some es
    ; init= Some cl 
    ; _ } ->
      let srp =
        { graph= AdjGraph.add_edges (AdjGraph.create n) es
        ; trans= tf
        ; merge= mf
        ; assertion= a }
      in
      (srp, cl, info.syms)
  | {m= None; _} -> Console.error "missing merge function"
  | {t= None; _} -> Console.error "missing trans function"
  | {ns= None; _} -> Console.error "missing nodes declaration"
  | {es= None; _} -> Console.error "missing edges declaration"
  | {init= None; _} -> Console.error "missing init declaration"

let net_to_state net ~throw_requires =
  let srp, init, syms = net_to_srp net ~throw_requires in
  let state = create_state (AdjGraph.num_vertices srp.graph) init in
  (srp, state, syms)

let solution_to_string s =
  AdjGraph.vertex_map_to_string Printing.value_to_string s

let get_attribute v s =
  let find_opt v m =
    try Some (AdjGraph.VertexMap.find v m) with Not_found -> None
  in
  match find_opt v s with
  | None -> failwith ("no attribute at vertex " ^ string_of_int v)
  | Some a -> a

let simulate_step ({graph= g; trans; merge; _} : srp) s x =
  let do_neighbor initial_attribute (s, todo) n =
    let neighbor = vnode n in
    let edge = vedge (x, n) in
    let n_incoming_attribute =
      Interp.interp_closure trans [edge; initial_attribute]
    in
    let n_old_attribute = get_attribute n s in
    let n_new_attribute =
      Interp.interp_closure merge
        [neighbor; n_old_attribute; n_incoming_attribute]
    in
    if equal_values ~cmp_meta:false n_old_attribute n_new_attribute
    then (s, todo)
    else (AdjGraph.VertexMap.add n n_new_attribute s, n :: todo)
  in
  let initial_attribute = get_attribute x s in
  let neighbors = AdjGraph.neighbors g x in
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
  let vals = simulate_init srp state in
  let asserts = check_assertions srp vals in
  {labels= vals; symbolics= syms; assertions= Some asserts}

let simulate_net_bound net k : (Nv_solution.Solution.t * queue) =
  let srp, state, syms =
    net_to_state net ~throw_requires:true
  in
  let vals, q = simulate_init_bound srp state k in
  let asserts = check_assertions srp vals in
  ({labels= vals; symbolics= syms; assertions= Some asserts}, q)
