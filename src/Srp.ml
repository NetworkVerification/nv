open Collections
open Unsigned
open Solution
open Syntax

type srp =
  { graph: Graph.t
  ; trans: Syntax.closure
  ; merge: Syntax.closure
  ; assertion: Syntax.closure option }

(******************)
(* SRP Simulation *)
(******************)

module S = Map.Make (UInt32)

exception Simulation_error of string

(* Simulation States *)
(* Solution Invariant: All valid graph vertices are associated with an attribute initially (and always) *)
type solution = value Graph.VertexMap.t

type queue = Graph.Vertex.t QueueSet.queue

type state = solution * queue

let create_state n cl : state =
  let rec loop n (q: UInt32.t QueueSet.queue) m =
    if UInt32.compare n UInt32.zero > 0 then
      let next_n = UInt32.pred n in
      let next_q = QueueSet.add q next_n in
      let next_m =
        Graph.VertexMap.add next_n
          (Interp.interp_closure cl [vint next_n])
          m
      in
      loop next_n next_q next_m
    else (m, q)
  in
  loop n (QueueSet.empty UInt32.compare) Graph.VertexMap.empty

type info =
  { mutable env: Syntax.env
  ; (* environment *)
    mutable m: Syntax.closure option
  ; (* merge *)
    mutable t: Syntax.closure option
  ; (* assert *)
    mutable a: Syntax.closure option
  ; (* trans *)
    mutable ns: UInt32.t option
  ; (* nodes *)
    mutable es: (UInt32.t * UInt32.t) list option
  ; (* edges *)
    mutable init: Syntax.closure option (* initial state *)
  ; mutable syms: value StringMap.t }

exception Require_false

let declarations_to_state ds ~throw_requires =
  let info =
    { env= Interp.empty_env
    ; m= None
    ; t= None
    ; a= None
    ; ns= None
    ; es= None
    ; init= None
    ; syms= StringMap.empty }
  in
  let if_none opt f msg =
    match opt with None -> f () | Some f -> Console.error msg
  in
  let process_declaration d =
    match d with
    | DLet (x, _, e) ->
        let env = info.env in
        let v = Interp.interp_exp env e in
        info.env <- Interp.update_value env x v
    | DSymbolic (x, Exp e) ->
        let env = info.env in
        let v = Interp.interp_exp env e in
        info.env <- Interp.update_value env x v ;
        info.syms <- StringMap.add (Var.to_string x) v info.syms
    | DSymbolic (x, Ty ty) ->
        let env = info.env in
        let e = e_val (default_value ty) in
        let v = Interp.interp_exp env e in
        info.env <- Interp.update_value env x v ;
        info.syms <- StringMap.add (Var.to_string x) v info.syms
    | DMerge e ->
        let get_merge () =
          match (Interp.interp_exp info.env e).v with
          | VClosure cl -> info.m <- Some cl
          | _ -> failwith "merge was not evaluated to a closure"
        in
        if_none info.m get_merge "multiple merge functions"
    | DTrans e ->
        let get_trans () =
          match (Interp.interp_exp info.env e).v with
          | VClosure cl -> info.t <- Some cl
          | _ -> failwith "trans was not evaluated to a closure"
        in
        if_none info.t get_trans "multiple trans functions"
    | DAssert e ->
        let get_assert () =
          match (Interp.interp_exp info.env e).v with
          | VClosure cl -> info.a <- Some cl
          | _ -> failwith "assert was not evaluated to a closure"
        in
        if_none info.a get_assert "multiple assert functions"
    | DNodes n ->
        if_none info.ns
          (fun () -> info.ns <- Some n)
          "multiple nodes declarations"
    | DEdges es ->
        if_none info.es
          (fun () -> info.es <- Some es)
          "multiple edges declarations"
    | DInit e ->
        let get_initializer () =
          match (Interp.interp_exp info.env e).v with
          | VClosure cl -> info.init <- Some cl
          | _ -> failwith "init was not evaluated to a closure"
        in
        if_none info.init get_initializer
          "multiple initialization declarations"
    | DRequire e -> (
      match (Interp.interp_exp info.env e).v with
      | VBool true -> ()
      | _ ->
          if throw_requires then raise Require_false
          else
            Console.warning
              "requires condition not satisified by inital state" )
    | DATy _ -> ()
  in
  List.iter process_declaration ds ;
  match info with
  | { env= _
    ; m= Some mf
    ; t= Some tf
    ; a
    ; ns= Some n
    ; es= Some es
    ; init= Some cl } ->
      let srp =
        { graph= Graph.add_edges (Graph.create n) es
        ; trans= tf
        ; merge= mf
        ; assertion= a }
      in
      let state = create_state n cl in
      (srp, state, info.syms)
  | {m= None} -> Console.error "missing merge function"
  | {t= None} -> Console.error "missing trans function"
  | {ns= None} -> Console.error "missing nodes declaration"
  | {es= None} -> Console.error "missing edges declaration"
  | {init= None} -> Console.error "missing init declaration"

let solution_to_string s =
  Graph.vertex_map_to_string Printing.value_to_string s

let get_attribute v s =
  let find_opt v m =
    try Some (Graph.VertexMap.find v m) with Not_found -> None
  in
  match find_opt v s with
  | None -> failwith ("no attribute at vertex " ^ UInt32.to_string v)
  | Some a -> a

let simulate_step {graph= g; trans; merge} s x =
  let do_neighbor initial_attribute (s, todo) n =
    let neighbor = vint n in
    let origin = vint x in
    let edge = vtuple [origin; neighbor] in
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
    else (Graph.VertexMap.add n n_new_attribute s, n :: todo)
  in
  let initial_attribute = get_attribute x s in
  let neighbors = Graph.neighbors g x in
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

let check_assertion srp node v =
  match srp.assertion with
  | None -> true
  | Some a ->
      let v = Interp.interp_closure a [vint node; v] in
      match v.v with
      | VBool b -> b
      | _ -> failwith "internal error (check_assertion)"

let check_assertions srp vals =
  Graph.VertexMap.mapi (fun n v -> check_assertion srp n v) vals

let simulate_declarations ds =
  let srp, state, syms =
    declarations_to_state ds ~throw_requires:true
  in
  let vals = simulate_init srp state in
  let asserts = check_assertions srp vals in
  {labels= vals; symbolics= syms; assertions= Some asserts}

let simulate_declarations_bound ds k =
  let srp, state, syms =
    declarations_to_state ds ~throw_requires:true
  in
  let vals, q = simulate_init_bound srp state k in
  let asserts = check_assertions srp vals in
  ({labels= vals; symbolics= syms; assertions= Some asserts}, q)
