open Nv_datastructures
open Nv_lang
open Syntax
open Collections

(* e should be of the form:
 * fun node -> match node with | 0n -> ... | 1n -> ... *)
let hijack_init hijacker hijack_var e =
  match e.e with
  | EFun f ->
    let body =
      match f.body.e with
      | EMatch (e, branches) ->
        (* add a branch for the new node *)
        ematch
          e
          (addBranch
             (PNode hijacker)
             (aexp (evar hijack_var, f.resty, Span.default))
             branches)
      | _ -> failwith "hijack_init: expected an inner match statement"
    in
    efunc { f with body }
  | _ -> failwith "hijack_init: expected a function"
;;

let edgetag = "edgeTag"

(* Return a DLet declaration for an edgeTag function, used to update the BGP
 * community tags on transfer for edges leaving the destination or the hijacker. *)
let hijack_edgetag (hijacker : node) (dest : node) =
  let edge_var = Var.fresh "e" in
  let comms_var = Var.fresh "comms" in
  let tru = ebool true in
  let legit = e_val (vint (Integer.of_int 0)) in
  let illegit = e_val (vint (Integer.of_int 1)) in
  let set_add k = eop MSet [evar comms_var; k; tru] in
  let dest = e_val (vnode dest) in
  let hijacker = e_val (vnode hijacker) in
  let avar = Var.fresh "a" in
  let bvar = Var.fresh "b" in
  let edgePat = PEdge (PVar avar, PVar bvar) in
  let hijack_if = eif (eop Eq [evar avar; hijacker]) (set_add illegit) (evar comms_var) in
  let dest_if = eif (eop Eq [evar avar; dest]) (set_add legit) hijack_if in
  let body = ematch (evar edge_var) (addBranch edgePat dest_if emptyBranch) in
  let fn = efunc (func comms_var body) in
  let fn = efunc (func edge_var fn) in
  DLet (Var.fresh edgetag, None, fn)
;;

type transferBgpBehavior =
  | ExitDrop
  | ExitLeak
  | Enter

(** Given a function over record key-value pairs, return a new record expression.
 *)
let mapi_record (f : String.t * exp -> exp) labels e =
  erecord
    (List.fold_left
       (fun r l -> StringMap.add l (f (l, eproject e l)) r)
       StringMap.empty
       labels)
;;

let update_record_at f label = mapi_record (fun (l, e) -> if l = label then f e else e)

(* e is a function with an edge argument and a rib argument *)
let hijack_transferBgp (edges : (edge * transferBgpBehavior) list) e =
  (* The hijack edges don't need to do anything special in transferBgp, just increment the aslen.
   * If leak is true, the last exiting edge will leak the route; otherwise, all exiting edges
   * simply transfer None.
   * For the opposite direction, no other special behaviour happens here: edgeTag takes care of the
   * community tag. *)
  (* FIXME: kinda risky just assuming this will work: relies on b being the chosen let var *)
  let bvar = Var.fresh "b" in
  let labels = ["bgpAd"; "lp"; "aslen"; "med"; "comms"] in
  let add_edgetag_call arg (pat, exp) =
    match pat with
    | POption (Some (PVar v)) when Var.equal_names v bvar ->
      let et = evar (Var.fresh edgetag) in
      let update_comms =
        update_record_at (fun e -> eapp (eapp et (evar arg)) e) "comms" labels
      in
      (* wrap the first expression with a let *)
      pat, elet bvar (update_comms (evar bvar)) exp
    | _ -> pat, exp
  in
  let add_hijack_branch branches ((u, v), behavior) =
    let edgePat = PEdge (PNode u, PNode v) in
    let incr_aslen =
      update_record_at
        (fun e -> eop (UAdd 32) [e; e_val (vint (Integer.of_int 1))])
        "aslen"
        labels
    in
    let body =
      match behavior with
      | ExitDrop -> e_val (voption None)
      | _ -> esome (incr_aslen (evar bvar))
    in
    addBranch edgePat body branches
  in
  let update_edge_match v2 v3 e =
    match e.e with
    | EMatch (e1, bs) ->
      (match e1.e with
      | EVar v when Var.equal_names v v2 ->
        ematch e1 (List.fold_left add_hijack_branch bs edges)
      | EVar v when Var.equal_names v v3 ->
        ematch e1 (mapBranches (add_edgetag_call v2) bs)
      | _ -> e)
    | _ -> e
  in
  match e.e with
  | EFun { arg; body; _ } ->
    efun (func arg (Visitors.map_exp (update_edge_match arg bvar) body))
  | _ -> failwith "hijack_transferBgp: expected a function"
;;
