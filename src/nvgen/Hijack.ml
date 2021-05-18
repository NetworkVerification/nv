open Nv_datastructures
open Nv_lang
open Syntax
open Collections

let legit = e_val (vint (Integer.of_int 0))
let illegit = e_val (vint (Integer.of_int 1))

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

(* Return a match statement over the given variable's bgp field, testing an assertion. *)
let assert_bgp x =
  let b = Var.fresh "b" in
  let comms = eproject (evar b) "comms" in
  let has_illegit_tag = eop Not [eop MGet [comms; illegit]] in
  let xbgp = eproject x "bgp" in
  let branches = addBranch (POption (Some (PVar b))) has_illegit_tag emptyBranch in
  let branches = addBranch (POption None) (ebool false) branches in
  ematch xbgp branches
;;

(* Modify assert_node to instead have the form:
 * match x.selected with
 *   | None -> false
 *   | Some prot -> !(prot = 3u2) || (match x.selected with
 *      | None -> false
 *      | Some b -> (node = hijacker) || (!b.comms[illegitimate]))
 * where hijacker is the newly-added node and illegitimate is the tag to identify it.
 *)
let hijack_assert_node hijacker e =
  let update_branch_case x (p, e) =
    match p with
    | POption None -> p, e
    | PWild ->
      (* change to capture the protocol, and test it.
       * if it's BGP, perform the additional BGP test; otherwise, return true? *)
      let prot = Var.fresh "prot" in
      (* create a 3u2, used to identify the BGP protocol *)
      let protoBgp = e_val (vint (Integer.create 3 2)) in
      let isNotBgpProt = eop Not [eop Eq [evar prot; protoBgp]] in
      let test = eop Or [isNotBgpProt; assert_bgp x] in
      POption (Some (PVar prot)), test
    | _ ->
      failwith
        ("found unexpected branch pattern in hijack_assert_node: "
        ^ Printing.pattern_to_string p)
  in
  match e.e with
  | EFun f1 ->
    let body1 =
      match f1.body.e with
      | EFun f2 ->
        let node = evar f1.arg in
        let body2 =
          match f2.body.e with
          | EIf (e1, e2, e3) ->
            let hijacker = e_val (vnode hijacker) in
            let is_hijacker = eop Eq [node; hijacker] in
            let x = evar f2.arg in
            let e2' =
              match e2.e with
              | EMatch (e', bs) -> ematch e' (mapBranches (update_branch_case x) bs)
              | _ -> failwith "unexpected inner expression in hijack_assert_node"
            in
            (* default to true for the hijacker: we don't care what their solution is *)
            let e2or = eop Or [is_hijacker; e2'] in
            eif e1 e2or e3
          | _ -> failwith "unexpected outer expression in hijack_assert_node"
        in
        efunc { f2 with body = body2 }
      | _ -> failwith "unexpected expression in hijack_assert_node"
    in
    efunc { f1 with body = body1 }
  | _ -> failwith "unexpected expression in hijack_assert_node"
;;
