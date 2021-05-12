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

(* Return a DLet declaration for an edgeTag function, used to update the BGP
 * community tags on transfer for edges leaving the destination or the hijacker. *)
let hijack_edgetag (hijacker : node) (dest : node) =
  let edge_var = Var.fresh "e" in
  let tru = ebool true in
  let fls = ebool false in
  let legit = e_val (vint (Integer.of_int 0)) in
  let illegit = e_val (vint (Integer.of_int 1)) in
  let empty_set = eop MCreate [fls] in
  let singleton k = eop MSet [empty_set; k; tru] in
  let dest = e_val (vnode dest) in
  let hijacker = e_val (vnode hijacker) in
  let avar = Var.fresh "a" in
  let bvar = Var.fresh "b" in
  let edgePat = PEdge (PVar avar, PVar bvar) in
  let hijack_if = eif (eop Eq [evar avar; hijacker]) (singleton illegit) empty_set in
  let dest_if = eif (eop Eq [evar avar; dest]) (singleton legit) hijack_if in
  let body = ematch (evar edge_var) (addBranch edgePat dest_if emptyBranch) in
  let fn = efunc (funcFull edge_var (Some TEdge) (Some (TMap (TInt 32, TBool))) body) in
  DLet (Var.fresh "edgeTag", None, fn)
;;

type transferBgpBehavior =
  | ExitDrop
  | ExitLeak
  | Enter

(* e is a function with an edge argument and a rib argument *)
let hijack_transferBgp (edges : (edge * transferBgpBehavior) list) e =
  (* The hijack edges don't need to do anything special in transferBgp, just increment the aslen.
   * If leak is true, the last exiting edge will leak the route; otherwise, all exiting edges
   * simply transfer None.
   * For the opposite direction, no other special behaviour happens here: edgeTag takes care of the
   * community tag. *)
  let add_hijack_branch branches ((u, v), behavior) =
    let edgePat = PEdge (PNode u, PNode v) in
    (* TODO:
     * making a record involves creating a StringMap;
     * in this case, we just project the original value of b for each field except aslen, which we increment *)
    let update_aslen b =
      let update_field l : exp =
        if l = "aslen"
        then eop (UAdd 32) [eproject b l; e_val (vint (Integer.of_int 1))]
        else eproject b l
      in
      let labels = ["bgpAd"; "lp"; "aslen"; "med"; "comms"] in
      erecord
        (List.fold_left
           (fun r l -> StringMap.add l (update_field l) r)
           StringMap.empty
           labels)
    in
    let body =
      match behavior with
      | ExitDrop -> e_val (voption None)
      | _ -> esome e
    in
    addBranch edgePat body branches
  in
  let update_edge_match v2 e =
    match e.e with
    | EMatch (e1, bs) ->
      (match e1.e with
      | EVar v when Var.equal_names v v2 ->
        ematch e1 (List.fold_left add_hijack_branch bs edges)
      | _ -> e)
    | _ -> e
  in
  match e.e with
  | EFun { arg; body; _ } -> Visitors.map_exp (update_edge_match arg) body
  | _ -> failwith "hijack_transferBgp: expected a function"
;;
