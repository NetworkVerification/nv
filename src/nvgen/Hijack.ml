(* Hijacking NVgen tools.
 * hijacks are intended for demonstration with fatXPol benchmarks:
 * code generated from other benchmarks will probably not work! *)
open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open Batteries
open Utils

let legit = e_val (vint (Integer.of_int 0))
let illegit = e_val (vint (Integer.of_int 1))
let enode = e_val % vnode

(* e should be of the form:
 * fun node -> match node with | 0n -> ... | 1n -> ... *)
let hijack_init hijacker hijack_var e =
  match e.e with
  | EFun f ->
    let body =
      match f.body.e with
      | EMatch (e, branches) ->
        (* add a branch for the new node *)
        let branches =
          addBranch
            (PNode hijacker)
            (aexp (evar hijack_var, f.resty, Span.default))
            branches
        in
        ematch e branches
      | _ -> failwith "hijack_init: expected an inner match statement"
    in
    efunc { f with body }
  | _ -> failwith "hijack_init: expected a function"
;;

let edgetag = "edgeTag"

(* Return a DLet declaration for an edgeTag function, used to update the BGP
 * community tags on transfer for edges leaving the destination or the hijacker.
 * edgeTag has type edge -> bgpType -> bgpType
 *)
let hijack_edgetag (hijacker : node) (dest : node) =
  let edge_var = Var.fresh "e" in
  let xvar = Var.fresh "x" in
  let bvar = Var.fresh "b" in
  let bupdate = update_comms [enode hijacker, illegit; enode dest, legit] in
  let branches = addBranch (POption None) (e_val (voption None)) emptyBranch in
  let branches = addBranch (POption (Some (PVar bvar))) (esome bupdate) branches in
  let xbgp = eproject (evar xvar) "bgp" in
  let bmatch = ematch xbgp branches in
  let fn = efunc (func xvar bmatch) in
  let fn = efunc (func edge_var fn) in
  DLet (Var.fresh edgetag, None, fn)
;;

(* e is a function with an edge argument and a rib argument *)
let hijack_transferBgp (edges : (edge * bool) list) e =
  (* NOTE: kinda risky hardcoding this stuff, but what can ya do *)
  let bvar = Var.fresh "b" in
  (* new branches for edges to and from hijacker *)
  let add_hijack_branch branches ((u, v), forward) =
    let edgePat = PEdge (PNode u, PNode v) in
    let incr_aslen =
      update_record_at
        (fun e -> eop (UAdd 32) [e; e_val (vint (Integer.of_int 1))])
        "aslen"
        bgplabels
    in
    let body = if forward then esome (incr_aslen (evar bvar)) else e_val (voption None) in
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
  | EFun { arg; body; _ } ->
    efun (func arg (Visitors.map_exp (update_edge_match arg) body))
  | _ -> failwith "hijack_transferBgp: expected a function"
;;

(* add a call to edgeTag before calling transferBgp *)

let hijack_trans e =
  let et = evar (Var.fresh edgetag) in
  let etapp edge x = eapp (eapp et (evar edge)) (evar x) in
  let f vars e =
    match e.e with
    | ELet (ovar, otrans, obody) ->
      let edge = List.nth vars 0 in
      let x = List.nth vars 1 in
      let xupdate =
        mapi_record
          (fun (l, e) -> if l = "bgp" then etapp edge x else e)
          riblabels
          (evar x)
      in
      (* add this update at the top of the body of let o = transferOspf e x in ...  *)
      let obody = elet x xupdate obody in
      elet ovar otrans obody
    | _ -> e
  in
  let g e l =
    match e.e with
    | EFun f -> f.arg :: l
    | _ -> l
  in
  descend f (fun l _ -> List.length l = 2) g [] e
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
            let hijacker = enode hijacker in
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
