(* Maintenance NVgen tools.
 * maintenance is intended for demonstration with fatXPol benchmarks:
 * code generated from other benchmarks will probably not work! *)
open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open Batteries
open Utils

let maintenanceTag = e_val (vint (Integer.of_int 0))

(* Return a DLet declaration for a tagDown function, used to update the BGP
 * community tags on transfer for edges leaving the down node.
 * Has the form:
 * ```
 * (* tagDown : edge -> bgpType -> bgpType *)
 * let tagDown e b =
 *   match down with
 *   | None -> b
 *   | Some d -> { b with comms = (match e with | u~_ -> if u = d then b.comms[0u32:=true] else b.comms) }
 *  ```
 *)
let tagDown_decl (down : var) =
  let edge_var = Var.fresh "e" in
  let bvar = Var.fresh "b" in
  let dvar = Var.fresh "d" in
  let bupdate = update_comms [evar dvar, maintenanceTag] in
  let branches = addBranch (POption (Some (PVar dvar))) bupdate emptyBranch in
  let branches = addBranch (POption None) (evar bvar) branches in
  let downmatch = ematch (evar down) branches in
  let fn = efunc (func bvar downmatch) in
  let fn = efunc (func edge_var fn) in
  DLet (Var.fresh "tagDown", None, fn)
;;

(* update the trans function to drop comms with the maintenance tag set *)
let maintenance_trans aty e =
  let xvar = Var.fresh "x" in
  let bvar = Var.fresh "b" in
  let dropBgp =
    let none = e_val (voption None) in
    let testMaintenance = eop MGet [eproject (evar bvar) "comms"; maintenanceTag] in
    let testTag = eif testMaintenance none (esome (evar bvar)) in
    let branches = addBranch (POption None) none emptyBranch in
    let branches = addBranch (POption (Some (PVar bvar))) testTag branches in
    ematch (eproject (evar xvar) "bgp") branches
  in
  let descender _ e =
    match e.e with
    | ERecord _ ->
      (* change the old { ... } to be assigned to a variable x,
       * and then use that x in a call to dropBgp *)
      let newb = elet bvar dropBgp e in
      elet xvar (ety e aty) newb
    | _ -> e
  in
  (* stop after four levels deep *)
  descend descender (fun l _ -> List.length l = 4) [] e
;;

(* update the BGP comms with the down tag if need be;
 * ```
 * let transferBgp e x0 =
 *   match x0.selected with
 *   | None -> None
 *   | Some prot ->
 *      (let b = if (prot = 3u2) then match x0.bgp with
 *        | None -> (...)
 *        | Some b -> b
 *       else (...)) in
 *       let b = { b with comms = tagDown e b } in
 *       match e with ...
 * ```
 *)
let maintenance_transferBgp e =
  let add_tagDown_before_edges edge e =
    match e.e with
    | ELet (bvar, bexp, edgebody) ->
      let tagdown = Var.fresh "tagDown" in
      let call = eapp (eapp (evar tagdown) edge) (evar bvar) in
      let body = elet bvar call edgebody in
      elet bvar bexp body
    | _ -> failwith "maintenance_transferBgp: unexpected expr"
  in
  let update_branch_case edge (p, e) =
    match p with
    | POption (Some (PVar _)) -> p, add_tagDown_before_edges edge e
    | _ -> p, e
  in
  let descender vars e =
    let edge = List.nth vars 1 in
    match e.e with
    | EMatch (e1, bs) -> ematch e1 (mapBranches (update_branch_case (evar edge)) bs)
    | _ -> e
  in
  descend descender (fun l _ -> List.length l = 2) [] e
;;

(* Modify assert_node to instead have the form:
 * ```
 *  match x.selected with
 *   | None -> false
 *   | _ -> (match x.bgp with
 *      | None -> false
 *      | Some b -> (!b.comms[maintenanceTag]))
 * ```
 *  where maintenanceTag is the tag to identify a node as under maintenance.
 *)
let maintenance_assert_node e =
  let update_branch_case x (p, e) =
    match p with
    | PWild ->
      (* change to capture the protocol, and test it.
       * if it's BGP, perform the additional BGP test; otherwise, return true? *)
      let xbgp = eproject x "bgp" in
      let check_tag b =
        let comms = eproject b "comms" in
        eop Not [eop MGet [comms; maintenanceTag]]
      in
      let test = assert_bgp xbgp check_tag in
      PWild, test
    | _ -> p, e
  in
  let descender vars e =
    let x = evar (List.nth vars 0) in
    match e.e with
    | EIf (e1, e2, e3) ->
      let e2 =
        match e2.e with
        | EMatch (e', bs) -> ematch e' (mapBranches (update_branch_case x) bs)
        | _ -> e2
      in
      eif e1 e2 e3
    | _ -> failwith "maintenance_assert_node: expected if, got something else"
  in
  descend descender (fun l _ -> List.length l = 2) [] e
;;
