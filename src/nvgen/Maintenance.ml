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

(* Return a DLet declaration for an edgeTag function, used to update the BGP
 * community tags on transfer for edges leaving the destination or the hijacker.
 * edgeTag has type edge -> bgpType -> bgpType
 *)
let tagDown_decl (down : var) =
  let edge_var = Var.fresh "e" in
  let xvar = Var.fresh "x" in
  let bvar = Var.fresh "b" in
  let bupdate = update_comms [evar down, maintenanceTag] in
  let branches = addBranch (POption None) (e_val (voption None)) emptyBranch in
  let branches = addBranch (POption (Some (PVar bvar))) (esome bupdate) branches in
  let xbgp = eproject (evar xvar) "bgp" in
  let bmatch = ematch xbgp branches in
  let fn = efunc (func xvar bmatch) in
  let fn = efunc (func edge_var fn) in
  DLet (Var.fresh "tagDown", None, fn)
;;

(* update the trans function to drop comms with the maintenance tag set *)
let maintenance_trans e =
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
  let descendor _ e =
    match e.e with
    | ERecord _ ->
      (* change the old { ... } to be assigned to a variable x,
       * and then use that x in a call to dropBgp *)
      let newb = elet bvar dropBgp e in
      elet xvar e newb
    | _ -> e
  in
  (* stop after four levels deep *)
  descend
    descendor
    (fun c _ -> c = 4)
    (fun e c ->
      match e.e with
      | EFun _ -> c + 1
      | ELet _ -> c + 1
      | _ -> c)
    0
    e
;;

(* TODO: update the BGP comms with the down tag if need be *)
let maintenance_transferBgp e = e
