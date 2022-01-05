open Nv_lang
open Nv_datastructures
open Batteries
open Syntax
open Collections

let node_to_int = Var.fresh "node_to_int"
let edge_to_int_pair = Var.fresh "edge_to_int_pair"

let node_to_int_decl (nodes : int) =
  let node_var = Var.fresh "node" in
  let add_node_branch b i = addBranch (PNode i) (e_val (vint (Integer.of_int i))) b in
  let branches =
    List.fold_left add_node_branch emptyBranch (Nv_utils.OCamlUtils.list_seq nodes)
  in
  let body = ematch (evar node_var) branches in
  let fn = efunc (func node_var body) in
  DLet (node_to_int, None, fn)
;;

let edge_to_int_pair_decl edges =
  let edge_var = Var.fresh "edge" in
  let add_edge_branch b (u, v) =
    let pair = vtuple [vint (Integer.of_int u); vint (Integer.of_int v)] in
    addBranch (PEdge (PNode u, PNode v)) (e_val pair) b
  in
  let branches = List.fold_left add_edge_branch emptyBranch edges in
  let body = ematch (evar edge_var) branches in
  let fn = efunc (func edge_var body) in
  DLet (edge_to_int_pair, None, fn)
;;

let omap = Var.fresh "omap"
let omap_decl =
  let opt_var = Var.fresh "o" in
  let x_var = Var.fresh "x" in
  let f_var = Var.fresh "f" in
  let branches =
    addBranch (POption (Some (PVar x_var)))
      (eapp (evar f_var) (evar x_var))
      (addBranch (POption None) (e_val (voption None)) emptyBranch) in
  let body = ematch (evar opt_var) branches in
  let inner_fn = efunc (func opt_var body) in
  let outer_fn = efunc (func f_var inner_fn) in
  DLet (omap, None, outer_fn)
;;

(* definitions we'll use for the functions.
 * the labels should really be extracted from the file instead of hardcoded,
 * but we can safely assume if we're running this code on fatXPol examples
 * that all of these elements will always be present and save ourselves the work of
 * doing type inference. *)
let bgplabels = ["bgpAd"; "lp"; "aslen"; "med"; "comms"]
let riblabels = ["bgp"; "connected"; "ospf"; "selected"; "static"]

let defaultRib =
  erecord (List.fold_left (fun r l -> StringMap.add l (e_val (voption None)) r) StringMap.empty riblabels)

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

(* type of resulting exp: TRecord *)
let update_comms (pairs : (exp * exp) list) : exp =
  let bvar = Var.fresh "b" in
  let update_comms comms =
    let edge_var = Var.fresh "e" in
    let uvar = Var.fresh "u" in
    let edgePat = PEdge (PVar uvar, PWild) in
    let set_add k = eop MSet [comms; k; ebool true] in
    let wrap_if e (case, tag) =
      eif (eop Eq [eapp (evar node_to_int) (evar uvar); case]) (set_add tag) e
    in
    let body = List.fold_left wrap_if comms pairs in
    ematch (evar edge_var) (addBranch edgePat body emptyBranch)
  in
  update_record_at update_comms "comms" bgplabels (evar bvar)
;;

(* match on the given e1: if it is None, return false;
 * otherwise, return the result of the test on the BGP variable b. *)
let assert_bgp e1 test =
  let b = Var.fresh "b" in
  let branches = addBranch (POption (Some (PVar b))) (test (evar b)) emptyBranch in
  let branches = addBranch (POption None) (ebool false) branches in
  ematch e1 branches
;;

(* `descend f b g a e` walks down the given expression into its subexpressions
 * e1 until b a e1, at which point we call f a e1 and reascend.
 * descend only traverses functions and lets, and maintains a list of all
 * captured variables.
 *)
let rec descend
    (f : var list -> exp -> exp)
    (b : var list -> exp -> bool)
    (a : var list)
    (e : exp)
    : exp
  =
  match e.e with
  | _ when b a e -> f a e
  | EFun f1 -> efunc { f1 with body = descend f b (f1.arg :: a) f1.body }
  | ELet (v, e1, b1) -> elet v e1 (descend f b (v :: a) b1)
  (* other exp types are to-do, but it's not immediately obvious how to handle them *)
  | _ -> e
;;
