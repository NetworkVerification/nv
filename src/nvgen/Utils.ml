open Nv_lang
open Nv_datastructures
open Batteries
open Syntax
open Collections

(* definitions we'll use for the functions.
 * the labels should really be extracted from the file instead of hardcoded,
 * but we can safely assume if we're running this code on fatXPol examples
 * that all of these elements will always be present and save ourselves the work of
 * doing type inference. *)
let bgplabels = ["bgpAd"; "lp"; "aslen"; "med"; "comms"]
let riblabels = ["bgp"; "connected"; "ospf"; "selected"; "static"]

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

let update_comms (pairs : (exp * exp) list) : exp =
  let bvar = Var.fresh "b" in
  let update_comms comms =
    let edge_var = Var.fresh "e" in
    let uvar = Var.fresh "u" in
    let edgePat = PEdge (PVar uvar, PWild) in
    let set_add k = eop MSet [comms; k; ebool true] in
    (* if u = hijacker, then add the illegit comms tag *)
    let wrap_if e (case, tag) = eif (eop Eq [evar uvar; case]) (set_add tag) e in
    let body = List.fold_left wrap_if comms pairs in
    ematch (evar edge_var) (addBranch edgePat body emptyBranch)
  in
  update_record_at update_comms "comms" bgplabels (evar bvar)
;;

(* `descend f b g a e` walks down the given expression into its subexpressions
 * e1 until b a e1, at which point we call f a e1 and reascend.
 * descend only traverses functions and lets, and maintains an accumulator a using
 * accumulation function g.
 *)
let rec descend
    (f : 'a -> exp -> exp)
    (b : 'a -> exp -> bool)
    (g : exp -> 'a -> 'a)
    (a : 'a)
    (e : exp)
    : exp
  =
  match e.e with
  | _ when b a e -> f a e
  | EFun f1 -> efunc { f1 with body = descend f b g (g e a) f1.body }
  | ELet (v, e1, b1) -> elet v e1 (descend f b g (g e a) b1)
  (* other exp types are to-do, but it's not immediately obvious how to handle them *)
  | _ -> e
;;
