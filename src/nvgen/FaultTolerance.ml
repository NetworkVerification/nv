open Nv_lang
open Nv_datastructures
open Batteries
open Syntax
open Utils

let isFailed = Var.fresh "isFailed"

(* Return a DLet declaration for an isFailed function,
   used to drop the route if the given edge has failed.
   Function adjusts based on the number of provided failure variables.
   Has the form:
   ```
   let isFailed e =
     (Some e = failed0) || (Some e = failed1) || ...
   ```
 *)
let isFailed_decl fail_variables =
  let edge_var = Var.fresh "e" in
  let some_edge = esome (evar edge_var) in
  let disjunct fail_var = eop Eq [some_edge; evar fail_var] in
  let disjunction =
    List.fold_left (fun b fv -> eop Or [disjunct fv; b]) (ebool false) fail_variables
  in
  let fn = efunc (func edge_var disjunction) in
  DLet (isFailed, None, fn)
;;

(* add an if condition that instantly drops the route if the edge has failed to
   the trans function. *)
let ft_trans trans =
  let drop vars e =
    let edge_var = List.nth vars 1 in
    let pair_var = Var.fresh "pair" in
    let pair = eapp (evar edge_to_int_pair) (evar edge_var) in
    let testFailed = eapp (evar isFailed) (evar pair_var) in
    elet pair_var pair (eif testFailed defaultRib e)
  in
  descend drop (fun l _ -> List.length l = 2) [] trans
;;
