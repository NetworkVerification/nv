open Nv_lang.Syntax
open Nv_lang.Collections

let ty_mutator _ x = Some x;;

let pattern_mutator _ p _ = Some p;;

let value_mutator _ v = Some v;;

let exp_mutator (recursors : Mutators.recursors) e =
  let optimizeExp = recursors.recurse_exp in
  match e.e with
  | EMatch (e1, bs) ->
     let bs' = mapBranches (fun (p,e) -> (p, optimizeExp e)) bs in
     Some (ematch (optimizeExp e1) (optimizeBranches bs'))
  | EVal {v=VClosure (env, f); vty= vty;vspan=vspan} ->
    Some (e_val (avalue(vclosure (env, {f with body = optimizeExp f.body}), vty, vspan)))
  | _ -> None
;;

let map_back_mutator _ v _ = Some v;;

let mask_mutator _ v _ = Some v;;

let make_toplevel (toplevel_mutator : 'a Mutators.toplevel_mutator) =
  toplevel_mutator ~name:"OptimizeBranches" ty_mutator pattern_mutator value_mutator exp_mutator map_back_mutator mask_mutator
;;

let optimize_declarations = make_toplevel Mutators.mutate_declarations
let optimize_net = make_toplevel Mutators.mutate_network
let optimize_srp = make_toplevel Mutators.mutate_srp
