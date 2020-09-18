open Nv_lang.Syntax
open Nv_lang.Collections

let ty_transformer _ x = Some x
let pattern_transformer _ p _ = Some p
let value_transformer _ v = Some v

let exp_transformer (recursors : Transformers.recursors) e =
  let optimizeExp = recursors.recurse_exp in
  match e.e with
  | EMatch (e1, bs) ->
    let bs' = mapBranches (fun (p, e) -> p, optimizeExp e) bs in
    Some (ematch (optimizeExp e1) (optimizeBranches bs'))
  | EVal { v = VClosure (env, f); vty; vspan } ->
    Some
      (e_val
         (avalue
            (vclosure (env, { f with body = optimizeExp f.body }), vty, vspan)))
  | _ -> None
;;

let map_back_transformer _ _ v _ = Some v
let mask_transformer = map_back_transformer

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer
    ~name:"OptimizeBranches"
    ty_transformer
    pattern_transformer
    value_transformer
    exp_transformer
    map_back_transformer
    mask_transformer
;;

let optimize_declarations = make_toplevel Transformers.transform_declarations
