open Syntax

let rec optimizeExp e =
  match e.e with
  | EMatch (e1, bs) ->
     let bs' = mapBranches (fun (p,e) -> (p, optimizeExp e)) bs in
     ematch (optimizeExp e1) (optimizeBranches bs') |> wrap e
  | EOp (op, es) ->
     eop op (BatList.map optimizeExp es) |> wrap e
  | EFun f ->
     efun {f with body = optimizeExp f.body} |> wrap e
  | EApp (e1, e2) ->
     eapp (optimizeExp e1) (optimizeExp e2) |> wrap e
  | EIf (e1, e2, e3) ->
     eif (optimizeExp e1) (optimizeExp e2) (optimizeExp e3) |> wrap e
  | ELet (x, e1, e2) ->
     elet x (optimizeExp e1) (optimizeExp e2) |> wrap e
  | ETuple es ->
     etuple (BatList.map optimizeExp es) |> wrap e
  | ESome e1 ->
     esome (optimizeExp e1) |> wrap e
  | ETy (e1, ty) ->
     ety (optimizeExp e1) ty |> wrap e
  | EVar _ -> e
  | EVal v ->
     (match v.v with
      | VClosure (env, f) ->
         e_val (avalue(vclosure (env, {f with body = optimizeExp f.body}), v.vty, v.vspan))
         |> wrap e
      | _ -> e)
  | ERecord es ->
     erecord (Collections.StringMap.map optimizeExp es) |> wrap e
  | EProject (e1, s) -> eproject (optimizeExp e1) s |> wrap e
          
let optimizeNet net =
  { attr_type = net.attr_type;
    init = optimizeExp net.init;
    trans = optimizeExp net.trans;
    merge = optimizeExp net.merge;
    assertion = BatOption.map optimizeExp net.assertion;
    symbolics = BatList.map (fun (x, tye) ->
                    (x, match tye with
                        | Exp e -> Exp (optimizeExp e)
                        | Ty ty -> tye)) net.symbolics;
    defs = BatList.map (fun (x, ty, e) ->
               (x, ty, optimizeExp e)) net.defs;
    utys = net.utys;
    requires = BatList.map optimizeExp net.requires;
    graph = net.graph
  }
