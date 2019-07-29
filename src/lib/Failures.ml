(** * Adds link failures to a network *)

open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax

let zero = Integer.create ~value:0 ~size:32
let one = Integer.create ~value:1 ~size:32

let failuresConstraint_arith (k: int) (aedges : AdjGraph.Edge.t list)
                             (failuresMap: Var.t AdjGraph.EdgeMap.t) : Syntax.exp =
  (*building the requires clause that requires
        fail1 + fail2 + .. <= k *)
  let bool2int_exp arg =
    aexp (eif arg (e_val (vint one)) (e_val (vint zero)),
          Some Typing.node_ty, Span.default)
  in
  let failuresSum =
    BatList.fold_left (fun acc (uhat, vhat) ->
        aexp (eop (UAdd 32)
                  [(bool2int_exp (evar (AdjGraph.EdgeMap.find (uhat, vhat) failuresMap))); acc],
              Some Typing.node_ty, Span.default))
                      (e_val (vint zero)) aedges in
  aexp(eop (ULeq 32)
           [failuresSum;
            e_val (vint (Integer.create ~value:k ~size:32))],
       Some TBool, Span.default)

let failuresConstraint_pb (k: int) (failuresMap: Var.t AdjGraph.EdgeMap.t) : Syntax.exp =
  let arg1 = aexp(etuple (AdjGraph.EdgeMap.fold (fun _ fv acc ->
                              (aexp (evar fv, Some TBool, Span.default)) :: acc)
                                       failuresMap []),
                  Some (TTuple (BatList.init (AdjGraph.EdgeMap.cardinal failuresMap)
                                             (fun _ -> TBool))),
                  Span.default
                 )
  in
  let arg2 =
    aexp(etuple (AdjGraph.EdgeMap.fold (fun _ _ acc ->
                     (exp_of_value
                        (avalue (vint (Integer.of_int 1),
                                 Some (TInt 32),
                                 Span.default))) :: acc)
                              failuresMap []),
         Some (TTuple (BatList.init (AdjGraph.EdgeMap.cardinal failuresMap)
                                    (fun _ -> TInt 32))),
         Span.default
        )
  in
  let arg3 = exp_of_value (avalue (vint (Integer.of_int k),
                                   Some (TInt 32),
                                   Span.default))
  in
  aexp (eop (AtMost (AdjGraph.EdgeMap.cardinal failuresMap)) [arg1; arg2; arg3],
        Some TBool,
        Span.default)

let buildSymbolicFailures (aedges : AdjGraph.Edge.t list) (k : int) =
  (* symbolic variables of failures, one for each abstract edge *)
  let open AdjGraph in
  let failuresMap =
    BatList.fold_left (fun acc (u,v) ->
        let e = Printf.sprintf "%s-%s" (Vertex.printVertex u) (Vertex.printVertex v) in
        let failVar = Var.fresh ("failed-" ^ e) in
        EdgeMap.add (u,v) failVar acc) EdgeMap.empty aedges in
  let failures_leq_k = failuresConstraint_pb k failuresMap in
  (*build and returning the declarations *)
  (failuresMap, EdgeMap.fold (fun _ fvar acc ->
                     (fvar, Ty TBool) :: acc) failuresMap [], failures_leq_k)

(* Given a transfer function, constructs a transfer function that
   models link failures. *)
let buildFailTrans
      (_ : AdjGraph.t)
      (trans: (AdjGraph.Edge.t, Syntax.exp) Hashtbl.t)
      (attrTy: Syntax.ty)
      (failuresMap : Var.t AdjGraph.EdgeMap.t)
    : Syntax.exp =
  (* edge argument used by abstract transfer function *)
  let aedge_var = Var.create "edge" in

  (* code that implements check for a failed edge *)
  let failCheck fvar body =
    aexp(eif (aexp(evar fvar, Some TBool, Span.default))
             (Nv_lang.Generators.default_value_exp attrTy)
             body, Some attrTy, Span.default)in

  (* inserting that code in the body of the transfer function *)
  let addFailureCheck fvar exp = (deconstructFun exp).body |> (failCheck fvar) in

  (* for each edge, find it's corresponding
         transfer function and augment it with a check for whether it's
         failed *)
  let branches =
    Hashtbl.fold (fun (u,v) transuv acc ->
        let p = PEdge (PNode u, PNode v) in
        addBranch p (addFailureCheck (AdjGraph.EdgeMap.find (u, v) failuresMap) transuv) acc)
      trans emptyBranch
  in

  (* partial evaluted trans functions are of the form fun m -> ..., grab m *)
  (*trick to find a transfer function *)
  let uv, _ = AdjGraph.EdgeMap.min_binding failuresMap in
  let transuv = Hashtbl.find trans uv in
  let transf = deconstructFun transuv in
  let messageArg = transf.arg in
  let match_exp =
    aexp(ematch (aexp (evar aedge_var, Some Typing.edge_ty, Span.default))
           (optimizeBranches branches),
         transf.resty, Span.default) in
  (* create fun m -> trans_hat_body *)
  let trans_hat_msg = efunc {arg=messageArg; argty=transf.argty; resty=transf.resty;
                             body=match_exp} in
  (*return fun e_hat m -> trans_hat_body *)
  efunc {arg=aedge_var; argty=Some Typing.edge_ty; resty= transuv.ety;
         body=trans_hat_msg}

let buildFailuresNet net k =
  let (failuresMap, failuresSym, failuresConstraint) =
    buildSymbolicFailures (AdjGraph.edges net.graph) k
  in
  let transMap =
    Nv_slicing.Slicing.partialEvalOverEdges (AdjGraph.edges net.graph) net.trans
  in
  {net with trans = buildFailTrans net.graph transMap net.attr_type failuresMap;
            requires = failuresConstraint :: net.requires;
            symbolics = failuresSym @ net.symbolics
  }
