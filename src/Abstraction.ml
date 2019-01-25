open AdjGraph
open AbstractionMap
open Unsigned
open Console
open Srp
open Hashtbl
open Syntax
open BatSet

let debugAbstraction = ref false

exception Cutoff

let zero = Integer.create ~value:0 ~size:32
let one = Integer.create ~value:1 ~size:32
                                       
(** Sets of Abstract Nodes *)
module AbstractNodeSet : BatSet.S with type elt = AbstractNode.t = BatSet.Make(AbstractNode)
module AbstractNodeMap = BatMap.Make(AbstractNode)

(** Sets of Abstract Node Ids *)
module AbsIdSet = BatSet.Make(UInts)
module AbsIdSetMap = BatMap.Make(AbsIdSet)
module AbsIdSetSet = BatSet.Make(AbsIdSet)

(** transfer hash, abstract id *)
module TransAbsId =
  struct
    type t = int * abstrId

    let compare (x1,x2) (y1,y2) =
      let cmp = Pervasives.compare x1 y1 in
      if cmp = 0 then
        Integer.compare x2 y2
      else
        cmp
      
  end
module TransAbsIdSet = BatSet.Make(TransAbsId)

(** merge_hash * {(trans_hash, abstractId)}*)
module PolicyAbsId =
  struct
    type t = int * TransAbsIdSet.t
           
    let compare ((m1, x1) : t) ((m2, x2) : t) =
      if (Pervasives.compare m1 m2 = 0) then
        TransAbsIdSet.compare x1 x2
      else Pervasives.compare m1 m2
  end
module PolicyAbsIdSet = BatSet.Make(PolicyAbsId)
module PolicyAbsIdMap = BatMap.Make(PolicyAbsId)
                 
let groupVerticesByAbsId (umap: (AbsIdSet.t) VertexMap.t) : VertexSetSet.t =
  let reverseMap : VertexSet.t AbsIdSetMap.t =
    VertexMap.fold (fun u vhat acc ->
        AbsIdSetMap.modify_def (VertexSet.singleton u) vhat (fun us -> VertexSet.add u us) acc)
                   umap AbsIdSetMap.empty in
  AbsIdSetMap.fold (fun _ v acc -> VertexSetSet.add v acc)
                   reverseMap VertexSetSet.empty
                 
(** ** Topological only abstraction *)
(* This does not handle a forall-forall abstraction. *)  
let refineTopological (f: abstractionMap) (g: AdjGraph.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : AbsIdSet.t VertexMap.t) =
    BatList.fold_left (fun acc v ->
        let vhat = getId f v in
        VertexMap.modify_opt u (fun omapu ->
                            match omapu with
                            | None -> Some (AbsIdSet.singleton vhat)
                            | Some vs -> Some (AbsIdSet.add vhat vs)) acc) umap
                   (neighbors g u)
  in
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  VertexSetSet.fold (fun us f' -> AbstractionMap.split f' (AbstractNode.fromSet us))
                    (groupVerticesByAbsId vmap) f

let abstractionTopological (f: abstractionMap) (g: AdjGraph.t) : abstractionMap =
  let rec loop fi =
    let f' = AbstractionMap.fold (fun us facc ->
                 if (AbstractNode.cardinal us > 1) then
                   refineTopological facc g us 
                 else
                   facc) fi fi in
    if (size fi = size f') then normalize f' 
    else loop f'
  in
  loop f

(** * Proper policy+topology abstraction *)  

let groupVerticesByPolicyAbsId (umap: (PolicyAbsId.t) VertexMap.t) : VertexSetSet.t =
  let reverseMap : VertexSet.t PolicyAbsIdMap.t =
    VertexMap.fold (fun u vhat acc ->
        PolicyAbsIdMap.modify_def (VertexSet.singleton u)
                                    vhat (fun us -> VertexSet.add u us) acc)
                   umap PolicyAbsIdMap.empty in
  PolicyAbsIdMap.fold (fun _ v acc -> VertexSetSet.add v acc)
              reverseMap VertexSetSet.empty
  
let refineAbstraction (f: abstractionMap) (g: AdjGraph.t)
                      (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                      (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : PolicyAbsId.t VertexMap.t) =
    BatList.fold_left (fun acc v ->
        let vhat = getId f v in
        let (trans_pol, _) = Hashtbl.find transMap (u,v) in
        VertexMap.modify_opt u (fun omapu ->
                            match omapu with
                            | None ->
                               let (merge_pol, _) = Hashtbl.find mergeMap u in
                               Some (merge_pol, TransAbsIdSet.singleton (trans_pol, vhat))
                            | Some (mp, vs) ->
                               Some (mp, TransAbsIdSet.add (trans_pol, vhat) vs))
                          acc) umap (neighbors g u)
  in
  (* for each node u in us, find the (abstract) nodes it's connected to and their policy *)
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  VertexSetSet.fold (fun us f' -> AbstractionMap.split f' (AbstractNode.fromSet us))
                    (groupVerticesByPolicyAbsId vmap) f

let abstraction (f: abstractionMap) (g: AdjGraph.t)
                    (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                    (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t) : abstractionMap =
  let rec loop fi =
    let f' = AbstractionMap.fold (fun us facc ->
                 if (AbstractNode.cardinal us > 1) then
                   refineAbstraction facc g transMap mergeMap us
                 else
                   facc) fi fi in
    if (size fi = size f') then normalize f'
    else loop f'
  in
  loop f

let partialEvalTrans (graph : AdjGraph.t)
                     (trans : Syntax.exp) : (Edge.t, int * Syntax.exp) Hashtbl.t  =
  let edge_to_val e = vtuple [vint (fst e); vint (snd e)] in
  let es = AdjGraph.edges graph in
  let tbl = Hashtbl.create (BatList.length es) in
  BatList.iter (fun e ->
      let ptrans = Interp.interp_partial_fun trans [edge_to_val e] in
      Hashtbl.add tbl e ((Syntax.hash_exp ~hash_meta:false ptrans), ptrans)) es;
  tbl

let partialEvalMerge (graph : AdjGraph.t)
                     (merge : Syntax.exp) : (Vertex.t, int * Syntax.exp) Hashtbl.t =
  let node_to_val n = vint n in
  let ns = AdjGraph.get_vertices graph in
  let tbl = Hashtbl.create (VertexSet.cardinal ns) in
  VertexSet.iter (fun v ->
      let pmerge = Interp.interp_partial_fun merge [node_to_val v] in
      Hashtbl.add tbl v (Syntax.hash_exp ~hash_meta:false pmerge, pmerge)) ns;
  tbl

(* Given a concrete graph g, an abstraction function f and an abstract
   node id returns its abstract edges *)
let findAbstractEdges (g: AdjGraph.t) (f: abstractionMap) (uhat: abstrId) : EdgeSet.t =
  let repru = getGroupRepresentativeId f uhat in
  let ns = neighbors g repru in
  BatList.fold_left (fun acc v -> EdgeSet.add (uhat, getId f v) acc) EdgeSet.empty ns

(* Given a concrete graph, transfer, merge functions a destinations
   computes an abstract network *)
let findAbstraction (graph: AdjGraph.t)
                    (transMap : (Edge.t, int * Syntax.exp) Hashtbl.t)
                    (mergeMap : (Vertex.t, int * Syntax.exp) Hashtbl.t)
                    (ds: VertexSet.t) : abstractionMap =
  (* Separate destination nodes from the rest *)
  let f =
    VertexSet.fold (fun d facc ->
        AbstractionMap.split facc (AbstractNode.singleton d))
                   ds (createAbstractionMap graph) in
  (* compute the abstraction function *)
  let f = abstraction f graph transMap mergeMap in
  f

(** * Functions related to creating the declarations of an abstract network *)
module BuildAbstractNetwork =
  struct
    
    (* Given a concrete graph and an abstraction function returns the node
   and edges of the abstract graph *)
    let buildAbstractAdjGraphDecls (g: AdjGraph.t) (f: abstractionMap)
        : Integer.t * (Edge.t list) =
      let n = Integer.create ~value:(size f) ~size:32 in
      let rec edges uhat =
        if uhat = n then EdgeSet.empty
        else
          EdgeSet.union (findAbstractEdges g f uhat) (edges (Integer.succ uhat))        
      in
      (n, EdgeSet.to_list (edges zero))

    let buildAbstractAdjGraph (g: AdjGraph.t) (f: abstractionMap) : AdjGraph.t =
      let n = Integer.create ~value:(size f) ~size:32 in
      let ag = AdjGraph.create n in
      fold_vertices (fun uhat ag ->
          let es = findAbstractEdges g f uhat in
          EdgeSet.fold (fun e ag -> add_edge ag e) es ag) n ag
      
    (* Helper function that constructs an MGet expression *)
    let mget (m : exp) (i : exp) : exp =
      eop MGet [m; i]

    let failuresConstraint_arith (k: int) (aedges : Edge.t list)
                                 (failuresMap: Var.t EdgeMap.t) : Syntax.exp =
      (*building the requires clause that requires
        fail1 + fail2 + .. <= k *)
      let bool2int_exp arg =
        aexp (eif arg (e_val (vint one)) (e_val (vint zero)),
              Some Typing.node_ty, Span.default)
      in
      let failuresSum =
        BatList.fold_left (fun acc (uhat, vhat) ->
            aexp (eop (UAdd 32)
                      [(bool2int_exp (evar (EdgeMap.find (uhat, vhat) failuresMap))); acc],
                  Some Typing.node_ty, Span.default))
                       (e_val (vint zero)) aedges in
      aexp(eop (ULeq 32)
               [failuresSum;
                e_val (vint (Integer.create ~value:k ~size:32))],
           Some TBool, Span.default)
      
    let failuresConstraint_pb (k: int) (failuresMap: Var.t EdgeMap.t) : Syntax.exp =
      let arg1 = aexp(etuple (EdgeMap.fold (fun _ fv acc ->
                                  (aexp (evar fv, Some TBool, Span.default)) :: acc)
                                           failuresMap []),
                      Some (TTuple (BatList.init (EdgeMap.cardinal failuresMap)
                                                 (fun _ -> TBool))),
                      Span.default
                     )
      in
      let arg2 =
        aexp(etuple (EdgeMap.fold (fun _ _ acc ->
                         (exp_of_value
                            (avalue (vint (Integer.of_int 1),
                                     Some (TInt 32),
                                     Span.default))) :: acc)
                                  failuresMap []),
             Some (TTuple (BatList.init (EdgeMap.cardinal failuresMap)
                                        (fun _ -> TInt 32))),
             Span.default
            )
      in
      let arg3 = exp_of_value (avalue (vint (Integer.of_int k),
                                       Some (TInt 32),
                                       Span.default))
      in
      aexp (eop (AtMost (EdgeMap.cardinal failuresMap)) [arg1; arg2; arg3],
            Some TBool,
            Span.default)

      
    let buildSymbolicFailures (aedges : Edge.t list) (k : int) =
      (* symbolic variables of failures, one for each abstract edge *)
      let failuresMap =
        BatList.fold_left (fun acc (u,v) ->
            let e = Printf.sprintf "%s-%s" (Vertex.printVertex u) (Vertex.printVertex v) in
            let failVar = Var.fresh ("failed-" ^ e) in
            EdgeMap.add (u,v) failVar acc) EdgeMap.empty aedges in

      let failures_leq_k = failuresConstraint_pb k failuresMap in
      (*build and returning the declarations *)
      (failuresMap, (EdgeMap.fold (fun _ fvar acc ->
                         (DSymbolic (fvar, Ty TBool) :: acc)) failuresMap
                                 [DRequire failures_leq_k]))

    let deconstructFun exp =
      match exp.e with
      | EFun f ->
         f
      | _ -> failwith "expected a function"
           
    (* get all the concrete neighbors v of u s.t. f(v) = vhat *)
    let getNeighborsInVhat f g u vhat =
      BatList.filter_map (fun v ->
          if (getId f v = vhat) then Some (u,v) else None) (neighbors g u)
           
    (* Given the abstract edges and a concrete transfer function, 
   synthesizes an abstract transfer function. *)
    let buildAbstractTrans
          (g : AdjGraph.t)
          (aedges : Edge.t list)
          (trans: (Edge.t, int * Syntax.exp) Hashtbl.t)
          (attrTy: Syntax.ty)
          (failuresMap : Var.t EdgeMap.t)
          (f: abstractionMap) : Syntax.exp =
      (* edge argument used by abstract transfer function *)
      let aedge_var = Var.create "edge" in
      
      (* code that implements check for a failed edge *)
      let failCheck fvar body =
        aexp(eif (aexp(evar fvar, Some TBool, Span.default))
                 (Syntax.default_exp_value attrTy)
                 body, Some attrTy, Span.default)in
      
      (* inserting that code in the body of the transfer function *)
      let addFailureCheck fvar exp = (deconstructFun exp).body |> (failCheck fvar) in
      
      (* for each abstract edge, find it's corresponding concrete
         transfer function and augment it with a check for whether it's
         failed *)
      let branches =
        BatList.fold_left (fun acc (uhat, vhat) ->
            let p = PTuple [PInt uhat; PInt vhat] in
            let u = getGroupRepresentativeId f uhat in
            match getNeighborsInVhat f g u vhat with
            | [] -> failwith "There must be a concrete edge
                              corresponding to the abstract edge"
            | uv :: _ -> 
               let (_, transuv) = Hashtbl.find trans uv in
               (* Printf.printf "transuv: %s\n" (Syntax.show_exp ~show_meta:true transuv); *)
               (p, addFailureCheck (EdgeMap.find (uhat, vhat) failuresMap) transuv) :: acc)
                       [] aedges
      in
      
      (* partial evaluted trans functions are of the form fun m -> ..., grab m *)

      let transuv =
        match aedges with
        | [] -> failwith "No edges found"
        | (uhat, vhat) :: _ ->
           let u = getGroupRepresentativeId f uhat in
           match getNeighborsInVhat f g u vhat with
           | [] -> failwith "There must be a concrete edge
                             corresponding to the abstract edge"
           | uv :: _ -> 
              let (_, transuv) = Hashtbl.find trans uv in
              transuv
      in
      let transf = deconstructFun transuv in
      let messageArg = transf.arg in
      let match_exp =
        aexp(ematch (aexp (evar aedge_var, Some Typing.edge_ty, Span.default)) branches,
             transf.resty, Span.default) in
      (* create fun m -> trans_hat_body *)
      let trans_hat_msg = efunc {arg=messageArg; argty=transf.argty; resty=transf.resty;
                                 body=match_exp} in
      (*return fun e_hat m -> trans_hat_body *)  
      efunc {arg=aedge_var; argty=Some Typing.edge_ty; resty= transuv.ety;
             body=trans_hat_msg}

    (* Given the number of abstract nodes and a concrete merge function, 
   synthesizes an abstract merge function. *)
    let buildAbstractMerge (n : Integer.t)
                           (merge: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                           (f: abstractionMap) : Syntax.exp =
      (* vertex argument used by abstract merge function *)
      let avertex_var = Var.create "node" in

      let _, merge0 = Hashtbl.find merge zero in
      let merge0x = deconstructFun merge0 in
      let merge0y = deconstructFun merge0x.body in
      
      (* get attribute arguments *)
      let xvar, yvar =
        (merge0x.arg, merge0y.arg) in
      (* for each abstract node, find it's corresponding concrete
      merge function. *)
      let rec branches uhat =
        if uhat = n then []
        else
          let p = PInt uhat in
          let u = getGroupRepresentativeId f uhat in
          let (_, mergeu) = Hashtbl.find merge u in
          let mergeu0 = deconstructFun mergeu in
          let mergeu1 = deconstructFun mergeu0.body in
          (p, aexp(mergeu1.body, mergeu1.resty, Span.default)) :: (branches (Integer.succ uhat))
      in
      (* create a match on the node expression *)
      let match_exp =
        aexp(ematch (aexp (evar avertex_var, Some Typing.node_ty, Span.default)) (branches zero),
                     merge0y.resty, Span.default)
      in
      (* create a function from attributes *)
      efunc {arg=avertex_var; argty= Some Typing.node_ty; resty = merge0.ety;
             body= efunc {arg=xvar; argty = merge0x.argty; resty = merge0x.resty;
                          body = efunc {arg=yvar; argty=merge0y.argty; resty = merge0y.resty;
                                        body = match_exp}}}
      (* Syntax.lam avertex_var (Syntax.lam xvar (Syntax.lam yvar match_exp)) *)

    (* Constructs the init function for the abstract network. Nodes in
       the set dst have the invariant that they announce the same
       prefixes *)
    let buildAbstractInit (dst: VertexSet.t)
                          (initMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                          (attrTy : Syntax.ty)
                          (f: abstractionMap) : Syntax.exp =
      (* vertex argument used by abstract init function *)
      let avertex_var = Var.create "node" in

      (* Grab one of the destination nodes *)
      let (d, dst') = VertexSet.pop_min dst in
      (* Grab its initial value *)
      let vinit = (Hashtbl.find initMap d) in
      let b = (PInt (getId f d), vinit) in
      (* This is the default initial value for all other nodes.
     Assuming default_value computes the value we want..*)
      let default_attr = default_exp_value attrTy in
      let default_branch = (PWild, default_attr) in
      (* compute the branches of the initial expression *)
      let branches = VertexSet.fold (fun u acc ->
                         let uhat = getId f u in
                         let p = PInt uhat in
                         (p, vinit) :: acc) dst' ([b; default_branch]) in
      (*build the match expression *)
      let match_exp =
        aexp (ematch (aexp (evar avertex_var, Some Typing.node_ty, Span.default)) branches,
              vinit.ety, Span.default) in
      (*return the function "init node = ..." *)
      efunc {arg=avertex_var; argty=Some Typing.node_ty; resty=Some attrTy;
             body=match_exp}

    (* Constructs the assertion function for the abstract network.*)
    (* TODO: we also need to slice the assertion function to only refer to
   prefixes of the current SRP *)
    (* Invariant: This assumes that nodes in the same abstract group have
   the same assertion. *)
    let buildAbstractAssert (assertionMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                            (f: abstractionMap) : Syntax.exp =
      (* vertex argument used by abstract init function *)
      let avertex_var = Var.create "node" in
      
      (* get abstract nodes *)
      let n = Integer.of_int (AbstractionMap.size f) in

      (* get the argument name of the attribute *)
      let mineu = Hashtbl.find assertionMap zero in
      let mineufun = deconstructFun mineu in
      let messageArg = mineufun.arg in
      
      (* for each abstract node, find it's corresponding concrete
      assertion function. *)
      let rec branches uhat =
        if uhat = n then []
        else
          let p = PInt uhat in
          let u = getGroupRepresentativeId f uhat in
          let assertu = Hashtbl.find assertionMap u in
          let assertubody = (deconstructFun assertu).body in
          (p, assertubody) :: (branches (Integer.succ uhat))
      in
      
      (* create a match on the node expression *)
      let match_exp =
        aexp (ematch (aexp (evar avertex_var, Some Typing.node_ty, Span.default)) (branches zero),
              mineu.ety, Span.default) in
      let assert_msg = efunc {arg=messageArg; argty=mineufun.argty;
                              resty=mineufun.resty; body=match_exp} in
      (*return fun uhat m -> assert_hat_body *)  
      efunc {arg=avertex_var; argty=Some Typing.node_ty; resty=mineu.ety; body=assert_msg}
      
      
    (* Given an abstraction function, a concrete graph, transfer and merge
   function, and the number of maximum link failures builds an
   abstract network *)
    let buildAbstractNetwork (f: abstractionMap)
                             (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                             (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                             (slice: Slicing.network)
                             (k: int) =
      (* build the abstract graph based on the abstraction function *)
      let (n, edgeshat) = buildAbstractAdjGraphDecls slice.graph f in
      (* build the symbolic representation of failures *)
      (*TODO: make this a separate transformation?*)
      let (failuresMap, symbolics) = buildSymbolicFailures edgeshat k in
      (* build the abstract merge function *)
      let mergehat = buildAbstractMerge n mergeMap f in
      (* build the abstract transfer function *)
      let transhat =
        buildAbstractTrans slice.graph edgeshat transMap slice.attr_type failuresMap f
      in
      (* build the abstract init function *)
      let initMap = Slicing.partialEvalOverNodes (num_vertices slice.graph) slice.init in
      let inithat = buildAbstractInit slice.destinations initMap slice.attr_type f in
      (* build the abstract assert function *)
      let assertMap =
        Slicing.partialEvalOverNodes (num_vertices slice.graph) slice.assertion
      in
      let asserthat = buildAbstractAssert assertMap f in
      if !debugAbstraction then
        begin
          let agraph = AdjGraph.add_edges (AdjGraph.create n) edgeshat in
          AdjGraph.print agraph
        end;
      (failuresMap, (DATy slice.attr_type) :: (DNodes n) :: (DEdges edgeshat) :: symbolics
                    @ slice.symbolics
                    @ ((DMerge mergehat) :: (DTrans transhat) :: (DInit inithat)
                       :: [DAssert asserthat]))

    let abstractToConcreteEdge (g: AdjGraph.t) (f: abstractionMap) (ehat: Edge.t) : EdgeSet.t =
      let (uhat, vhat) = ehat in
      let us = getGroupById f uhat in (* get nodes represented by uhat *)
      AbstractNode.fold
        (fun u acc ->
          EdgeSet.union (EdgeSet.of_list (getNeighborsInVhat f g u vhat)) acc) us EdgeSet.empty
      
    let getEdgeMultiplicity (g: AdjGraph.t) (f: abstractionMap) (ehat: Edge.t) : int =
      EdgeSet.cardinal (abstractToConcreteEdge g f ehat)

    let getEdgeMultiplicities (g: AdjGraph.t) (f: abstractionMap)
                              (fvars: Var.t AdjGraph.EdgeMap.t) =
      EdgeMap.fold (fun ehat var acc ->
          Collections.StringMap.add (Var.name var) (getEdgeMultiplicity g f ehat) acc)
                   fvars Collections.StringMap.empty

  end
      
(* For failures we don't really need to care about the policies when
   computing a new abstraction as those have already been factored in
   and we are only splitting things. We just have to ensure a
   topological abstraction (forall-exists). *)
module FailuresAbstraction =
  struct
    type splittings = Mesh | Groups of AbstractNodeSet.t

    let groupAbsNodesByVertexSet (umap: VertexSet.t VertexMap.t) : AbstractNodeSet.t =
      let reverseMap : AbstractNode.t AbstractNodeMap.t =
        VertexMap.fold (fun u vhat acc ->
            let vhat = AbstractNode.fromSet vhat in
            AbstractNodeMap.modify_def
              (AbstractNode.singleton u) vhat
              (fun us -> AbstractNode.add u us) acc)
                       umap AbstractNodeMap.empty in
      AbstractNodeMap.fold (fun _ v acc -> AbstractNodeSet.add v acc)
                           reverseMap AbstractNodeSet.empty
                                     
    (* For each abstract node [uhat] and [vhat], partitions the concrete
       nodes in uhat into subsets s.t. that nodes in the same subset have
       edges to the same concrete nodes in [vhat] *)                              
    let findSplittingByConnectivity (uhat : AbstractNode.t) (vhat : AbstractNode.t)
                         (g: AdjGraph.t) : splittings = 
      let addNeighbor u =
        let neighborsOfu = neighbors g u in
        let neighborsOfUinV =
          BatList.filter (fun v -> AbstractNode.mem v vhat) neighborsOfu
        in
        VertexSet.of_list neighborsOfUinV
      in
      let connectivityMap = AbstractNode.fold (fun u acc ->
                                VertexMap.add u (addNeighbor u) acc)
                              uhat VertexMap.empty in
      let us = groupAbsNodesByVertexSet connectivityMap in
      if ((AbstractNodeSet.cardinal us) = 1) then
        Mesh
      else
        Groups us


    (* Given a group of abstract nodes, creates two new abstract
       nodes, trying to maintain the other abstract nodes.
       This is done as follows:
       if {u1,u2,u3} and {u4,u5,u6} are two abstract groups each with same connectivity,
       the new abstract nodes are {u1,u4,u3,u6} {u2,u5} i.e. picking
       one node from each group *)
    let createFreshAbstractNodes (uss: AbstractNodeSet.t) =
      if AbstractNodeSet.cardinal uss > 2 then
        begin
          let (_, us1, us2) =
            AbstractNodeSet.fold (fun us (b, us1, us2) ->
                if (AbstractNode.cardinal us) > 1 then
                  let usl, usr = AbstractNode.randomSplit us in
                  (b, AbstractNode.union usl us1, AbstractNode.union usr us2)
                else
                  if b then
                    (not b, AbstractNode.union us us1, us2)
                  else
                    (not b, us1, AbstractNode.union us us2)) uss
                                 (true, AbstractNode.empty, AbstractNode.empty)
          in
          AbstractNodeSet.add us2 (AbstractNodeSet.singleton us1)
        end
      else
        uss
          
    (** Returns true if the given value is not the default for the
       given attribute type. A non-default value indicates that this
       message has a path to the destination *)
    let validAttribute (attrTy: Syntax.ty) (m : Syntax.value) : bool =
      not (equal_values ~cmp_meta:false (default_value attrTy) m)
      
    let splitSet_debug us =
      if !debugAbstraction then
        Printf.printf "splitting set:%s\n" (AbstractNode.printAbstractNode us)
      
    (* Repeatedly split to create the abstract nodes in [uss] *)
    let splitSet f (uss : AbstractNodeSet.t) : abstractionMap =
      AbstractNodeSet.fold
        (fun us f' -> splitSet_debug us; AbstractionMap.split f' us) uss f
      
    let refineForFailures_debug (f: abstractionMap) =
      if !debugAbstraction then
        show_message (printAbstractGroups f "\n") T.Blue
                     "Abstract groups after refine for failures "

    let compare_refinements f f' =
      Pervasives.compare (AbstractionMap.normalized_size f)
                         (AbstractionMap.normalized_size f')


    (* given a refined abstraction f and a previous abstraction forig,
       returns the abstract node that uhat belonged to before being
       refined *)
    let get_orig_group forig f (uhat: abstrId) =
      let repr = getGroupRepresentativeId f uhat in
      getId forig repr
      
    module VertexFreq =
      struct
        type t = int * Vertex.t
        let compare (f1, u1) (f2, u2) =
          let fcmp = Pervasives.compare f1 f2 in
          if fcmp = 0 then
            Vertex.compare u1 u2
          else
            fcmp
      end

    module VertexFreqSet = BatSet.Make(VertexFreq)

    let rec updateList (u: 'a) (f: 'b option -> 'b) (xs: ('a*'b) list) =
      match xs with
      | [] -> [(u,f None)]
      | (x,y) :: xs ->
         if (x = u) then
           (x, f (Some y)) :: xs
         else
           (x,y) :: (updateList u f xs)

        
    (* given a list of cut-sets, returns: 
       1. the reachable nodes that
       appear in the cut-sets sorted by their frequency.
       2. the reachables nodes groupped by their original abstraction.
       3. the unreachable nodes groupped by their original abstraction.*)
    let cuts_choices forig f (cuts: EdgeSet.t list)
        : ((abstrId * int) list) * ((abstrId list) GroupMap.t) * ((abstrId list) GroupMap.t) =
      let accfreq, accReachAbs, accUnreachAbs =
        BatList.fold_left (fun acc cutset ->
            EdgeSet.fold (fun (u,v) (accfreq, accReachAbs, accUnreachAbs) ->
                (updateList u (fun freq -> match freq with
                                           | None -> 1
                                           | Some f -> f+1) accfreq,
                 (let uorig = get_orig_group forig f u in
                  GroupMap.modify_def [u] uorig
                                      (fun us -> u :: us) accReachAbs),
                 (let vorig = get_orig_group forig f v in
                  GroupMap.modify_def [v] vorig
                                      (fun vs -> v :: vs) accReachAbs))) cutset acc)
                       ([], GroupMap.empty, GroupMap.empty) cuts
      in
      let accfreq = BatList.sort (fun (_,f) (_,f') -> Pervasives.compare f' f) accfreq in 
      (accfreq, accReachAbs, accUnreachAbs)

    (* finds the minimum entry of the map that satisfies p, raises Not_found. *)
    let findPred (p: 'a -> bool) (m: 'a GroupMap.t) =
      let rec loop m =
        let (k,v), m = GroupMap.pop_min_binding m in
        if p v then (k, v)
        else loop m
      in loop m

    (* returns the first n elements that satisfy p *)
    let findNPred (p: 'a -> bool) (m: 'a GroupMap.t) n =
      let rec loop m acc sz =
        if GroupMap.is_empty m then
          if acc = [] then raise Not_found else acc
        else
          let (k,v), m = GroupMap.pop_min_binding m in
          if p v then
            if sz+1 = n then
              (v :: acc)
            else
              loop m (v :: acc) (sz+1)
          else loop m acc sz
      in loop m [] 0
   
    (* creates a map from abstract nodes in f to the nodes that they
       were split to in fnew *)
    let buildForwardMap (f: abstractionMap) (fnew: abstractionMap) =
      AbstractionMap.foldi (fun uhat _ acc ->
          let uhat_orig = get_orig_group f fnew uhat in
          GroupMap.modify_def [uhat] uhat_orig (fun us -> uhat :: us) acc)
                           fnew GroupMap.empty
      
      
    (* given a set of nodes in the abstraction f that need to be
       checked for min-cut, returns a new set of nodes in fnew, a
       refinement of f, that should be checked for min-cut *)
    let update_vertex_set backMap (vs: VertexSet.t) =
      VertexSet.fold (fun uorig acc ->
          let us = GroupMap.find uorig backMap in
          BatList.fold_left (fun acc u ->
              VertexSet.add u acc) acc us) vs VertexSet.empty

    (* g is the graph that corresponds to the new abstraction *)
    let update_edge_set backMap (g: AdjGraph.t) (es: EdgeSet.t) =
      EdgeSet.fold (fun (uorig,vorig) acc ->
          let us = GroupMap.find uorig backMap in
          let vs = GroupMap.find vorig backMap in
          BatList.fold_left (fun acc u ->
              let ns = neighbors g u in
              BatList.fold_left (fun acc n ->
                  if BatList.mem n vs then
                    EdgeSet.add (u,n) acc
                  else acc) acc ns) acc us) es EdgeSet.empty

    (* Returns a pair of cuts and set of vertices that have min-cuts <= k *)
    let compute_cuts (g : AdjGraph.t) (d: abstrId) k (todo: VertexSet.t) =
      let rec loop todo cuts new_todo =
        try
          let u, todo' = VertexSet.pop_min todo in
          if u <> d then
            begin
              let (es, sset, tset) =  min_cut g d u in
              if EdgeSet.cardinal es > k then
                loop todo' cuts new_todo
              else
                loop (VertexSet.diff todo' tset) (es :: cuts) (VertexSet.union tset new_todo)
            end
          else
            loop todo' cuts new_todo
        with | Not_found -> (cuts, new_todo)
      in loop todo [] VertexSet.empty


    module SearchElt =
      struct
        type t = abstractionMap * VertexSet.t
        let compare (x1,y1) (x2,y2) =
          let sz = Pervasives.compare (normalized_size x1) (normalized_size x2) in
          if sz = 0 then
            VertexSet.compare y1 y2
          else
            sz
      end 

    module FSet = BatSet.Make(SearchElt)

    module type SearchStruct =
      sig
        type elt = SearchElt.t
        type t

        val create: unit -> t
        val add: elt -> t -> t
        val pop: t -> elt * t
        val iter: (elt -> 'a -> 'a) -> t -> 'a -> 'a
        val length: t -> int
        val prune: t -> t
      end

    module SearchSet : SearchStruct =
      struct
        type elt = SearchElt.t
        type t = FSet.t

        let create () = FSet.empty
        let add x s = FSet.add x s
        let pop s = FSet.pop_min s
        let iter f s v = FSet.fold f s v
        let length s = FSet.cardinal s
        let prune s =
          let fmin,_ = FSet.min_elt s in
          FSet.filter (fun (f,_) ->
              if ((normalized_size fmin)*2 > normalized_size f) then
                true
              else
                false) s
      end

    module QueueSet : SearchStruct =
      struct
        type elt = SearchElt.t
        type t = elt Queue.t

        let create () = Queue.create ()
        let add x s = Queue.add x s; s
        let pop s = try let x = Queue.pop s in
                        (x, s)
                    with Queue.Empty -> raise Not_found
        let iter f s v = Queue.fold (fun acc x ->
                             f x acc) v s
        let length q = Queue.length q
        let prune q = q (*not yet implemented for queues*)
      end
       
    let countererexample_refinement_breadth = 20

    let choose_random_splittable f (es:EdgeSet.t list) =
      BatList.fold_left (fun acc es ->
          EdgeSet.fold (fun (u,v) acc ->
              let acc =
                if AbstractNode.cardinal (getGroupById f u) > 1 then
                  (u :: acc)
                else
                  acc
              in
              if AbstractNode.cardinal (getGroupById f v) > 1 then
                (v :: acc)
              else
                acc) es []) [] es

    let counterexample_step (g: AdjGraph.t) forig (f: abstractionMap) (todo: VertexSet.t)
                            (unused: EdgeSet.t) ds k =
      let ag = BuildAbstractNetwork.buildAbstractAdjGraph g f in
      let backMap = buildForwardMap forig f in
      let unused_new = update_edge_set backMap ag unused in
      (* compute the abstract graph after removing the unused edges *)
      let rag = EdgeSet.fold (fun e acc -> AdjGraph.remove_edge acc e) unused_new ag in
      let d = getId f (VertexSet.choose ds) in (*assume only one destination for now *)
      let cuts, todo = compute_cuts rag d k todo in
      match cuts with
      | [] -> (* no min-cuts <= k, we are done. *)
         assert (VertexSet.is_empty todo);
         []
      | _ ->
         (* sort (reachable) vertices by frequency of appereance in cut-sets. *)
         let (cut_freq, reachAbs, unreachAbs) = cuts_choices forig f cuts in
         let most_freq =
           try
             [fst (BatList.find (fun (u,_) ->
                       AbstractNode.cardinal (getGroupById f u) > 1) cut_freq)]
           with Not_found -> []
         in

         let nodes_to_split_1 =
           try (findNPred (fun us ->
                    BatList.for_all (fun u ->
                                AbstractNode.cardinal (getGroupById f u) > 1) us)
                          reachAbs 1)
           with Not_found ->  []
         in
         let nodes_to_split_2 = 
           try (findNPred (fun us ->
                    BatList.for_all (fun u ->
                        AbstractNode.cardinal (getGroupById f u) > 1) us)
                          unreachAbs 1)
           with Not_found ->
             []
         in
         let nodes_to_split = nodes_to_split_1 @ nodes_to_split_2 in
         let nodes_to_split =
           match nodes_to_split with
           | [] ->
              (match choose_random_splittable f cuts with
               | [] ->
                  []
               | x ->
                  (* Printf.printf "nodes to split:%d\n" (List.length x); *)
                  (* List.iter (fun u -> Printf.printf "nodes:%s" (Vertex.printVertex u)) x; *)
                  [x])
           | _ -> nodes_to_split
         in
         match nodes_to_split with
         | [] -> (* cannot refine further, return an empty list.*)
            []
         | uhatss ->
            (* for each element of the list, note that they all belong the same original group:
                 2. Get all their neighbors.
                 3. Try all refinements on them and pick the best.
                 2. if one of them is in the unreachable set, then try to refine based on that.
                 3. otherwise pick one randomly for now *)

            (* Remove duplicates based on cardinality, because they
               are likely to lead to similar refinements.*)
            let uhats =
              BatList.map (fun uhats ->
                  BatList.sort_unique (fun x y -> Pervasives.compare
                                                    (AbstractNode.cardinal (getGroupById f x))
                                                    (AbstractNode.cardinal (getGroupById f y)))
                                      uhats) uhatss
              |> BatList.flatten
            in
            (* add in the most_freq node *)
            let uhats = most_freq @ uhats in
            (* Printf.printf "size of uhats: %d\n" (List.length uhats); *)
            (* for each node to split, compute a refinement with each of its neighbor *)
            let uhat_neighbors = BatList.map (fun uhat -> (uhat, neighbors ag uhat)) uhats in
            let refinements =
              BatList.fold_left (fun acc (uhat, vhats) ->
                  let uhatGroup = getGroupById f uhat in
                  (BatList.filter_map
                     (fun vhat ->
                       let vhatGroup = getGroupById f vhat in
                       match findSplittingByConnectivity uhatGroup vhatGroup g with
                       | Mesh -> None
                       | Groups uss ->
                          let uss = createFreshAbstractNodes uss in
                          let f' = splitSet f uss in
                          Some (abstractionTopological f' g)) vhats) @ acc) [] uhat_neighbors
              |> BatList.sort (compare_refinements)
            in
            (* Printf.printf "size of refinements:%d\n" (List.length refinements); *)
            (*get k-best refinements (defined by
               refinement_breadth). If none are available, it means
               all of them are full mesh, so just split the node
               randomly. *)
            let best_refinements =
              BatList.take countererexample_refinement_breadth refinements |>
                BatList.sort_unique (fun x y -> compare_refinements x y)
            in
            match best_refinements with
            | [] -> (* if everything was a full mesh, take a random split *)
               let us1, us2 =
                 BatList.hd uhats |>
                   AbstractionMap.getGroupById f |>
                   AbstractNode.randomSplit
               in
               let uss = AbstractNodeSet.add us2 (AbstractNodeSet.singleton us1) in
               let f' = splitSet f uss in
               let f' = abstractionTopological f' g in
               let backMap = buildForwardMap f f' in
               [(f', update_vertex_set backMap todo)]
            | _ -> BatList.map (fun fnew ->
                       let backMap = buildForwardMap f fnew in
                       (fnew, update_vertex_set backMap todo)) best_refinements

    let counterExampleSearch (g: AdjGraph.t) (forig: abstractionMap)
                             (unused: EdgeSet.t)
                             (todo: VertexSet.t) ds k =
      let q = SearchSet.create () in
      let q = SearchSet.add (forig, todo) q in
      
      let rec loop explored minimum q =
        try
          let ((f, todo), q) = SearchSet.pop q in
          let b = match minimum with
            | None -> false 
            | Some minimumf ->
               if (compare_refinements minimumf f <= 0) then
                 true
               else
                 false
          in
          if b then
            loop (explored+1) minimum q
          else
            match counterexample_step g forig f todo unused ds k with
            | [] ->
               ( match minimum with
                 | None -> loop (explored+1) (Some f) q
                 | Some minimum ->
                    if (compare_refinements f minimum < 0) then
                      loop (explored+1) (Some f) q
                    else
                      loop (explored+1) (Some minimum) q)
            | fs ->
               (* If we have already find a refinement that is better
                   than the one we are exploring right now, then stop
                   exploring it *)
               let q = BatList.fold_left (fun acc (f,todo) ->
                           match minimum with
                           | None ->
                              SearchSet.add (f,todo) acc
                           | Some minimum ->
                              if compare_refinements f minimum = -1 then
                                SearchSet.add (f,todo) acc
                              else acc) q fs in
               loop explored minimum q
        with
          Not_found -> explored, minimum
      in
      match loop 0 None q with
      | explored, Some f ->
         Printf.printf "Explored refinements: %d\n" explored;
         f
      | _, _ ->
         failwith "found no refinement"

    let refineCounterExample (draw: bool) (file: string) (g: AdjGraph.t)
                          (fbonsai: abstractionMap) (f: abstractionMap)
                          (failVars: Var.t EdgeMap.t) (sol: Solution.t) (k: int)
                          (* (unused_edges: EdgeSet.t) *)
                          (dst: VertexSet.t) (attrTy : Syntax.ty)
                          (iteration: int): abstractionMap option =
      
      (* get set of failures, and also build abstract graph useful for
         splitting. Note that this code works if all edges can fail. *)
      let failures, agraph =
        EdgeMap.fold (fun edge fvar (acc, ag) ->
            let bv = Collections.StringMap.find (Var.name fvar) sol.symbolics in
            match bv.v with
            | VBool b ->
               if b then
                 begin
                   Printf.printf "Failed edge: %s\n" (AdjGraph.printEdge edge); 
                   (EdgeSet.add edge acc, AdjGraph.add_edge ag edge)
                 end
               else (acc, AdjGraph.add_edge ag edge)
            | _ -> failwith "This should be a boolean variable") failVars
                     (EdgeSet.empty,
                      AdjGraph.create (AbstractionMap.size f |> Integer.of_int))
      in

      (* Draw the abstract graph if asked *)
      if draw then
        begin
          let dotfile = AdjGraph.DrawableGraph.graph_dot_file k file in
          AdjGraph.DrawableGraph.drawGraph agraph dotfile
        end;

      (* number of concrete links failed in the network *)
      let total_failures =
        EdgeSet.fold (fun ehat acc ->
            (BuildAbstractNetwork.getEdgeMultiplicity g f ehat) + acc)
                     failures 0
      in
      if (total_failures <= k) then
        None
      else
        begin
          (* Find the set of unreachable nodes *)
          let unreachable =
            AdjGraph.fold_vertices (fun u acc ->
                if not (validAttribute attrTy (VertexMap.find u sol.labels)) then
                  VertexSet.add u acc
                else acc) (AdjGraph.num_vertices agraph) VertexSet.empty
          in
          (* and the set of edges that were not used for forwarding even though there
             were no failures *)
          let unused_edges =
            BatList.fold_left
              (fun acc (i,j) ->
                if VertexSet.mem j unreachable &&
                     (validAttribute attrTy (AdjGraph.VertexMap.find i sol.labels)) &&
                       (not (EdgeSet.mem (i,j) failures)) then
                  EdgeSet.add (i,j) acc
                else
                  acc) EdgeSet.empty (AdjGraph.edges agraph)
          in
          let fwdMap = buildForwardMap fbonsai f in
          (* find all the unused edges exploiting symmetry between transfer functions *)
          let unused_edges_sym =
            EdgeSet.fold (fun (u,v) acc ->
                let vorig = get_orig_group fbonsai f v in
                let vs = GroupMap.find vorig fwdMap in
                BatList.fold_left (fun acc v' ->
                    EdgeSet.add (u,v') acc) acc vs) unused_edges EdgeSet.empty
          in
          (* find all potentially unreachable nodes based on symmetries *)
          let unreachable_sym =
            VertexSet.fold (fun u acc ->
                let uorig = get_orig_group fbonsai f u in
                let us = GroupMap.find uorig fwdMap in
                BatList.fold_left (fun acc u ->
                    VertexSet.add u acc) acc us) unreachable VertexSet.empty
          in
          let f' = counterExampleSearch g f unused_edges_sym unreachable_sym dst k in
          Some f'
        end


    let refinement_breadth = 10
                                            
    let refine_step (g: AdjGraph.t) forig (f: abstractionMap) (todo: VertexSet.t) ds k =
      let ag = BuildAbstractNetwork.buildAbstractAdjGraph g f in
      let d = getId f (VertexSet.choose ds) in (*assume only one destination for now *)
      let cuts, todo = compute_cuts ag d k todo in
      (* AdjGraph.print ag; *)
      match cuts with
      | [] -> (* no min-cuts <= k, we are done. *)
         assert (VertexSet.is_empty todo);
         []
      | _ ->
         (* sort (reachable) vertices by frequency of appereance in cut-sets. *)
         let (cut_freq, reachAbs, unreachAbs) = cuts_choices forig f cuts in
         let most_freq =
           try
             [fst (BatList.find (fun (u,_) ->
                       AbstractNode.cardinal (getGroupById f u) > 1) cut_freq)]
           with Not_found -> []
         in
         (* require all of them to be in cut-set? *)
         let nodes_to_split =
           try (findNPred (fun us ->
                            BatList.for_all (fun u ->
                                AbstractNode.cardinal (getGroupById f u) > 1) us)
                          reachAbs 1)
           with Not_found ->
                 try (findNPred (fun us ->
                                   BatList.for_all (fun u ->
                                       AbstractNode.cardinal (getGroupById f u) > 1) us)
                                  unreachAbs 1)
                 with Not_found ->
                   match choose_random_splittable f cuts with
                   | [] -> []
                   | x -> [x]
         in
         match nodes_to_split with
         | [] -> (* cannot refine further.*)

            (*TODO: Don't automatically stop here, until we do this only for source nodes.
              Otherwise, we may be stopping if a non-source node can be cut-off *)
            (* Printf.printf "Nodes can be cut-off, and no further \
             *                refinements can be made. Verification will fail.\n";
             * BatList.iter (fun es ->
             *     Printf.printf "min-cut: ";
             *     EdgeSet.iter (fun ehat ->
             *         EdgeSet.iter (fun e ->
             *             Printf.printf "%s," (printEdge e))
             *                      (BuildAbstractNetwork.abstractToConcreteEdge g f ehat))
             *                  es;
             *     Printf.printf "\n")
             *              cuts;
             * raise Cutoff *)
            []
         | uhatss ->
            (* for each element of the list, note that they all belong the same original group:
                 2. Get all their neighbors.
                 3. Try all refinements on them and pick the best.
                 2. if one of them is in the unreachable set, then try to refine based on that.
                 3. otherwise pick one randomly for now, 
                     TODO: pick the one that is the most common among them *)

            (* Remove duplicates based on cardinality, because they
               are likely to lead to similar refinements.*)
            let uhats =
              BatList.map (fun uhats ->
                  BatList.sort_unique (fun x y -> Pervasives.compare
                                                    (AbstractNode.cardinal (getGroupById f x))
                                                    (AbstractNode.cardinal (getGroupById f y)))
                                      uhats) uhatss
              |> BatList.flatten
            in
            (* add in the most_freq node *)
            let uhats = most_freq @ uhats in
            (* for each node to split, compute a refinement with each of its neighbor *)
            let uhat_neighbors = BatList.map (fun uhat -> (uhat, neighbors ag uhat)) uhats in
            let refinements =
              BatList.fold_left (fun acc (uhat, vhats) ->
                  let uhatGroup = getGroupById f uhat in
                  (BatList.filter_map
                     (fun vhat ->
                       let vhatGroup = getGroupById f vhat in
                       match findSplittingByConnectivity uhatGroup vhatGroup g with
                       | Mesh -> None
                       | Groups uss ->
                          let uss = createFreshAbstractNodes uss in
                          let f' = splitSet f uss in
                          Some (abstractionTopological f' g)) vhats) @ acc) [] uhat_neighbors
              |> BatList.sort (compare_refinements)
            in
            (* Printf.printf "size of refinements:%d\n" (List.length refinements); *)
            (*get k-best refinements (defined by
               refinement_breadth). If none are available, it means
               all of them are full mesh, so just split the node
               randomly. *)
            let best_refinements =
              BatList.take refinement_breadth refinements |>
                BatList.sort_unique (fun x y -> compare_refinements x y)
            in
            match best_refinements with
            | [] -> (* if everything was a full mesh, take a random split *)
               let us1, us2 =
                 BatList.hd uhats |>
                   AbstractionMap.getGroupById f |>
                   AbstractNode.randomSplit
               in
               let uss = AbstractNodeSet.add us2
                                             (AbstractNodeSet.singleton us1)
               in
               let f' = splitSet f uss in
               let f' = abstractionTopological f' g in
               let backMap = buildForwardMap f f' in
               [(f', update_vertex_set backMap todo)]
            | _ -> BatList.map (fun fnew ->
                       let backMap = buildForwardMap f fnew in
                       (fnew, update_vertex_set backMap todo)) best_refinements
                 
    (* computes a refinement of f, s.t. all sources (currently sources
       are not defined, all nodes are considered sources) have at
       least k+1 disjoint paths to the destination *)
    (* TODO: find source nodes, we only want to min-cut source nodes *)
    let refineK (g: AdjGraph.t) (forig: abstractionMap) (ds: VertexSet.t) (k: int) =
      let q = SearchSet.create () in
      let todo =
        AdjGraph.fold_vertices
          (fun uhat acc -> VertexSet.add uhat acc)
          (AbstractionMap.normalized_size forig |> Integer.of_int) VertexSet.empty in
      let q = SearchSet.add (forig, todo) q in

      (* making minimum a reference, as an optimization on the final step*)
      let rec loop explored minimum q =
        try
          let ((f, todo), q) = SearchSet.pop q in
          let b =
            match minimum with
            | None -> false
            | Some minimumf ->
               if (compare_refinements minimumf f <= 0) then
                 true
               else
                 false
          in
          if b then
            loop (explored+1) minimum q
          else
            match refine_step g forig f todo ds k with
            | [] ->
               ( match minimum with
                 | None -> loop (explored+1) (Some f) q
                 | Some minimum ->
                    if (compare_refinements f minimum < 0) then
                      loop (explored+1) (Some f) q
                    else
                      loop (explored+1) (Some minimum) q)
            | fs ->
               (* If we have already find a refinement that is better
                   than the one we are exploring right now, then stop
                   exploring it *)
               let q = BatList.fold_left (fun acc (f,todo) ->
                           match minimum with
                           | None ->
                              SearchSet.add (f,todo) acc
                           | Some minimum ->
                              if compare_refinements f minimum = -1 then
                                SearchSet.add (f,todo) acc
                              else acc) q fs in
               loop explored minimum q
        with
          Not_found -> explored, minimum
      in
      match loop 0 None q with
      | explored, Some f ->
         Printf.printf "Explored refinements: %d\n" explored;
         (* for statistics only *)
         (* let ag = BuildAbstractNetwork.buildAbstractAdjGraph g f in *)
         (* let d = getId f (VertexSet.choose ds) in *)
         (* for u=0 to (AdjGraph.num_vertices ag |> Integer.to_int) do *)
         (*    let (es, sset, tset) =  min_cut ag d (Integer.of_int u) in *)
         (*      if (EdgeSet.cardinal es > (k+1)) then *)
         (*        Printf.printf "not optimal\n" *)
         (* done; *)
         f
      | _, _ ->
         failwith "found no refinement"
        
  end

  
  
