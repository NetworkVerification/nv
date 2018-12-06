open AdjGraph
open AbstractionMap
open Unsigned
open Console
open Srp
open Hashtbl
open Syntax
open BatSet

let debugAbstraction = ref true

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

    let compare = Pervasives.compare
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
        (* Printf.printf "For node %d: {" (Unsigned.Integer.to_int u); *)
        (* BatSet.iter (fun v -> Printf.printf "%d," (Unsigned.Integer.to_int v)) vhat; *)
        (* Printf.printf "}\n"; *)
        AbsIdSetMap.modify_def (VertexSet.singleton u) vhat (fun us -> VertexSet.add u us) acc)
                 umap AbsIdSetMap.empty in
  AbsIdSetMap.fold (fun _ v acc -> VertexSetSet.add v acc)
              reverseMap VertexSetSet.empty
                 
(** ** Topological only abstraction *)
(* This does not handle a forall-forall abstraction. *)  
let refineTopological (f: abstractionMap) (g: AdjGraph.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : AbsIdSet.t VertexMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getId f v in
        VertexMap.modify_opt u (fun omapu ->
                            match omapu with
                            | None -> Some (AbsIdSet.singleton vhat)
                            | Some vs -> Some (AbsIdSet.add vhat vs)) acc) umap
                   (neighbors g u)
  in
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  (* Printf.printf "The map:\n"; *)
  (* VertexMap.iter (fun u vs -> Printf.printf "%d: {" (Integer.to_int u); *)
  (*                          (AbsIdSet.iter (fun v -> Printf.printf "%d," (Integer.to_int v)) *)
  (*                                       vs); *)
  (*                          Printf.printf "}\n" *)
  (*             ) vmap; *)
  (* Printf.printf "The groups: \n"; *)
  (* let groups = (groupVerticesByAbsId vmap) in *)
  (* AdjGraph.VertexSetSet.iter (fun us -> Printf.printf "{"; *)
  (*                        VertexSet.iter (fun u -> Printf.printf "%d," (Integer.to_int u)) us; *)
  (*                        Printf.printf "}\n") groups; *)
  (* Printf.printf "cardinal: %d\n" (VertexSetSet.cardinal groups); *)
  (* Printf.printf "end of iter\n%!"; *)
  VertexSetSet.fold (fun us f' -> AbstractionMap.split f' (AbstractNode.fromSet us))
                    (groupVerticesByAbsId vmap) f

let abstractionTopological (f: abstractionMap) (g: AdjGraph.t) : abstractionMap =
  let rec loop fi =
    let f' = AbstractionMap.fold (fun us facc ->
                 (* Printf.printf "refining %s\n" (AbstractNode.printAbstractNode us); *)
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
    List.fold_left (fun acc v ->
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
  let tbl = Hashtbl.create (List.length es) in
  List.iter (fun e ->
      (* Printf.printf "%s\n" *)
      (*               (Syntax.show_exp ~show_meta:false *)
      (*                                   (exp_of_value (vclosure (network.trans)))); *)
      let ptrans = Interp.interp_partial_fun trans [edge_to_val e] in
      (* Printf.printf "edge (%d,%d): %s\n" (Integer.to_int (fst e)) (Integer.to_int (snd e)) *)
      (*               (Syntax.show_exp ~show_meta:false ptrans); *)
      (* Printf.printf "edge (%d,%d): %d\n" (Integer.to_int (fst e)) (Integer.to_int (snd e)) *)
      (*               (Syntax.hash_exp ~hash_meta:false ptrans); *)
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
  List.fold_left (fun acc v -> EdgeSet.add (uhat, getId f v) acc) EdgeSet.empty ns

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
      (* show_message (printAbstractGroups f "\n") T.Blue *)
      (*              "Abstract groups before crash "; *)
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
      
    let buildSymbolicFailures (aedges : Edge.t list) (k : int) =
      (* symbolic variables of failures, one for each abstract edge *)
      let failuresMap =
        List.fold_left (fun acc (u,v) ->
            let e = Vertex.printVertex u ^ Vertex.printVertex v in
            let failVar = Var.fresh ("failed-" ^ e) in
            EdgeMap.add (u,v) failVar acc) EdgeMap.empty aedges in

      (*building the requires clause that requires
        fail1 + fail2 + .. <= k *)
      let bool2int_exp arg =
        aexp (eif arg (e_val (vint one)) (e_val (vint zero)),
              Some Typing.node_ty, Span.default)
      in
      let failuresSum =
        List.fold_left (fun acc (uhat, vhat) ->
            aexp (eop (UAdd 32)
                      [(bool2int_exp (evar (EdgeMap.find (uhat, vhat) failuresMap))); acc],
                  Some Typing.node_ty, Span.default))
                       (e_val (vint zero)) aedges in
      let failures_leq_k = aexp(eop (ULeq 32)
                                    [failuresSum;
                                     e_val (vint (Integer.create ~value:k ~size:32))],
                                Some TBool, Span.default) in
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
      let failCheck fvar body = eif (evar fvar)
                                   (exp_of_value (Syntax.default_value attrTy))
                                   body in
      
      (* inserting that code in the body of the transfer function *)
      let addFailureCheck fvar exp = (deconstructFun exp).body |> (failCheck fvar) in
      
      (* for each abstract edge, find it's corresponding concrete
         transfer function and augment it with a check for whether it's
         failed *)
      let branches =
        List.fold_left (fun acc (uhat, vhat) ->
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
      let messageArg =
        match aedges with
        | [] -> failwith "No edges found"
        | (uhat, vhat) :: _ ->
           let u = getGroupRepresentativeId f uhat in
           match getNeighborsInVhat f g u vhat with
           | [] -> failwith "There must be a concrete edge
                             corresponding to the abstract edge"
           | uv :: _ -> 
              let (_, transuv) = Hashtbl.find trans uv in
              let transf = deconstructFun transuv in
              transf.arg
      in
      let match_exp = ematch (evar aedge_var) branches in
      (* create fun m -> trans_hat_body *)
      let trans_hat_msg = Syntax.lam messageArg match_exp in
      (*return fun e_hat m -> trans_hat_body *)  
      Syntax.lam aedge_var trans_hat_msg

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
          (p, mergeu1.body) :: (branches (Integer.succ uhat))
      in
      (* create a match on the node expression *)
      let match_exp = ematch (evar avertex_var) (branches zero) in
      (* create a function from attributes *)
      Syntax.lam avertex_var (Syntax.lam xvar (Syntax.lam yvar match_exp))

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
      let default_attr = e_val (default_value attrTy) in
      let default_branch = (PWild, default_attr) in
      (* compute the branches of the initial expression *)
      let branches = VertexSet.fold (fun u acc ->
                         let uhat = getId f u in
                         let p = PInt uhat in
                         (p, vinit) :: acc) dst' ([b; default_branch]) in
      (*build the match expression *)
      let match_exp = ematch (evar avertex_var) branches in
      (*return the function "init node = ..." *)
      Syntax.lam avertex_var match_exp

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
      let messageArg = (deconstructFun mineu).arg in
      
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
      let match_exp = ematch (evar avertex_var) (branches zero) in
      let assert_msg = Syntax.lam messageArg match_exp in
      
      (*return fun uhat m -> assert_hat_body *)  
      Syntax.lam avertex_var assert_msg
      
    (* Given an abstraction function, a concrete graph, transfer and merge
   function, and the number of maximum link failures builds an
   abstract network *)
    let buildAbstractNetwork (f: abstractionMap) (graph: AdjGraph.t)
                             (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                             (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                             (initMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                             (assertMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                             (dst : VertexSet.t)
                             (attrTy: Syntax.ty)
                             (symb: (Syntax.var * Syntax.ty_or_exp) list)
                             (k: int) =
      (* build the abstract graph based on the abstraction function *)
      let (n, edgeshat) = buildAbstractAdjGraphDecls graph f in
      (* build the symbolic representation of failures *) 
      let (failuresMap, symbolics) = buildSymbolicFailures edgeshat k in
      (* build the abstract merge function *)
      let mergehat = buildAbstractMerge n mergeMap f in
      (* build the abstract transfer function *)
      let transhat = buildAbstractTrans graph edgeshat transMap attrTy failuresMap f in
      (* build the abstract init function *)
      let inithat = buildAbstractInit dst initMap attrTy f in
      (* build the abstract assert function *)
      let asserthat = buildAbstractAssert assertMap f in
      let symbD = List.map (fun (d, tye) -> DSymbolic (d,tye)) symb in
      if !debugAbstraction then
        begin
          let agraph = AdjGraph.add_edges (AdjGraph.create n) edgeshat in
          AdjGraph.print agraph
        end;
      (failuresMap, (DATy attrTy) :: (DNodes n) :: (DEdges edgeshat) :: symbolics @ symbD
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
          List.filter (fun v -> AbstractNode.mem v vhat) neighborsOfu
        in
        VertexSet.of_list neighborsOfUinV
      in
      let connectivityMap = AbstractNode.fold (fun u acc ->
                                VertexMap.add u (addNeighbor u) acc)
                              uhat VertexMap.empty in
      (* VertexMap.iter (fun k v -> Printf.printf "%d -> %s\n" (Integer.to_int k) (AbstractNode.printAbstractNode (AbstractNode.fromSet v))) connectivityMap; *)
      let us = groupAbsNodesByVertexSet connectivityMap in
      (* AbstractNodeSet.iter (fun u -> Printf.printf "%s\n" (AbstractNode.printAbstractNode u)) us; *)
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
          (* old code that did not try to avoid splitting neighbors *)
        (*   let b = ref false in *)
        (*   let uss1, uss2 = AbstractNodeSet.partition (fun _ -> b := not !b; !b) uss in *)
        (*   let us1 = AbstractNodeSet.fold (fun us acc -> AbstractNode.union us acc) *)
        (*                                   uss1 AbstractNode.empty *)
        (*   in *)
        (*   let us2 = AbstractNodeSet.fold (fun us acc -> AbstractNode.union us acc) *)
        (*                                   uss2 AbstractNode.empty *)
        (*   in *)
          (*   AbstractNodeSet.add us2 (AbstractNodeSet.singleton us1) *)
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

    (* using the abstract group id on path for efficiency reasons *)
    (* - assumes uid can be split
       - returns a random split with maximum ratio if the path was empty
       - returns a random split with ratio 1.0 if you immediately get to a full mesh.
       TODO: no need to return a ratio of 1.0, do max_int. Also avoid enforcing invariants
       with the ratio *)
    let bestSplitForFailures (g : AdjGraph.t) (f: abstractionMap)
                             (uid: abstrId) (path: abstrId list) =
      let rec loop path current best =
        match path with
        | [] -> best
        | vid :: path ->
           let curGroup = getGroupById f current in
           (* Printf.printf "vid:%d\n" (Integer.to_int vid); *)
           (* I think the arguments curGroup and getGroupById.. should
              be the other way around *)
           match findSplittingByConnectivity curGroup (getGroupById f vid) g with
           | Groups us when AbstractNodeSet.cardinal us = 2 ->
              (* Printf.printf "best-split was vertex: %d\n" (Integer.to_int current); *) 
              (us, 0.0)
           | Groups us ->
              let szNew = AbstractNodeSet.cardinal us in
              let szCur = AbstractNode.cardinal curGroup in
              let ratio = (float_of_int szNew) /. (float_of_int szCur) in
              (* heuristic *)
              if (ratio < snd best) then
                loop path vid (us, ratio)
              else
                loop path vid best
           | Mesh ->
              (* do a randomSplit if necessary, but maybe there are better options*)
              if (snd best) > 1.0 then
                begin
                  (* Printf.printf "best-split was random\n"; *)
                  let u1, u2 = AbstractNode.randomSplit curGroup in
                  (AbstractNodeSet.of_list [u1;u2], 1.0)
                end
              else
                best
      in
      let u1, u2 = AbstractNode.randomSplit (getGroupById f uid) in
      let (uss, _) =
        loop path uid (AbstractNodeSet.of_list [u1;u2], float_of_int max_int)
      in
      AbstractNodeSet.iter (fun us -> Printf.printf "%s," (AbstractNode.printAbstractNode us))
                           uss;
      (* If the group is larger than 2 try to make it more abstract by
         creating groups of two *)
      createFreshAbstractNodes uss
            
    (** Returns true if the given value is not the default for the
       given attribute type. A non-default value indicates that this
       message has a path to the destination *)
    let validAttribute (attrTy: Syntax.ty) (m : Syntax.value) : bool =
      not (default_value attrTy = m)
      (* match m with
       * | VTuple [_;_;_;_; bestu], VTuple [_;_;_;_; bestv] ->
       *    (match bestu.v, bestv.v with
       *     | VOption (Some _), VOption None ->
       *        true
       *     | _, _ -> false)
       * | _ -> false) *)

    (** Finds a path in the graph starting from abstract vertex
       uid. Will stop once it reaches the destination or a cycle. It
       tries to find a good path by first looking at neighbors who
       have a solution *)
    let findRandomPath (ag: AdjGraph.t) (sol: Solution.t)
          (uid: abstrId) (ds: AdjGraph.VertexSet.t) (attrTy: Syntax.ty) =
      (* finding incoming messages the hard way for now. Why are edges
         not treated the other way around? *)
      let rec loop uid acc =
        (* Find neighbors of uid that have a valid attribute *)
        let sol = sol.Solution.labels in
        let neighborsu =
          BatList.filter_map
            (fun (i,j) ->
              if uid = j then
                Some (i, validAttribute attrTy (AdjGraph.VertexMap.find i sol))
              else None) (AdjGraph.edges ag)
        in
        (* If there are none with a valid attribute, look into the other ones *)
        let neighborsu = List.sort (fun (u, bu) (v, bv) ->
                             - (Pervasives.compare bu bv)) neighborsu
        in
        let rec pickRandom neighborsu =
          match neighborsu with
          | [] ->
             (* if there are none left, then we've visited all of the neighbors *)
             BatList.rev acc
          | (vhat, _) :: neighborsu ->
              (* Stop if at destination *)
             if VertexSet.mem vhat ds then
               if (List.tl acc = []) then
                 pickRandom neighborsu
               else
                 BatList.rev (vhat :: acc)
             else if BatList.mem vhat acc then
               (* If we've visited this vertex before try another one *)
               pickRandom neighborsu
             else
               (* otherwise add it to the path *)
               loop vhat (vhat :: acc)
        in
        pickRandom neighborsu
      in
      (* add uid to avoid revisiting it when searching for path but
         throw it away in the end, as the code that does the
         refinement assumes the vertex refined is not in the path used for refinement *)
      List.tl (loop uid [uid])

    (** ** Various heuristics for splitting abstract nodes*)

    (** Returns the subset of failed edges for which the abstract node
       (fst or snd) has a cardinality larger than 1 and thus we can
       split *)
    let splittable (f: abstractionMap) proj (failed: EdgeSet.t) =
      EdgeSet.filter (fun e -> ((AbstractNode.cardinal (getGroupById f (proj e))) > 1))
                     failed

    (** Given a set of failed variables, for each (u,v) it will select
       one s.t. |neighbors(u)| <= k if it exists otherwise it will
       return a random failed edge. *)
    let chooseRandomForK (ag: AdjGraph.t) (failed: EdgeSet.t) (k: int) =
      let rec loop fs =
        if EdgeSet.is_empty fs then
          EdgeSet.choose failed
        else
          begin
            let e, fs = EdgeSet.pop_min fs in
            let u = fst e in
            if List.length (neighbors ag u) <= k then
              e
            else
              loop fs
          end
      in
      loop failed
      
    (** Try to find a failure for which splitting would make the most
       sense. This is based on heuristics, currently: 
       * 1. Choose a u,v with |u| > 1 or |v| > 1, so we can split it.  
       * 2. Choose failure (u,v) such that u can reach the destination and v 
            cannot. Not sure if that's relevant anymore.
       * 3. If we have two or more failures (u_1,v) (u_2,v) etc. then split the u_i that 
            is connected with the most abstract nodes that used to be in the same group 
            as v. That way, we may avoid splitting for them as well in a separate 
            iteration.
       * 4. When choosing between vertices u and v to split, 
            split one that has at most k neighbors if possible. 
            Chances are we were going to have to split that too. *)
    let findVertexToRefine finit f (ag: AdjGraph.t) (failed: EdgeSet.t) sol attrTy k =
      let lbl = sol.Solution.labels in
      let candidates = splittable f fst failed in
      let isEmpty1 = EdgeSet.is_empty candidates in
      (* if there is no failed edge <u,v> with |u| > 1 *)
      let candidates = if isEmpty1 then
                         splittable f snd failed
                       else
                         candidates
      in
      (* This is kind of fragile, it matches on the expected value of
         the label of a vertex that has a path vs one that doesn't. If
         the value changes this won't work. *)
      let candidate2 =
        EdgeSet.filter (fun (u,v) ->
            match validAttribute attrTy (VertexMap.find u lbl),
                  validAttribute attrTy(VertexMap.find v lbl) with
            | true, false -> true
            | _, _ -> false) candidates in
      let selector = if isEmpty1 then snd else fst in
      let candidate3 =
        match EdgeSet.is_empty candidate2 with
        |  false ->
            (* choose an edge randomly *)
            let (u, v) = chooseRandomForK ag candidate2 k in
            (* Printf.printf "chose randomly: %s\n" (printEdge (u,v)); *)
            (* keep only the failures towards v if there are many *)
            let vedges = EdgeSet.filter (fun (x,y) ->
                             Printf.printf "x,y,v:%s,%s,%s\n" (Vertex.printVertex x)
                                           (Vertex.printVertex y) (Vertex.printVertex v);
                             if y = v then
                               begin
                                 Printf.printf "true\n";
                                 true
                               end
                             else false) candidate2 in
            (* Printf.printf "did I keep at least 2? %d\n" (EdgeSet.cardinal vedges); *)
            if EdgeSet.cardinal vedges > 1 then
              begin
                (* compute the group that v originally belonged to *)
                let vrepr = AbstractionMap.getGroupRepresentativeId f v in
                let oldGroupOfV = AbstractionMap.getGroup finit vrepr in
                if AbstractNode.cardinal oldGroupOfV =
                     AbstractNode.cardinal (AbstractionMap.getGroupById f v) then
                  (* v has never been split yet *)
                  (u,v)
                else
                  begin
                    (* v was split before *)
                    let findNeighborsInOriginalV u =
                      let neigh = AdjGraph.neighbors ag u in
                      List.fold_left (fun acc what ->
                          let vrepr = AbstractionMap.getGroupRepresentativeId f what in
                          let oldW = AbstractionMap.getGroup finit vrepr in
                          if AbstractNode.equal oldW oldGroupOfV then
                            acc + 1
                          else acc) 0 neigh
                    in
                    let mostNeighbors, n = EdgeSet.fold
                                             (fun (u,v) acc ->
                                               let n = findNeighborsInOriginalV u in
                                               if n >= snd acc then
                                                 (((u,v), n) :: (fst acc), n)
                                               else
                                                 (((u,v),n) :: fst acc, snd acc))
                                             vedges ([], 0)
                    in
                    let filteredMax =
                      BatList.filter_map (fun (e,m) -> if m = n then Some e else None)
                                         mostNeighbors |> EdgeSet.of_list
                    in
                    chooseRandomForK ag filteredMax k
                  end
              end
            else
              (u,v)
        | true ->
           EdgeSet.choose candidates
      in
      let res = selector candidate3 in
      if !debugAbstraction then
        Printf.printf "Abstract Vertex to split: %s\n" (Vertex.printVertex res);
      res
        
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
      
    let refineForFailures (draw: bool) (file: string) (g: AdjGraph.t)
                          (finit: abstractionMap) (f: abstractionMap)
                          (failVars: Var.t EdgeMap.t) (sol: Solution.t) (k: int)
                          (dst: VertexSet.t) (attrTy : Syntax.ty) : abstractionMap option =
      
      (* get set of failures, and also build abstract graph useful for
         splitting, at least until we can get forwarding information
         in labels *)
      let failures, agraph =
        EdgeMap.fold (fun edge fvar (acc, ag) ->
            let bv = Collections.StringMap.find (Var.to_string fvar) sol.symbolics in
            match bv.v with
            | VBool b ->
               if b then
                 begin
                   Printf.printf "failed: %s\n" (AdjGraph.printEdge edge); 
                   (EdgeSet.add edge acc, AdjGraph.add_edge ag edge)
                 end
               else (acc, AdjGraph.add_edge ag edge)
            | _ -> failwith "This should be a boolean variable") failVars
                     (EdgeSet.empty, AdjGraph.create (AbstractionMap.size f |> Integer.of_int))
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
          let uhat = findVertexToRefine finit f agraph failures sol attrTy k in
          (* what path to use for refining, by default will look for a
             (somewhat) random path. random indicates a random split
             of the node selected for refinement. That's probably the
             worst possible option. *)
          let path_heuristic = "somePath" in (* make it an option at some point? *)
          let path =
            if path_heuristic = "random" then []
            else
              findRandomPath agraph sol uhat
                             (VertexSet.map (fun d -> getId f d) dst) attrTy
          in
          Printf.printf "splitting over path: %s"
                        (Collections.printList (Vertex.printVertex) path "" "," "\n");
          let uss = bestSplitForFailures g f uhat path in
          let f' = splitSet f uss in
          let f'' =  abstractionTopological f' g in
          (* if no progress was made, then do a random split on uhat *)
          (* the group of uhat in abstraction f *)
          let group_uhat_f = AbstractionMap.getGroupById f uhat in
          (* the group of uhat in f'' *)
          let group_uhat_f'' =
            AbstractionMap.getGroup f''
              (AbstractionMap.getGroupRepresentativeId f uhat)
          in
          if (AbstractNode.equal group_uhat_f group_uhat_f'') then
            begin
              let uhat1, uhat2 = AbstractNode.randomSplit group_uhat_f in
              let f = splitSet f'' (AbstractNodeSet.of_list [uhat1; uhat2]) in
              let f = abstractionTopological f g in
              Some f
            end
          else
            (* refineForFailures_debug f''; *)
            Some f''
        end

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
       2. the reachables nodes that have cardinality > 1
       3. the unreachable nodes that have cardinality < 1 *)
    let reachable_by_freq f (cuts: EdgeSet.t list)
        : ((Vertex.t * int) list) * (Vertex.t list) * (Vertex.t list) =
      let accfreq, accReachAbs, accUnreachAbs =
        List.fold_left (fun acc cutset ->
            EdgeSet.fold (fun (u,v) (accfreq, accReachAbs, accUnreachAbs) ->
                (updateList u (fun freq -> match freq with
                                           | None -> 1
                                           | Some f -> f+1) accfreq,
                 (if (AbstractNode.cardinal (getGroupById f u)) > 1 then
                    u :: accReachAbs
                  else accReachAbs),
                 (if (AbstractNode.cardinal (getGroupById f v)) > 1 then
                    v :: accUnreachAbs
                  else accUnreachAbs))) cutset acc ) ([], [], []) cuts
      in
      let accfreq = List.sort (fun (_,f) (_,f') -> Pervasives.compare f f') accfreq in 
      (accfreq, accReachAbs, accUnreachAbs)
          
      
    (* computes a refinement of f, s.t. all sources (currently sources
       are not defined, all nodes are considered sources) have at
       least k+1 disjoint paths to the destination *)
      (*TODO: do the actua refinement and put this in a loop,
              until the set of cuts is empty*)
    let refineK (g: AdjGraph.t) (forig: abstractionMap) (ds: VertexSet.t) (k: int) =
      let ag = BuildAbstractNetwork.buildAbstractAdjGraph g forig in
      let d = getId forig (VertexSet.choose ds) in (*assume only one destination for now *)
      let cuts = fold_vertices (fun u acc ->
                     if u <> d then
                       let (es, _, _) =  min_cut ag d u in
                       if EdgeSet.cardinal es > k then
                         acc
                       else
                         es :: acc
                     else
                       acc) (num_vertices ag) []
      in
      (* sort (reachable) vertices by frequency of appereance in cut-sets. *)
      let cut_freq = reachable_by_freq cuts in
      let most_freq =
        try
          Some (BatList.find (fun (u,_) -> AbstractNode.cardinal u > 1) cut_freq)
        with Not_found -> None
      in
      match most_freq with
      | None ->
         EdgeSet.fold (fu
      List
      match cut_freq with
      | [] -> failwith "cannot be empty"
      | (u,f) :: freq ->
         if (AbstractNode.cardinal u) > 1 then
           u
      
      List.iter (fun es -> EdgeSet.iter (fun e -> Printf.printf "%s" (printEdge e)) es) cuts;
      f
                 
      
  end

  
  
