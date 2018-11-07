open Graph
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
let refineTopological (f: abstractionMap) (g: Graph.t)
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
  (* Graph.VertexSetSet.iter (fun us -> Printf.printf "{"; *)
  (*                        VertexSet.iter (fun u -> Printf.printf "%d," (Integer.to_int u)) us; *)
  (*                        Printf.printf "}\n") groups; *)
  (* Printf.printf "cardinal: %d\n" (VertexSetSet.cardinal groups); *)
  (* Printf.printf "end of iter\n%!"; *)
  VertexSetSet.fold (fun us f' -> AbstractionMap.split f' (AbstractNode.fromSet us))
                    (groupVerticesByAbsId vmap) f

let rec abstractionTopological (f: abstractionMap) (g: Graph.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun us facc ->
               (* Printf.printf "refining %s\n" (AbstractNode.printAbstractNode us); *)
               if (AbstractNode.cardinal us > 1) then
                 refineTopological facc g us 
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstractionTopological f' g

(** * Proper policy+topology abstraction *)  

let groupVerticesByPolicyAbsId (umap: (PolicyAbsId.t) VertexMap.t) : VertexSetSet.t =
  let reverseMap : VertexSet.t PolicyAbsIdMap.t =
    VertexMap.fold (fun u vhat acc ->
        PolicyAbsIdMap.modify_def (VertexSet.singleton u)
                                    vhat (fun us -> VertexSet.add u us) acc)
                   umap PolicyAbsIdMap.empty in
  PolicyAbsIdMap.fold (fun _ v acc -> VertexSetSet.add v acc)
              reverseMap VertexSetSet.empty
  
let refineAbstraction (f: abstractionMap) (g: Graph.t)
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

let rec abstraction (f: abstractionMap) (g: Graph.t)
                    (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                    (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun us facc ->
               if (AbstractNode.cardinal us > 1) then
                 refineAbstraction facc g transMap mergeMap us
               else
                 facc) f f in
  if (size f = size f') then normalize f'
  else abstraction f' g transMap mergeMap


let partialEvalTrans (graph : Graph.t)
                     (trans : Syntax.exp) : (Edge.t, int * Syntax.exp) Hashtbl.t  =
  let edge_to_val e = vtuple [vint (fst e); vint (snd e)] in
  let es = Graph.edges graph in
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

let partialEvalMerge (graph : Graph.t)
                     (merge : Syntax.exp) : (Vertex.t, int * Syntax.exp) Hashtbl.t =
  let node_to_val n = vint n in
  let ns = Graph.get_vertices graph in
  let tbl = Hashtbl.create (VertexSet.cardinal ns) in
  VertexSet.iter (fun v ->
      let pmerge = Interp.interp_partial_fun merge [node_to_val v] in
      Hashtbl.add tbl v (Syntax.hash_exp ~hash_meta:false pmerge, pmerge)) ns;
  tbl

(* Given a concrete graph g, an abstraction function f and an abstract
   node id returns its abstract edges *)
let findAbstractEdges (g: Graph.t) (f: abstractionMap) (uhat: abstrId) : EdgeSet.t =
  let repru = getGroupRepresentativeId f uhat in
  let ns = neighbors g repru in
  List.fold_left (fun acc v -> EdgeSet.add (uhat, getId f v) acc) EdgeSet.empty ns

(* Given a concrete graph, transfer, merge functions a destinations
   computes an abstract network *)
let findAbstraction (graph: Graph.t)
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
    let buildAbstractGraphDecls (g: Graph.t) (f: abstractionMap) : Integer.t * (Edge.t list) =
      let n = Integer.create ~value:(size f) ~size:32 in
      let rec edges uhat =
        if uhat = n then EdgeSet.empty
        else
          EdgeSet.union (findAbstractEdges g f uhat) (edges (Integer.succ uhat))        
      in
      (n, EdgeSet.to_list (edges zero))

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
          (g : Graph.t)
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
    let buildAbstractNetwork (f: abstractionMap) (graph: Graph.t)
                             (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                             (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                             (initMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                             (assertMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                             (dst : VertexSet.t)
                             (attrTy: Syntax.ty)
                             (symb: (Syntax.var * Syntax.ty_or_exp) list)
                             (k: int) =
      (* build the abstract graph based on the abstraction function *)
      let (n, edgeshat) = buildAbstractGraphDecls graph f in
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
          let agraph = Graph.add_edges (Graph.create n) edgeshat in
          Graph.print agraph
        end;
      (failuresMap, (DATy attrTy) :: (DNodes n) :: (DEdges edgeshat) :: symbolics @ symbD
                    @ ((DMerge mergehat) :: (DTrans transhat) :: (DInit inithat)
                       :: [DAssert asserthat]))

    let abstractToConcreteEdge (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : EdgeSet.t =
      let (uhat, vhat) = ehat in
      let us = getGroupById f uhat in (* get nodes represented by uhat *)
      AbstractNode.fold
        (fun u acc ->
          EdgeSet.union (EdgeSet.of_list (getNeighborsInVhat f g u vhat)) acc) us EdgeSet.empty
      
    let getEdgeMultiplicity (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : int =
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
                         (g: Graph.t) : splittings = 
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
      let us = groupAbsNodesByVertexSet connectivityMap in
      if ((AbstractNodeSet.cardinal us) = 1) then
        Mesh
      else
        Groups us

    (* using the abstract group id on path for efficiency reasons *)
    (* - assumes uid can be split
       - returns a random split with maximum ratio if the path was empty
       - returns a random split with ratio 1.0 if you immediately get to a full mesh.
       TODO: no need to return a ratio of 1.0, do max_int. Also avoid enforcing invariants
       with the ratio *)
    let bestSplitForFailures (g : Graph.t) (f: abstractionMap)
                             (uid: abstrId) (path: abstrId list) =
      let rec loop path current best =
        match path with
        | [] -> best
        | vid :: path ->
           let curGroup = getGroupById f current in
           match findSplittingByConnectivity curGroup (getGroupById f vid) g with
           | Groups us when AbstractNodeSet.cardinal us = 2 ->
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
                let u1, u2 = AbstractNode.randomSplit curGroup in
                (AbstractNodeSet.of_list [u1;u2], 1.0)
              else
                best
      in
      let u1, u2 = AbstractNode.randomSplit (getGroupById f uid) in
      loop path uid (AbstractNodeSet.of_list [u1;u2], float_of_int max_int)

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
    let findRandomPath (ag: Graph.t) (sol: Solution.t)
          (uid: abstrId) (ds: Graph.VertexSet.t) (attrTy: Syntax.ty) =
      (* finding incoming messages the hard way for now. Why are edges
         not treated the other way around? *)
      let rec loop uid acc =
        (* Find neighbors of uid that have a valid attribute *)
        let neighborsu =
          BatList.filter_map
            (fun (i,j) -> if uid = j then Some i else None) (Graph.edges ag)
        in
        let sol = sol.Solution.labels in 
        let valid_neighbors =
          List.filter (fun vhat -> validAttribute attrTy
                                     (Graph.VertexMap.find vhat sol)) neighborsu
        in
        (* If there are none with a valid attribute, look into the other ones *)
        let neighborsu =
          if BatList.is_empty valid_neighbors then
            neighborsu else valid_neighbors
        in
        (* Pick one randomly *)
        let vhat = BatList.hd neighborsu in
        (* Stop if at destination *)
        if VertexSet.mem vhat ds then
          BatList.rev (vhat :: acc)
        else if BatList.mem vhat acc then
          (* Or if we've visited this vertex before *)
          BatList.rev acc
        else
          loop vhat (vhat :: acc)
      in
      loop uid []

    (* Try to find a failure for which splitting would make the most
       sense. This is based on heuristics, currently: 
       * 1. Choose a u,v with |u| > 1 or |v| > 1, so we can split it.  
       * 2. Choose failure (u,v) such that u can reach the destination and v 
            cannot.  
       * 3. Choose u with the biggest cost (thus "distance" from the
            destination). This is good for our splitting based on the
            path. *)
    let findVertexToRefine f (failed: EdgeSet.t) sol attrTy =
      let lbl = sol.Solution.labels in
      let candidate1 =
        EdgeSet.filter (fun (u,v) -> ((AbstractNode.cardinal (getGroupById f u)) > 1))
                      failed in
      let isEmpty1 = EdgeSet.is_empty candidate1 in
      (* if there is no failed edge <u,v> with |u| > 1 *)
      let candidate1 = if isEmpty1 then
                         EdgeSet.filter (fun (u,v) ->
                             ((AbstractNode.cardinal (getGroupById f v)) > 1))
                                       failed
                       else
                         candidate1
      in
      (* This is kind of fragile, it matches on the expected value of
         the label of a vertex that has a path vs one that doesn't. If
         the value changes this won't work. *)
      let candidate2 =
        EdgeSet.filter (fun (u,v) ->
            match validAttribute attrTy (VertexMap.find u lbl),
                  validAttribute attrTy(VertexMap.find v lbl) with
            | true, false -> true
            | _, _ -> false) candidate1 in
      let selector = if isEmpty1 then snd else fst in
      let candidate3 =
        match EdgeSet.is_empty candidate2 with
        | false ->
           (* not sure how to implement this right now *)
           EdgeSet.choose candidate2
        | true ->
           EdgeSet.choose candidate1
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
      
    let refineForFailures (g: Graph.t) (f: abstractionMap)
          (failVars: Var.t EdgeMap.t) (sol: Solution.t) (k: int)
          (dst: VertexSet.t) (attrTy : Syntax.ty) : abstractionMap option =
      (* Collections.StringMap.iter (fun k _ -> Printf.printf "symb: %s\n" k) sol.symbolics; *)
      (* EdgeMap.iter (fun e k -> Printf.printf "edge %d,%d %s\n" (UInt32.to_int (fst e)) *)
      (*                                        (UInt32.to_int (snd e)) (Var.to_string k)) failVars; *)

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
                   Printf.printf "failed: %s\n" (Graph.printEdge edge); 
                   (EdgeSet.add edge acc, Graph.add_edge ag edge)
                 end
               else (acc, Graph.add_edge ag edge)
            | _ -> failwith "This should be a boolean variable") failVars
          (EdgeSet.empty, Graph.create (AbstractionMap.size f |> Integer.of_int))
      in
      
      let total_failures =
        EdgeSet.fold (fun ehat acc ->
            (BuildAbstractNetwork.getEdgeMultiplicity g f ehat) + acc)
          failures 0
      in
      if (total_failures <= k) then
        None
      else
        begin
          let uhat = findVertexToRefine f failures sol attrTy in
          (* what path to use for refining, by default will look for a
             (somewhat) random path. random indicates a random split
             of the node selected for refinement. That's probably the
             worst possible option. *)
          let path_heuristic = "somePath" in (* make it an option at some point? *)
          let path =
            if path_heuristic = "random" then []
            else
              findRandomPath agraph sol uhat dst attrTy
          in  
          let (uss, _) = bestSplitForFailures g f uhat path in
          let f' = splitSet f uss in
          let f'' =  abstractionTopological f' g in
          (* refineForFailures_debug f''; *)
          Some f''
        end
  end

  
  
