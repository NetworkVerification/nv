open Syntax
open Unsigned
open BatSet

module Prefix =
  struct
    type t = Integer.t * Integer.t
    let compare (x1,x2) (y1,y2) =
      let xcmp = Integer.compare x1 y1 in
      if xcmp = -1 then -1
      else if xcmp=1 then 1
      else Integer.compare x2 y2
  end

module PrefixSet = BatSet.Make(Prefix)
module PrefixSetSet = BatSet.Make(PrefixSet)
module PrefixMap = BatMap.Make(Prefix)
                              
type network_slice =
  { net          : network;
    prefixes     : PrefixSet.t;
    destinations : AdjGraph.VertexSet.t
  }
  
let printPrefix ((ip, pre) : Prefix.t) =
  Printf.sprintf "(%d, %d)" (Integer.to_int ip) (Integer.to_int pre)

let printPrefixes (prefixes : PrefixSet.t) =
  "{" ^ PrefixSet.fold (fun pre acc -> (printPrefix pre) ^ "," ^ acc) prefixes "}"
            
let partialEvalOverNodes (n : Integer.t) (e: Syntax.exp) =
  let tbl = Hashtbl.create (Integer.to_int n) in
  AdjGraph.fold_vertices
    (fun u _ ->
      let initu = Interp.interp_partial (Syntax.apps e [e_val (vint u)]) in
      Hashtbl.add tbl u initu) n ();
  tbl

let partialEvalOverEdges (edges : AdjGraph.Edge.t list) (e: Syntax.exp) = 
  let edge_to_val edge = vtuple [vint (fst edge); vint (snd edge)] in
  let tbl = Hashtbl.create (BatList.length edges) in
  BatList.iter (fun edge ->
      let ptrans = Interp.interp_partial_fun e [edge_to_val edge] in
      Hashtbl.add tbl edge ptrans) edges;
  tbl

let build_prefix_map (u : Integer.t)
                     (prefixes: PrefixSet.t)
                     (acc : AdjGraph.VertexSet.t PrefixMap.t):
      AdjGraph.VertexSet.t PrefixMap.t =
  PrefixSet.fold (fun pre acc ->
      PrefixMap.modify_def AdjGraph.VertexSet.empty pre
                           (fun us -> AdjGraph.VertexSet.add u us) acc)
                 prefixes acc

(* Finds the prefixes used by an expression *)
let get_prefixes_from_expr (expr: Syntax.exp) : PrefixSet.t =
  let prefixes = ref PrefixSet.empty in
  Visitors.iter_exp (fun e ->
      match e.e with
      | EOp (UEq, [var; pre]) when is_value pre ->
         (match var.e with
          | EVar x ->
             if (Var.name x) = "d" then
               begin
                 match (Syntax.to_value pre).v with
                 | VTuple [v1;v2] ->
                    (match v1.v, v2.v with
                     | VInt ip, VInt p ->
                        prefixes := PrefixSet.add (ip, p) !prefixes
                     | _ -> ())
                 | _ -> ()
               end
             else ()
          | _ -> ())
      | _ -> ()) expr;
  !prefixes
  
let relevantPrefixes (assertionTable : (Integer.t, Syntax.exp) Hashtbl.t) =
  Hashtbl.fold (fun _ eu acc ->
      let prefixes = get_prefixes_from_expr eu in
      PrefixSet.union prefixes acc) assertionTable PrefixSet.empty
  
(* Inspects the assertion function to find which nodes are of interest
   in the given query. Over-approximates, this should also be per prefix as well.*)
let findRelevantNodes (assertionTable : (Integer.t, Syntax.exp) Hashtbl.t) =
  Hashtbl.fold (fun u eu acc ->
      match eu.e with
      | EFun f ->
         (match f.body.e with
          | EVal v ->
             (match v.v with
              | VBool true -> acc
              | _ -> AdjGraph.VertexSet.add u acc)
          | _ -> AdjGraph.VertexSet.add u acc)
      | _ -> AdjGraph.VertexSet.add u acc) assertionTable AdjGraph.VertexSet.empty
  
  
(* Currently this will only work with networks generated by batfish. *)
let findInitialSlices initTbl =
  Hashtbl.fold
    (fun u initu acc ->
      let prefixes = get_prefixes_from_expr initu in
      build_prefix_map u prefixes acc) initTbl PrefixMap.empty

let groupPrefixesByVertices (umap: AdjGraph.VertexSet.t PrefixMap.t) : PrefixSetSet.t =
  let reverseMap : PrefixSet.t AdjGraph.VertexSetMap.t =
    PrefixMap.fold (fun u vhat acc ->
        AdjGraph.VertexSetMap.modify_opt vhat (fun us -> match us with
                                          | None -> Some (PrefixSet.singleton u)
                                          | Some us -> Some (PrefixSet.add u us)) acc)
                 umap AdjGraph.VertexSetMap.empty in
  AdjGraph.VertexSetMap.fold (fun _ v acc -> PrefixSetSet.add v acc)
                       reverseMap PrefixSetSet.empty
  
let sliceDestination symb (pre: Prefix.t) =
  let ls1, ls2 = BatList.partition (fun (x, tye) ->
                     if Var.name x = "d" then
                       true
                     else
                       false) symb
  in
  (DLet ((fst (List.hd ls1),Some (TTuple [TInt 32; TInt 32]),
             e_val (vtuple [vint (fst pre); vint (snd pre)]))),
   BatList.map (fun (s,v) -> DSymbolic (s,v)) ls2)

let createNetwork decls =
  match
    ( get_merge decls
    , get_trans decls
    , get_init decls
    , get_nodes decls
    , get_edges decls
    , get_attr_type decls
    , get_symbolics decls
    , get_lets decls
    , get_requires decls)
  with
  | Some emerge, Some etrans, Some einit, Some n, Some es,
    Some aty, symb, defs, erequires ->
     { attr_type = aty;
       init = einit;
       trans = etrans;
       merge = emerge;
       assertion = get_assert decls;
       symbolics = symb;
       defs = defs;
       requires = erequires;
       graph = AdjGraph.add_edges (AdjGraph.create n) es
     }
  | _ ->
     Console.error
       "missing definition of nodes, edges, merge, trans, or init"


(* Need to have inlined definitions before calling this *)
let createSlices info net =
  let n = AdjGraph.num_vertices net.graph in
  let initMap = partialEvalOverNodes n net.init in
  (* Printf.printf "init: %s\n" (Printing.exp_to_string net.init); *)
  Hashtbl.iter (fun _ e -> Printf.printf "init: %s\n" (Printing.exp_to_string e)) initMap;
  let assertMap = partialEvalOverNodes n (oget net.assertion) in
  (* find the prefixes that are relevant to the assertions *)
  let assertionPrefixes = relevantPrefixes assertMap in
  (* find where each prefix is announced from *)
  let slices = findInitialSlices initMap in
  (* keep only the relevant slices, i.e. prefixes that are used by the assertion *)
  let relevantSlices =
    PrefixMap.filter (fun pre _ -> PrefixSet.mem pre assertionPrefixes) slices in
  (* each set of prefixes represents an SRP *)
  let relevantSliceGroups = groupPrefixesByVertices relevantSlices in
  PrefixSetSet.fold (fun prefixes acc ->
      (* get a prefix from this class of prefixes *)
      let pre = PrefixSet.min_elt prefixes in
      (* find the nodes this class is announced from *)
      let ds = PrefixMap.find pre relevantSlices in
      let dstPre, symb = sliceDestination net.symbolics pre in
      let decls =
        Inline.inline_declarations ((DATy net.attr_type) :: dstPre :: (DNodes n)
                                    :: (DEdges (AdjGraph.edges (net.graph))) :: symb @
                                      [(DInit net.init);
                                       (DMerge net.merge); (DTrans net.trans);
                                       (DAssert (oget net.assertion))]) |>
          Typing.infer_declarations info in
      { net =
          { attr_type = net.attr_type;
            init = oget (get_init decls);
            trans = oget (get_trans decls);
            merge = oget (get_merge decls);
            assertion = (get_assert decls);
            symbolics = get_symbolics decls;
            defs = get_lets decls;
            requires = get_requires decls;
            graph = net.graph;
          };
        prefixes = prefixes;
        destinations = ds
      } :: acc) relevantSliceGroups []
  
