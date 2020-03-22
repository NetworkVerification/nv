(* Printing utilities for abstract syntax *)
open Batteries
open Nv_lang
open Nv_lang.Syntax
open Nv_lang.Collections
open Cudd
open Nv_datastructures
open Nv_utils.PrimitiveCollections
open Nv_utils.RecordUtils
open Nv_utils
open Nv_solution
open Jupyter

(* set to true if you want to print universal quanifiers explicitly *)
let quantifiers = true

let max_prec = 10

let glob = ref false

let tableStyle = "border: 1px solid black; border-collapse: collapse;"
let thStyle = "text-align: center; border: 1px solid black; border-collapse: collapse;"
let tdStyle = "text-align: center; border: 1px solid black; border-collapse: collapse;"
let trStyle = "text-align: center; border: 1px solid black; border-collapse: collapse;"

let mkTable ?(style=tableStyle) s = Printf.sprintf "<table style=\"%s\">%s</table>" style s

let mkTh ?(style=thStyle) s = Printf.sprintf "<th style=\"%s\">%s</th>" style s

let mkTd ?(style=tdStyle) s = Printf.sprintf "<td style=\"%s\">%s</td>" style s

let mkTr ?(style=trStyle) s = Printf.sprintf "<tr style=\"%s\">%s</tr>" style s

(* missing type information so this is not usable*)
(*let rec containsMapTy ty =
  match ty with
  | TInt _ | TBool | TUnit | TNode | TEdge | QVar _ -> false
  | TVar {contents = Link t} -> containsMap t
  | TVar _ -> false
  | TMap (_, TBool) -> false
  | TMap (_, ty) -> true
  | TArrow (ty1, ty2) -> (containsMap ty1) || (containsMap ty2)
  | TOption ty1 -> containsMap ty1
  | TTuple ts ->
    List.exists containsMap ts
  | TRecord map ->
    StringMap.exists (fun _ ty -> containsMap ty) map*)

let rec containsMap v =
  match v.v with
    | VUnit | VBool _ | VInt _ | VNode _ | VEdge _ -> false
    | VMap (m, _) ->
      (match (Mtbdd.pick_leaf m).v with
        | VBool _ -> false
        | _ -> true)
    | VOption None -> false
    | VOption (Some v) -> containsMap v
    | VTuple vs ->
      List.exists containsMap vs
    | VRecord map ->
      StringMap.exists (fun _ v -> containsMap v) map

let rec showMap m =
  let binding_to_string k v =
    (showValueP max_prec k, showValueP max_prec v)
  in
  let bs, default = BddMap.bindings m in
  let default = mkTr ((mkTd "*") ^ (mkTd(showValueP max_prec default))) in
  let tbl = List.fold_left (fun acc (k,v) ->
      let (k,v) = binding_to_string k v in
        Printf.sprintf "%s%s" acc (mkTr ((mkTd k) ^ (mkTd v)))) "" bs
  in
    mkTable(tbl ^ default)

and showSet m =
  let binding_to_string def k v =
    match v.v with
      | VBool b when b = def -> ""
      | VBool _ -> showValueP max_prec k
      | _ -> failwith "impossible"
  in
  let bs, default = BddMap.bindings m in
  let def = match default.v with
    | VBool b -> b
    | _ -> failwith "impossible"
  in
  let tbl =
    PrimitiveCollections.printList (fun (k,v) -> binding_to_string def k v) bs "{" "," "}"
  in
    if def then
      Printf.sprintf "* \ %s" tbl
    else
      Printf.sprintf "%s" tbl

and showValueP prec v =
  match v.v with
    | VUnit ->  "()"
    | VBool true ->  "T"
    | VBool false ->  "F"
    | VInt i -> (Integer.to_string i)
    | VMap m ->
      (match (Mtbdd.pick_leaf (fst m)).v with
        | VBool _ -> (* special handling for sets *)
          showSet m
        | _ -> showMap m)
    | VTuple vs ->
      if List.is_empty vs then "[]" else
        (PrimitiveCollections.printList (showValueP max_prec) vs "(" "," ")")
    | VOption None -> (* Printf.sprintf "None:%s" (ty_to_string (oget v.vty)) *)
      "None"
    | VOption (Some v) ->
      let s = Printf.sprintf "Some " ^ showValueP max_prec v in
        if max_prec > prec then Printf.sprintf "(%s)" s else s
    | VClosure _ -> failwith "ignoring closures for now"
    | VRecord map ->
      if containsMap v then
        showRecordTableP prec map
      else
        showRecordP prec map
    | VNode n -> Printf.sprintf "%dn" n
    | VEdge (n1, n2) -> Printf.sprintf "%d~%d" n1 n2

and showRecordTableP prec record =
  let fields = mkTr (StringMap.fold (fun k _ acc -> Printf.sprintf "%s%s" acc (mkTh k)) record "") in
  let values = mkTr (StringMap.fold (fun _ v acc -> Printf.sprintf "%s%s" acc (mkTd (showValueP prec v)))
                       record "")
  in
    mkTable (fields ^ values)

and showRecordP prec record =
  Printf.sprintf "{%s}"
    (StringMap.fold (fun k v acc -> Printf.sprintf "%s%s = %s; " acc k (showValueP prec v)) record "")

let showValue v =
  Jupyter_notebook.printf "%s" (showValueP max_prec v)


let showSymbolics symbs =
  let names = mkTr ((mkTh ("Symbolic")) ^ (mkTh ("Concrete Value"))) in
  let contents = VarMap.fold
      (fun k v acc ->
         let vstring = showValueP max_prec v in
       Printf.sprintf "%s%s" acc (mkTr ((mkTd (Nv_datastructures.Var.name k)) ^ (mkTd vstring)));
      ) symbs ""
  in
    Jupyter_notebook.printf "%s" (mkTable (names ^ contents))

let showAssertions asserts =
  let names = mkTr ((mkTh ("Assertion")) ^ (mkTh ("Nodes"))) in
  let trueAssertions, falseAssertions = AdjGraph.VertexMap.partition (fun _ v -> v) asserts in
  let trueAssertions = AdjGraph.VertexMap.bindings trueAssertions in
  let falseAssertions = AdjGraph.VertexMap.bindings falseAssertions in
  let t =
    mkTr ~style:"background-color: #addeaa;"
      (mkTd ("Passed") ^
       (mkTd(Collections.printList
               (fun (k,_) -> Printf.sprintf "%s" (string_of_int k)) trueAssertions "" "," "")))
  in
  let f =
    mkTr ~style:"background-color: #deaeaa;"
      (mkTd ("Failed") ^
       (mkTd(Collections.printList
               (fun (k,_) -> Printf.sprintf "%s" (string_of_int k)) falseAssertions "" "," "")))
  in
    Jupyter_notebook.printf "%s" (mkTable (names ^ t ^ f))

let checkAssertions (answers : Solution.t option) =
  (match answers with
    | None ->
      Jupyter_notebook.printf "<font color=\"green\">All assertions passed!</font>"
    | Some m ->
      let asserts = match m.assertions with [] -> AdjGraph.VertexMap.empty | [ms] -> ms in
      let all_pass = AdjGraph.VertexMap.for_all (fun _ b -> b) asserts in
        if all_pass then
          Jupyter_notebook.printf  "<font color=\"green\">All assertions passed!</font>"
        else
          begin
            showSymbolics m.symbolics;
            showAssertions asserts
          end);
  Jupyter_notebook.display_formatter "text/html"

let showSolutions ?(asTable=false) (solution : Solution.t option) =
  (match solution with
    | None ->
      Jupyter_notebook.printf  "<font color=\"blue\">No solutions computed!</font>"
    | Some solution ->
      if asTable then
        begin
          let contents =
            AdjGraph.VertexMap.fold (fun node sol acc ->
                acc ^ mkTr(mkTd(Printf.sprintf "%d" node) ^ mkTd(showValueP max_prec sol)))
              solution.labels ""
          in
          let header = mkTr(mkTh("Node") ^ mkTh("Solution")) in
            Jupyter_notebook.printf "%s" (mkTable (header ^ contents))
        end
      else
        AdjGraph.VertexMap.iter (fun node sol ->
            Jupyter_notebook.printf "<h3>Node %d</h3> <hr style=\"border-top: 1px solid #999; width=90%%;\">" node;
            showValue sol) solution.labels);
  Jupyter_notebook.display_formatter "text/html"
