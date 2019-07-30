open ANSITerminal
open Nv_datastructures
open Nv_lang
open Collections
open AdjGraph (* For VertexMap *)
open Syntax
open Nv_utils.OCamlUtils

(* The mask field is used for AttributeSlicing -- it is a syntax.value with the
   same structure as the attribute (e.g. both tuples of the same size), but
   with a boolean in place of each base value. A value of false indicates that
   the value at that location in each attribute is bogus -- i.e. it was not
   needed to produce the counterexample *)
type t =
  { symbolics: value VarMap.t
  ; labels: value VertexMap.t
  ; assertions: bool VertexMap.t option
  ; mask: value option }

let rec mask_type_ty ty =
  match ty with
  | TBool
  | TInt _
  | TEdge
  | TNode
  | TUnit -> TBool
  | TOption ty -> mask_type_ty ty
  | TRecord map -> TRecord (StringMap.map mask_type_ty map)
  | TTuple tys -> TTuple (List.map mask_type_ty tys)
  | TMap (kty, vty) -> TMap (kty, mask_type_ty vty)
  | TVar {contents = Link ty} -> mask_type_ty ty
  | TVar _ | QVar _ | TArrow _ -> failwith "internal error (mask_ty)"

let mask_type_sol sol =
  let one_attr = VertexMap.choose sol.labels |> snd in
  mask_type_ty (oget one_attr.vty)

let print_solution (solution : t) =
  let cfg = Nv_lang.Cmdline.get_cfg () in
  print_newline () ;
  if cfg.verbose then (
    VarMap.iter
      (fun k v ->
         Printf.printf "%s:%s\n" (Nv_datastructures.Var.name k) (Nv_lang.Printing.value_to_string v) )
      solution.symbolics ;
    AdjGraph.VertexMap.iter
      (fun k v ->
         Printf.printf "Label(%d):%s\n"
           k
           (Nv_lang.Printing.value_to_string v) )
      solution.labels ) ;
  ( match solution.assertions with
    | None ->
      print_string [green; Bold] "Success: " ;
      Printf.printf "No assertions provided, so none failed\n"
    | Some m ->
      let all_pass = AdjGraph.VertexMap.for_all (fun _ b -> b) m in
      if all_pass then (
        print_string [green; Bold] "Success: " ;
        Printf.printf "all assertions passed\n" )
      else
        AdjGraph.VertexMap.iter
          (fun k v ->
             if not v then (
               print_string [red; Bold] "Failed: " ;
               Printf.printf "assertion for node %d\n" k ) )
          m ) ;
  print_newline ()
