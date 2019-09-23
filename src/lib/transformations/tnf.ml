(** * Tuple normal form transformation*)
(* need a proper name for this *)
open Nv_lang
open Collections
open Syntax
open Nv_utils.OCamlUtils

(** For now, assume it only applies to unboxed and inlined NV
   programs. It seems like a reasonable assumption *)

let rec tnf_exp e : exp =
  match e.e with
  | ETy (e, ty) -> ety (tnf_exp e) ty |> wrap e
  | EVal _
  | EVar _ -> e
  | EFun f -> efun {f with body = tnf_exp f.body} |> wrap e
  | EApp (_, _) ->
     failwith "ignore this case for now"
  | EIf (e1, e2, e3) ->
     let e1 = tnf_exp e1 in
     (* Printf.printf "e2before=%s\n" (Printing.exp_to_string e2); *)
     let e2 = tnf_exp e2 in
     let e3 = tnf_exp e3 in
     (match (oget e.ety) with
      | TTuple _ ->
         (* Printf.printf "e1 = %s\n\n e2 = %s\n\n e3 = %s\n" (Printing.exp_to_string e1) (Printing.exp_to_string e2) (Printing.exp_to_string e3); *)
         let es2 = tupleToList e2 in
         let es3 = tupleToList e3 in
         (* Printf.printf "%d,%d\n" (BatList.length es2) (BatList.length es3); *)
         aexp(etuple (BatList.map2 (fun e2 e3 -> eif e1 e2 e3 |> wrap e2) es2 es3),
              e.ety, e.espan)
      | _ -> aexp(eif e1 e2 e3, e.ety, e.espan))
     | ELet (x, e1, e2) ->
        let e1 = tnf_exp e1 in
        let e2 = tnf_exp e2 in
        (match oget e2.ety with
         | TTuple _ ->
            aexp (etuple (BatList.map (fun e2 -> elet x e1 e2 |> wrap e2) (tupleToList e2)),
                  e.ety, e.espan)
         | _ ->
            aexp (elet x e1 e2,e.ety, e.espan))
     | ETuple es ->
        (etuple (BatList.fold_right (fun e acc ->
                     let e' = tnf_exp e in
                    match e'.e with
                    | ETuple es -> es @ acc
                    | _ -> e' :: acc) es [])) |> wrap e
     | ESome e1 ->
        aexp (esome (tnf_exp e1), e.ety, e.espan)
     | EMatch (e1, bs) ->
        let es1 = tnf_exp e1 in
        let bs = mapBranches (fun (p,b) ->
                     (* Printf.printf "b before tnf :%s\n\n" (Printing.exp_to_string b); *)
                     (p, tnf_exp b)) bs in
        (match oget e.ety with
         |  TTuple ts ->
             let es =
               BatList.mapi (fun i ty ->
                   aexp(ematch es1
                          (mapBranches (fun (p,b) ->
                               (* Printf.printf "%d,%d:%s\n\n" i (List.length (tupleToList b)) (Printing.exp_to_string b); *)
                               (p, BatList.nth (tupleToList b) i)) bs),
                        Some ty, Nv_datastructures.Span.default)) ts
             in
             aexp(etuple es, e.ety, e.espan)
         | _ ->
            aexp (ematch es1 bs, e.ety, e.espan))
     | EOp (op, es) -> (
       match op with
       | And
         | Or
         | Not
         | UAdd _
         | USub _
         | Eq
         | ULess _
         | AtMost _
         | MCreate
         | MGet
         | MSet
         | MMap
         | MMapFilter
         | MMerge
         | MFoldNode
         | MFoldEdge
         | ULeq _
         | NLess
         | NLeq
         | TGet _
         | TSet _ ->
          aexp (eop op (BatList.map tnf_exp es), e.ety, e.espan))
     | ERecord _ | EProject _ -> failwith "Record expression in tnf"

let tnf_net net =
  { net with init = tnf_exp net.init;
             trans = tnf_exp net.trans;
             merge = tnf_exp net.merge;
             defs = BatList.map (fun (x, ty, e) -> (x, ty, tnf_exp e)) net.defs
  }
