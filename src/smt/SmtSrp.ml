open Syntax
open SmtUtils
open SmtExprEncodings

let node_exp (u: Integer.t) : Syntax.exp =
  aexp(e_val (vint u), Some Typing.node_ty, Span.default)

let edge_exp (u: Integer.t) (v: Integer.t) : Syntax.exp =
  aexp(e_val (vtuple [vint u; vint v]), Some Typing.edge_ty, Span.default)

let init_exp einit u =
  Interp.Full.interp_partial_fun einit [node_exp u]

(* Reduces the transfer function, maybe a full reduction is not
     necessary at this point, experiment to see if just reducing based
     on the edge is better *)
let trans_exp etrans u v x =
  let args = (edge_exp u v) :: [x] in
  Syntax.apps etrans args
(* (Interp.Full.interp_partial_fun etrans args) (\* |> Tnf.tnf_exp *\) *)

let merge_exp emerge u x y =
  let args = (node_exp u) :: x :: [y] in
  let e = Syntax.apps emerge args in
  (* let e = (Interp.Full.interp_partial_fun emerge args) in *)
  (* Printf.printf "merge after interp:\n%s\n" (Printing.exp_to_string e); *)
  e

let network_to_srp net =
  (* Create a map from nodes to variables denoting
       the label of the node*)
  let labelling =
      AdjGraph.fold_vertices (fun u acc ->
          (* the string name that corresponds to the label of node u*)
          let lbl_u_name = label_var u in
          let lbl_u = Boxed.create_strings lbl_u_name net.attr_type in
          (*create label vars *)
          let lbl_vars = Boxed.lift1 Var.create lbl_u in
          let lbl_exp =
            Boxed.lift1 (fun v -> aexp(evar v, Some net.attr_type, Span.default))
              lbl_vars
          in
          let lbl_exp = Boxed.to_list lbl_exp |> BatList.hd in
          AdjGraph.VertexMap.add u lbl_exp acc)
        (AdjGraph.num_vertices net.graph) AdjGraph.VertexMap.empty
  in
  (* Map from nodes to incoming messages*)
  let incoming_messages_map =
    BatList.fold_left (fun acc (u,v) ->
        (* Find the label variables associated with node u*)
        let lblu = AdjGraph.VertexMap.find u labelling in
        (*compute the incoming message through the transfer function *)
        let transuv = trans_exp net.trans u v lblu in
        (* add them to the incoming messages of node v *)
        AdjGraph.VertexMap.modify_def [] v (fun us -> transuv :: us) acc)
      AdjGraph.VertexMap.empty (AdjGraph.edges net.graph)
  in
  (* map from nodes to the merged messages *)
  let merged_messages_map =
    AdjGraph.fold_vertices (fun u acc ->
        let messages = AdjGraph.VertexMap.find_default [] u incoming_messages_map in
        let best = BatList.fold_left (fun accm m ->
                       merge_exp net.merge u m accm)
                     (init_exp net.init u) messages
        in
        let best_eval = Interp.Full.interp_partial best in
        (* Printf.printf "merge after interp:\n%s\n" (Printing.exp_to_string best_eval); *)
        AdjGraph.VertexMap.add u best_eval acc)
      (AdjGraph.num_vertices net.graph) AdjGraph.VertexMap.empty
  in
  { srp_attr = net.attr_type;
    srp_constraints = merged_messages_map;
    srp_labels = labelling;
    srp_symbolics = net.symbolics;
    srp_assertion = net.assertion;
    srp_requires = net.requires
  }
