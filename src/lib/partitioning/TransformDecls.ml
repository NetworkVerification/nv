open Nv_lang
open Syntax

let transform_init (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let OpenAdjGraph.{ inputs; outputs;_ } = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let _branches =
    (* create a (pattern * exp) from each input and output *)
    default_branch
  in
  failwith "TODO"
  (* DInit (ematch branches) *)

let transform_trans (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let OpenAdjGraph.{ inputs; outputs;_ } = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let _branches =
    default_branch
  in
  failwith "TODO"
  (* DTrans (ematch branches) *)

let transform_merge (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let OpenAdjGraph.{ inputs; outputs;_ } = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let _branches =
    default_branch
  in
  failwith "TODO"
  (* DMerge (ematch branches) *)

