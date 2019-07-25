open Nv_datastructures
open ANSITerminal
open Nv_core.Collections

type t =
  { symbolics: Nv_core.Syntax.value VarMap.t
  ; labels: Nv_core.Syntax.value AdjGraph.VertexMap.t
  ; assertions: bool AdjGraph.VertexMap.t option }

let print_solution solution =
  let cfg = Nv_core.Cmdline.get_cfg () in
  print_newline () ;
  if cfg.verbose then (
    VarMap.iter
      (fun k v ->
         Printf.printf "%s:%s\n" (Nv_datatypes.Var.name k) (Nv_core.Printing.value_to_string v) )
      solution.symbolics ;
    AdjGraph.VertexMap.iter
      (fun k v ->
        Printf.printf "Label(%d):%s\n"
          k
          (Nv_core.Printing.value_to_string v) )
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
