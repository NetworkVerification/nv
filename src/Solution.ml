open Graph
open ANSITerminal
open Collections

type t =
  { symbolics: Syntax.value StringMap.t
  ; labels: Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }

let print_solution solution =
  let cfg = Cmdline.get_cfg () in
  print_newline () ;
  if cfg.verbose then (
    StringMap.iter
      (fun k v ->
        Printf.printf "%s:%s\n" k (Printing.value_to_string v) )
      solution.symbolics ;
    Graph.VertexMap.iter
      (fun k v ->
        Printf.printf "%s:%s\n"
          (Integer.to_string k)
          (Printing.value_to_string v) )
      solution.labels ) ;
  ( match solution.assertions with
  | None ->
      print_string [green; Bold] "Success: " ;
      Printf.printf "all assertions passed\n"
  | Some m ->
      let all_pass = Graph.VertexMap.for_all (fun _ b -> b) m in
      if all_pass then (
        print_string [green; Bold] "Success: " ;
        Printf.printf "all assertions passed\n" )
      else
        Graph.VertexMap.iter
          (fun k v ->
            if not v then (
              print_string [red; Bold] "Failed: " ;
              Printf.printf "assertion for node %s\n"
                (Integer.to_string k) ) )
          m ) ;
  print_newline ()
