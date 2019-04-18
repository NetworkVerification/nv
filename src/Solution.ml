open AdjGraph
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
    ANSITerminal.print_string [Foreground Blue; Bold]
                              ("Symbolic variables\n---------------------\n");
    StringMap.iter
      (fun k v ->
        Printf.printf "%s: %s\n" k (Printing.value_to_string v))
      solution.symbolics ;
    ANSITerminal.print_string [Foreground Blue; Bold]
                              ("Labels\n---------------------\n");
    AdjGraph.VertexMap.iter
      (fun k v ->
        ANSITerminal.print_string [Bold]
                                  (Printf.sprintf "  Label %d:\n" (Integer.to_int k)); 
        Printf.printf "%s\n" (Printing.value_to_string v))
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
              Printf.printf "assertion for node %s\n"
                (Integer.to_string k) ) )
          m ) ;
  print_newline ()
