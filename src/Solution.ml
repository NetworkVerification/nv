open Graph
open ANSITerminal

module StringMap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

type t =
  { symbolics: Syntax.value StringMap.t
  ; labels: Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }

let print_solution solution =
  print_newline ();
  StringMap.iter
    (fun k v -> Printf.printf "%s:%s\n" k (Printing.value_to_string v))
    solution.symbolics ;
  Graph.VertexMap.iter
    (fun k v ->
      Printf.printf "%s:%s\n"
        (Unsigned.UInt32.to_string k)
        (Printing.value_to_string v) )
    solution.labels ;
  match solution.assertions with
  | None -> ()
  | Some m ->
      let all_pass = Graph.VertexMap.for_all (fun _ b -> b) m in
      if all_pass then (
        print_string [green; Bold] "Success: " ;
        Printf.printf "all assertions passed\n" ;)
      else
        (Graph.VertexMap.iter
          (fun k v ->
            if not v then (
              print_string [red; Bold] "Failed: " ;
              Printf.printf "assertion for node %s\n"
                (Unsigned.UInt32.to_string k) ) )
          m);
      print_newline ()

