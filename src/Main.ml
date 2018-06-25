(* Driver *)

open Syntax
open Printing
open Interp

(* Command Line Arguments *)

let simulate_flag = ref false
let verbose_flag = ref false
let debug_flag = ref false
let filename_flag = ref ""
  
let debug () = !debug_flag
let verbose () = !verbose_flag
let filename () = !filename_flag
let simulate () = !simulate_flag
  
let set_filename s = filename_flag := s
  
let commandline_processing () =
  let speclist =
    [("-d", Arg.Set debug_flag, "Enables debugging mode");
     ("-f", Arg.String (set_filename), "SRP definition file");
     ("-v", Arg.Set (verbose_flag), "Print SRP definition file");
     ("-s", Arg.Set (simulate_flag), "Simulate SRP definition file");
    ]
  in
  let usage_msg = "SRP verification. Options available:" in
  Arg.parse speclist print_endline usage_msg


let main =
  let () = commandline_processing () in
  let ds = Input.read_from_file (filename()) in
  print_endline (Printing.declarations_to_string ds)


(*
let prog =
  "let nodes = 2 \
\
let edges = {\
 0=1;\
}\
\
let merge x y =\
  if x < y then x else y\
\
let trans x = x + 1\
\
let init = {\
 0=0;\
}"


let e = "2"

let fn = "examples/simple.nv"
    
let main =
  let ds = Input.read_from_file fn in
  print_endline (Printing.declarations_to_string ds)

*)
