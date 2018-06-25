(* Driver *)

open Syntax
open Printing
open Interp

let t = VBool true
let f = VBool false
let e1 = EVal t
let e2 = EVal f
let e3 = EOp (And, [e1; e2])
let v4 = interp e3

let pl = print_endline


let print_components cs =
  print_endline "made it!"

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
    
let main () =
  let () = commandline_processing () in
  let components = Input.read_from_file (filename()) in
  if verbose() then
    print_components components;
  

