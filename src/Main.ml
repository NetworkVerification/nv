(* Driver *)

open Syntax
open Printing
open Interp
open Typing
open Renaming
open Inline

(* Command Line Arguments *)

let simulate_flag = ref false

let verbose_flag = ref false

let debug_flag = ref false

let filename_flag : string option ref = ref None

let sim_bound_flag : int option ref = ref None

let simulate () = !simulate_flag

let debug () = !debug_flag

let verbose () = !verbose_flag

let filename () =
  match !filename_flag with
  | None ->
      print_endline "use -f <filename> to add nv file" ;
      exit 0
  | Some f -> f


let bound () = !sim_bound_flag

let set_filename s = filename_flag := Some s

let set_bound n = sim_bound_flag := Some n

let commandline_processing () =
  let speclist =
    [ ("-d", Arg.Set debug_flag, "Enables debugging mode")
    ; ("-f", Arg.String set_filename, "SRP definition file")
    ; ("-v", Arg.Set verbose_flag, "Print SRP definition file")
    ; ("-s", Arg.Set simulate_flag, "Simulate SRP definition file")
    ; ("-b", Arg.Int set_bound, "Bound on number of SRP simulation steps") ]
  in
  let usage_msg = "SRP verification. Options available:" in
  Arg.parse speclist print_endline usage_msg


let main =
  let () = commandline_processing () in
  let ds, info = Input.parse (filename ()) in
  let decls = Typing.infer_declarations 0 info ds in
  let decls = Renaming.alpha_convert_declarations decls in
  let decls = Inline.inline_declarations decls in
  print_endline "" ;
  print_endline "** Starting SRP Processing **" ;
  if verbose () then (
    print_endline "** SRP Definition **" ;
    print_endline (Printing.declarations_to_string ds) ;
    print_endline "** End SRP Definition **" ) ;
  if simulate () then (
    print_endline "** Starting SRP Simulation **" ;
    let solution, q =
      match bound () with
      | None -> (Srp.simulate_declarations decls, [])
      | Some b -> Srp.simulate_declarations_bound decls b
    in
    print_endline "** SRP Solution **" ;
    Srp.print_solution solution ;
    ( match q with
    | [] -> ()
    | qs ->
        print_string "non-quiescent nodes:" ;
        List.iter
          (fun q -> print_string (Unsigned.UInt32.to_string q ^ ";"))
          qs ) ;
    print_endline "** End SRP Solution **" )
