(* Driver *)

open Syntax
open Printing
open Interp
open Typing
open Renaming
open Inline
open Quickcheck
open Smt
open Solution
open StateSet

(* Command Line Arguments *)

let simulate_flag = ref false

let random_test_flag = ref false

let verify_flag = ref false

let verbose_flag = ref false

let unroll_flag = ref false

let debug_flag = ref false

let filename_flag : string option ref = ref None

let sim_bound_flag : int option ref = ref None

let simulate () = !simulate_flag

let random_test () = !random_test_flag

let verify () = !verify_flag

let unroll_maps () = !unroll_flag

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
    ; ("-r", Arg.Set random_test_flag, "Random test SRP definition file")
    ; ("-b", Arg.Int set_bound, "Bound on number of SRP simulation steps")
    ; ("-smt", Arg.Set verify_flag, "Verify the SRP definition file using SMT")
    ; ( "-unroll-maps"
      , Arg.Set unroll_flag
      , "Try to optimize an SMT encoding by unrolling maps" ) ]
  in
  let usage_msg = "SRP verification. Options available:" in
  Arg.parse speclist print_endline usage_msg

let rec apply_all s fs =
  match fs with [] -> s | f :: fs -> apply_all (f s) fs

let run_smt info ds =
  let fs = ref [] in
  let decls, f = Renaming.alpha_convert_declarations ds in
  fs := f :: !fs ;
  let decls = Inline.inline_declarations info decls in
  let res =
    if unroll_maps () then (
      let decls, vars, f = MapUnrolling.unroll info decls in
      Printf.printf "baz\n";
      let decls = Inline.inline_declarations info decls in
      fs := f :: !fs ;
      Smt.solve decls ~symbolic_vars:vars )
    else Smt.solve decls ~symbolic_vars:[]
  in
  match res with
  | Unsat -> ()
  | Unknown -> Console.error "SMT returned unknown"
  | Sat solution -> print_solution (apply_all solution !fs)

let main =
  let () = commandline_processing () in
  let ds, info = Input.parse (filename ()) in
  let decls = Typing.infer_declarations info ds in
  Typing.check_annot_decls decls ;
  if verbose () then (
    print_endline "** SRP Definition **" ;
    print_endline (Printing.declarations_to_string ds) ;
    print_endline "** End SRP Definition **" ) ;
  if verify () then run_smt info decls ;
  ( if random_test () then
      let sol = Quickcheck.check_random decls ~iterations:100 in
      match sol with None -> () | Some sol -> print_solution sol ) ;
  if simulate () then (
    let solution, q =
      match bound () with
      | None -> (Srp.simulate_declarations decls, [])
      | Some b -> Srp.simulate_declarations_bound decls b
    in
    print_solution solution ;
    match q with
    | [] -> ()
    | qs ->
        print_string "non-quiescent nodes:" ;
        List.iter
          (fun q -> print_string (Unsigned.UInt32.to_string q ^ ";"))
          qs )
