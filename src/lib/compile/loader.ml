open SrpNative
open Findlib
open Fl_dynload

let load_srp name =
  let () = Findlib.init () in
  (* let pkgs = Fl_package_base.list_packages () in
   *   List.iter (fun p -> Printf.printf "%s\n" p) pkgs; *)
  Fl_dynload.load_packages [name]

let simulate name =
  load_srp (name ^ ".plugin");
  let module Srp = (val get_srp () : NATIVE_SRP) in
  let module SrpSimulator = (val (module SrpSimulation(Srp) : SrpSimulationSig)) in
    SrpSimulator.simulate_srp ()
