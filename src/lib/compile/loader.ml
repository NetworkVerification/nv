open SrpNative
open Findlib
open Fl_dynload
open Nv_utils

let load_srp name =
  let () = Findlib.init () in
    try Fl_dynload.load_packages [name]
    with Dynlink.Error err ->
      Printf.printf "%s\n" (Dynlink.error_message err)

let simulate name net =
  Compile.compile_ocaml name net; (* TODO: make this optional *)
  load_srp (name ^ ".plugin");
  let module Srp = (val get_srp () : NATIVE_SRP) in
  let module SrpSimulator = (val (module SrpSimulation(Srp) : SrpSimulationSig)) in
    Profile.time_profile "Native simulation"
      (fun () -> SrpSimulator.simulate_srp net.attr_type net.graph)
