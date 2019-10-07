open SrpNative
open Findlib
open Fl_dynload
open Nv_utils
open Symbolics

let load_srp name =
  let () = Findlib.init () in
    try Fl_dynload.load_packages [name]
    with Dynlink.Error err ->
      Printf.printf "%s\n" (Dynlink.error_message err)

let simulate name net =
  ignore(Compile.compile_ocaml name net); (* TODO: make this optional *)
  load_srp (name ^ ".plugin");
  let module Symbs = (val (defaultSymbolics net.symbolics)) in
  let module EnrichedSrp = (val get_srp ()) in
  let module Srp = (val (module EnrichedSrp(Symbs) : NATIVE_SRP)) in
  let module SrpSimulator = (val (module SrpSimulation(Srp) : SrpSimulationSig)) in
    Profile.time_profile "Native simulation"
      (fun () -> SrpSimulator.simulate_srp net.attr_type net.graph)
