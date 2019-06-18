open SrpNative

let load_srp name =
  let name = Dynlink.adapt_filename name in
  if Sys.file_exists name then
    try
      Dynlink.loadfile name
    with
    | (Dynlink.Error err) as e ->
       Printf.printf "ERROR loading plugin: %s" (Dynlink.error_message err);
       raise e
    | _ -> failwith "Unknown error while loading SRP"
  else
    failwith "Could not find SRP file"

let simulate name =
  load_srp name;
  let module Srp = (val get_srp () : NATIVE_SRP) in
  let module SrpSimulator = (val SrpSimulation (SRP)) in
  SrpSimulator.simulate_srp ()
