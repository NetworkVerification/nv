(* open SrpNative *)

let load_srp name = failwith "todo"
  (* Printf.printf "reaches1\n";
   * let name = Dynlink.adapt_filename name in
   *   Printf.printf "%s\n" name;
   *   flush_all ();
   * if true (\* Sys.file_exists name  *\)then
   *   try
   *     Printf.printf "reaches\n";
   *     (\* Dynlink.load_packages name; *\)
   *       Printf.printf "crashes\n";
   *   with
   *   | (Dynlink.Error err) as e ->
   *      Printf.printf "ERROR loading plugin: %s" (Dynlink.error_message err);
   *      raise e
   *   | _ -> failwith "Unknown error while loading SRP"
   * else
   *   failwith "Could not find SRP file" *)

let simulate name = failwith "todo"
  (* let build_dir = Sys.getenv "NV_BUILD" in
   *   Printf.printf "reaches0\n";
   *   load_srp (Printf.sprintf "%s/%s.cmxs" build_dir name);
   *   Printf.printf "loaded\n";
   *   (\* let module Srp = (val get_srp () : NATIVE_SRP) in *\)
   *     failwith "error" *)
  (* let module SrpSimulator = (val (module SrpSimulation(Srp) : SrpSimulationSig)) in
   * SrpSimulator.simulate_srp () *)
