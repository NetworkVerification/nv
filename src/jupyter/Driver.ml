open Nv.Main_defs
open Nv_datastructures
open Nv_solution
open Nv_lang.Collections
open Jupyter
open Lwt

let computeFile args file =
  Printexc.record_backtrace true;
  let cfg, info, file, net, fs =
    parse_input (Array.append [|"nv"|] (Array.append args [|file|]))
  in
  let networkOp =
    if cfg.smt
    then run_smt file
    else if cfg.random_test
    then run_test
    else if cfg.simulate
    then run_simulator
    else if cfg.compile
    then run_compiled file
    else exit 0
  in
  match networkOp cfg info net fs with
  | CounterExample sol, fs -> Some (apply_all sol fs)
  | Success (Some sol), fs -> Some (apply_all sol fs)
  | Success None, _ -> None
;;

(* Gets a text of the first cell and sends it to the OCaml kernel. *)
let dispPrevCell =
  Jupyter_notebook.display
    "text/html"
    {|<script>
Jupyter.notebook.kernel.comm_manager.register_target('comm-code', function(comm, msg){
  comm.on_msg(function (msg) {
        var cell_element = Jupyter.notebook.get_selected_cell()
        var index = Jupyter.notebook.find_cell_index(cell_element)
        console.log(index);
    comm.send(Jupyter.notebook.get_cell(index-2).get_text());
  });
});
</script>|}
;;

let mvar : string Lwt_mvar.t = Lwt_mvar.create_empty ()

let receive_cell_text _ json =
  [%of_yojson: string] json
  |> function
  | Ok s -> Lwt.async (fun () -> Lwt_mvar.put mvar s)
  | Error msg -> failwith msg
;;

(* Registers a comm for acception of messages from JavaScript code. *)
let target = Jupyter_comm.Manager.Target.create "comm-code" ~recv_msg:receive_cell_text
let comm = Jupyter_comm.Manager.Comm.create target

let loadNetwork () =
  (* 0 is arbritrary, assume it's a code for communication*)
  Jupyter_comm.Manager.Comm.send comm (`Int 0)
;;

let createSrp () =
  let tmpFile, out = Filename.open_temp_file "nv" "file" in
  let str = Lwt_main.run (Lwt_mvar.take mvar) in
  let _, str = BatString.replace str "```ocaml" "" in
  let _, str = BatString.replace str "```" "" in
  Printf.fprintf out "%s" str;
  flush out;
  (* Format.printf "%s@." tmpFile;
   * Format.printf "%s@." str; *)
  tmpFile
;;

let computeNetwork args = computeFile args (createSrp ())
