(** * Sets up communication with SMT solver *)

(* TODO: 1. Don't fix the solver, instead get it through an
   environment variable *)

let solver = "z3"
           
let solver_params = ["-in"]

type solver_proc =
  { pid             : int;
    nvin            : in_channel;
    nvout           : out_channel;
    mutable running : bool;
  }
  
let start_solver (params : string list) =
  (* compute params *)
  let params = solver_params @ params in
  
  (* pipe that nv writes to and solver reads from *)
  let (solver_in, nv_out) = BatUnix.pipe ~cloexec:false () in
  (* pipe that solver writes to and nv reads from *)
  let (nv_in, solver_out) = BatUnix.pipe ~cloexec:false () in

  (* Solver should not get the descriptors used by nv to read and write *)
  BatUnix.set_close_on_exec nv_in;
  BatUnix.set_close_on_exec nv_out;

  let pid = BatUnix.create_process solver (Array.of_list (solver :: params))
              solver_in solver_out solver_out in

  (* NV should close the descriptors used by the solver *)
  BatUnix.close solver_in;
  BatUnix.close solver_out;
  let cin = Unix.in_channel_of_descr nv_in in
  set_binary_mode_in cin false;
  let cout = Unix.out_channel_of_descr nv_out in
  set_binary_mode_out cout false;  
  (* let output = BatIO.output_channel ~cleanup:true cout in *)
  {pid=pid; nvin = cin; nvout = cout; running = true}

let ask_solver (solver: solver_proc) (question: string) : unit =
  (* BatIO.write_string solver.nvout question *)
  output_string solver.nvout question;
  flush solver.nvout

let get_reply (solver: solver_proc) : string option =
  try Some (input_line solver.nvin) with End_of_file -> None

let get_reply_until marker (solver: solver_proc) : string list =
  let rec loop acc =
    try
      let s = input_line solver.nvin in
      if s = marker then
        List.rev (s :: acc)
      else
        loop (s :: acc)
    with End_of_file -> List.rev acc
  in loop []
