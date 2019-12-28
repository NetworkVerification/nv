open Nv_lib.Main_defs
open Nv_datastructures
open Nv_solution
open Nv_lang.Collections
open Jupyter

let compute args file =
  Printexc.record_backtrace true;
  let cfg, info, file, net, fs =
    parse_input (Array.append [|"nv"|] (Array.append args [|file|]))
  in
  let networkOp =
    if cfg.smt then run_smt file
    else if cfg.random_test then run_test
    else if cfg.simulate then run_simulator
    else if cfg.compile then run_compiled file
    else exit 0
  in
    match networkOp cfg info net fs with
      | CounterExample sol, fs ->
        Some (apply_all sol fs)
      | Success (Some sol), fs -> (Some (apply_all sol fs))
      | Success None, _ -> None
