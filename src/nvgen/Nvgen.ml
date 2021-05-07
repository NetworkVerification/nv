open Batteries
open Cmdline
open Nv_lang
open Nv_lang.Syntax
open Partition

(* TODO *)

type networkCut = { cut : fattreeCut }
type hijackStub = ()
type notransStub = ()

type genOp =
  | Cut of networkCut
  | Hijack of hijackStub
  | Notrans of notransStub

let main_func () : unit =
  let cfg, rest = argparse default "nvgen" Sys.argv in
  let file = rest.(0) in
  let decls, info = Input.parse file in
  ()
;;
