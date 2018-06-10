(* Driver *)

open Syntax
open Printing
open Interp

let t = VBool true
let f = VBool false
let e1 = EVal t
let e2 = EVal f
let e3 = EOp (And, [e1; e2])
let v4 = interp e3

let pl = print_endline
  
let main =
  pl (exp_to_string e1);
  pl (exp_to_string e2);
  pl (exp_to_string e3);
  pl (value_to_string v4);
