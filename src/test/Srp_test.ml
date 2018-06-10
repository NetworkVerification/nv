(* Testing for SRP *)

open Syntax
open OUnit
open Unsigned
open Printf
open Srp

(* variables *)

let x = "x"
let y = "y"
let xe = EVar "x"
let ye = EVar "y"

(* integers *)

let u0 = UInt32.zero  
let u1 = UInt32.one
let u2 = UInt32.of_int 2
let u3 = UInt32.of_int 3
let u4 = UInt32.of_int 4
let u10 = UInt32.of_int 10

(* values *)

let t = VBool true
let f = VBool false
let z = VUInt32 UInt32.zero
let one = VUInt32 UInt32.one
let two = VUInt32 (UInt32.of_int 2)
let three = VUInt32 (UInt32.of_int 3)

(* functions *)
let lam x e = ([x], e)
let lams xs e = (xs, e)
  
let incr_f = lam x (EOp (UAdd, [xe; EVal one]))
let less_f = lams [x;y] (EIf (EOp (ULessEq, [xe; ye]), xe, ye))
  
(* SRPs *)
  
(* Diamond:
   0 -> 1 -> 3
   0 -> 2 -> 3 *)
  
let diamond_g =
  Graph.add_edges (Graph.create u4)
    [(u0,u1);
     (u1,u3);
     (u0,u2);
     (u2,u3);
    ]
  
let srp = {
  graph = diamond_g;
  trans = (fun e -> incr_f);
  merge = (fun v -> less_f);
}

let init = [(u0, VUInt32 u0)]
let default = VUInt32 u10

let tests =
  [(srp, init, default), [(u0,VUInt32 u0); (u1,VUInt32 u1); (u2,VUInt32 u1); (u3,VUInt32 u2)]]

let do_test i ((srp, init, default), expected) =
  print_endline ("TEST " ^ string_of_int i ^ ":");
  print_endline ("topology: ");
  Graph.print srp.graph;
  print_endline ("initial state");
  let initial_state = Srp.create_state srp.graph init default in
  Srp.print_state initial_state;
  let final_state = Srp.simulate_init srp initial_state (List.map (fun (v,a) -> v) init) in
  print_endline ("final state");
  Srp.print_state final_state
    
    
let all_tests () =
  List.iteri do_test tests
    
let main =
  all_tests ()
    
(*
let do_test (s, i, d) l () =
  let final = simulate s i d in
  assert_equal ~printer:Printing.value_to_string
    
    
(* utilties *)

let test_all tests =
  List.mapi
    (fun i arg ->
      let name = "test" ^ (string_of_int i) in
      let test () = f arg in
      name >::test) tests

let t_interp (e, result) =
  assert_equal ~printer:Printing.value_to_string (Interp.interp e) result 
    
let expression_suite = "interpreting expressions">:::
  test_all t_interp expression_tests
  
let _ = run_test_tt_main expression_suite
    *)
