(* Testing for SRP interpreter *)

open Syntax
open OUnit
open Unsigned

(* variables *)

let x = "x"
let y = "y"
let xe = EVar "x"
let ye = EVar "y"

(* values *)

let t = VBool true
let f = VBool false
let z = VUInt32 UInt32.zero
let one = VUInt32 UInt32.one
let two = VUInt32 (UInt32.of_int 2)
let three = VUInt32 (UInt32.of_int 3)
  
(* expressions *)

let te = EVal t
let fe = EVal f
let ze = EVal z
let onee = EVal one
let twoe = EVal two
let threee = EVal three
  
let e1 = te
let e2 = fe 
let e3 = EOp (And, [e1;e2])
let e4 = EOp (UAdd, [EVal z;EVal one])
let e5 = EOp (Or, [xe;xe])
let e6 = ELet (x, e1, e5)
let e7 = ELet (x, e2, ELet (x, e1, e5))
let e8 = ELet (x, e2, ELet (y, e1, e5))

(* functions *)
let lam x e = ([x], e)
  
let f1 = lam x (EOp (UAdd, [xe; EVal one]))
  
(* utilties *)

let test_all f tests =
  List.mapi
    (fun i arg ->
      let name = "test" ^ (string_of_int i) in
      let test () = f arg in
      name >::test) tests

let expression_tests = [
  e1, t;
  e3, f;
  e4, one;
  e6, t;
  e7, t;
  e8, f;
]

let t_interp (e, result) =
  assert_equal ~printer:Printing.value_to_string (Interp.interp e) result 
    
let expression_suite = "interpreting expressions">:::
  test_all t_interp expression_tests

let t_app ((f,arg), result) =
  assert_equal ~printer:Printing.value_to_string (Interp.apply f [arg]) result 
  
let function_tests = [
  (f1,z), one;  
  (f1,one), two;
]

let function_suite = "interpreting functions">:::
  test_all t_app function_tests
  
let _ = run_test_tt_main expression_suite
let _ = run_test_tt_main function_suite

