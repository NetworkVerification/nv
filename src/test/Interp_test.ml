(* Testing for SRP interpreter *)

open Syntax
open OUnit
open Unsigned

(* variables *)

let x = Var.fresh "x"
let y = Var.fresh "y"
let xe = EVar x
let ye = EVar y
let xf = Var.fresh "f"
let xfe = EVar xf

(* values *)

let t = VBool true
let f = VBool false
let z = VUInt32 UInt32.zero
let one = VUInt32 UInt32.one
let ne n = VUInt32 (UInt32.of_int n)
let two = ne 2
let three = ne 3
let four = ne 4

  
(* expressions *)

let te = EVal t
let fe = EVal f
let ze = EVal z
let onee = EVal one
let twoe = EVal two
let threee = EVal three
let foure = EVal four
  
let e1 = te
let e2 = fe 
let e3 = EOp (And, [e1;e2])
let e4 = EOp (UAdd, [EVal z;EVal one])
let e5 = EOp (Or, [xe;xe])
let e6 = ELet (x, e1, e5)
let e7 = ELet (x, e2, ELet (x, e1, e5))
let e8 = ELet (x, e2, ELet (y, e1, e5))

(* functions *)
let lam x e = EVal (VFun ([x], e))
let app f e = EApp (f, [e])

let lams xs e = EVal (VFun (xs,e))
let apps e es = EApp (e, es)
  
let f1 = lam x (EOp (UAdd, [xe; EVal one]))

let f_opt =
  lams [xf;x]
    (EMatch
       (EVar x,
	EVal (VOption None),
	y, ESome (app (EVar xf) (EVar y)))
    )

let some_one = EVal (VOption (Some one))
let e_add_one_option = apps f_opt [f1; some_one]

let two_again = EMatch (e_add_one_option, foure, y, EVar y)
  
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
  app f1 ze, one;  
  app f1 onee, two;
  two_again, two;
]

let test_interp (e, result) =
  assert_equal ~printer:Printing.value_to_string (Interp.interp e) result 
    
let expression_suite = "interpreting expressions">:::
  test_all test_interp expression_tests
   
let _ = run_test_tt_main expression_suite


