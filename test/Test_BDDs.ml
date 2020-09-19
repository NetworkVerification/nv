open BatSet
open OUnit2
open Nv
open Nv_lang
open Nv_datastructures
open Syntax

(* Unit tests for the BddMap data structure *)

let zero_u = Integer.of_int 0
let one_u = Integer.of_int 1
let two_u = Integer.of_int 2
let three_u = Integer.of_int 3
let five_u = Integer.of_int 5
let zero = vint zero_u
let one = vint one_u
let two = vint two_u
let three = vint three_u
let five = vint five_u
let zero_opt = voption (Some zero)
let two_opt = voption (Some two)
let five_opt = voption (Some five)
let ty_int = TInt 32
let tru = vbool true
let fal = vbool false
let new_key () = evar (Var.fresh "x")

let assert_equal_values =
  assert_equal ~cmp:(equal_values ~cmp_meta:false) ~printer:Printing.value_to_string
;;

let assert_equal_maps = assert_equal ~cmp:BddMap.equal

(* ~printer:BddMap.show_map *)

let test1 _ =
  let v1 = zero_opt in
  let v2 = five_opt in
  let bt = tru in
  let bf = fal in
  let ty = TOption ty_int in
  let map = BddMap.create ~key_ty:ty bf in
  let map = BddMap.update map v2 bt in
  let x = BddMap.find map v2 in
  let y = BddMap.find map v1 in
  assert_equal_values x bt;
  assert_equal_values y bf;
  let e = new_key () in
  let set = PSet.create Pervasives.compare in
  let map = BddMap.map ~op_key:(e, set) (fun _ -> vbool true) map in
  let x = BddMap.find map v2 in
  let y = BddMap.find map v1 in
  assert_equal_values x bt;
  assert_equal_values y bt
;;

let test2 _ =
  let k1 = vtuple [zero_opt; five_opt] in
  let k2 = vtuple [zero_opt; zero_opt] in
  let v1 = voption None in
  let v2 = voption (Some two_opt) in
  let ty = TTuple [ty_int; ty_int] in
  let map = BddMap.create ~key_ty:ty v1 in
  let map = BddMap.update map k1 v2 in
  let x = BddMap.find map k1 in
  let y = BddMap.find map k2 in
  assert_equal_values x v2;
  assert_equal_values y v1
;;

let test3 _ =
  let k1 = vtuple [zero; five] in
  let k2 = vtuple [zero; zero] in
  let v1 = voption None in
  let v2 = voption (Some two) in
  let ty = TTuple [ty_int; ty_int] in
  let map1 = BddMap.create ~key_ty:ty v1 in
  let map2 = BddMap.create ~key_ty:ty v2 in
  let e = evar (Var.create "x") in
  let set = PSet.create Pervasives.compare in
  let merged =
    BddMap.merge
      ~op_key:(e, set)
      (fun v1 v2 ->
        match v1.v, v2.v with
        | VOption None, VOption (Some _) -> v2
        | VOption (Some _), VOption None -> v1
        | _ -> failwith "")
      map1
      map2
  in
  let x = BddMap.find merged k1 in
  let y = BddMap.find merged k2 in
  assert_equal_values x v2;
  assert_equal_values y v2;
  assert_equal_maps merged map2
;;

let test4 _ =
  let default = voption None in
  let k1 = zero in
  let k2 = two in
  let v1 = voption (Some zero) in
  let v2 = voption (Some two) in
  let vs = [k1, v1; k2, v2] in
  let map = BddMap.from_bindings ~key_ty:ty_int (vs, default) in
  let bs, df = BddMap.bindings map in
  assert_equal_values default df;
  List.iter
    (fun b ->
      let k1, v1 = b in
      let k2, v2 =
        List.find
          (fun (k2, v2) ->
            equal_values ~cmp_meta:false k1 k2 && equal_values ~cmp_meta:false v1 v2)
          vs
      in
      assert_equal_values k1 k2;
      assert_equal_values v1 v2)
    bs
;;

let test5 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = evar x in
  let cmp = eop (ULeq 32) [var; e_val two] in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env cmp in
  let value =
    match value with
    | BBool b -> b
    | _ -> failwith ""
  in
  let value = BddFunc.wrap_mtbdd value in
  let map = BddMap.create ~key_ty:ty_int bf in
  let e = new_key () in
  let set = PSet.create Pervasives.compare in
  let map = BddMap.map_when ~op_key:(e, set) value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt;
  assert_equal_values x1 bt;
  assert_equal_values x2 bt;
  assert_equal_values x3 bf;
  assert_equal_values x5 bf
;;

let test6 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = evar x in
  let sum = eop (UAdd 32) [var; e_val one] in
  let cmp = eop (ULess 32) [sum; e_val two] in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env cmp in
  let value =
    match value with
    | BBool b -> b
    | _ -> failwith ""
  in
  let value = BddFunc.wrap_mtbdd value in
  let map = BddMap.create ~key_ty:ty_int bf in
  let e = new_key () in
  let set = PSet.create Pervasives.compare in
  let map = BddMap.map_when ~op_key:(e, set) value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt;
  assert_equal_values x1 bf;
  assert_equal_values x2 bf;
  assert_equal_values x3 bf;
  assert_equal_values x5 bf
;;

let test7 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = evar x in
  let e1 = eop (ULess 32) [var; e_val three] in
  let e2 = eop (ULess 32) [var; e_val five] in
  let e3 = eop (ULess 32) [var; e_val two] in
  let e = eif e1 e2 e3 in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env e in
  let value =
    match value with
    | BBool b -> b
    | _ -> failwith ""
  in
  let value = BddFunc.wrap_mtbdd value in
  let map = BddMap.create ~key_ty:ty_int bf in
  let e = new_key () in
  let set = PSet.create Pervasives.compare in
  let map = BddMap.map_when ~op_key:(e, set) value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt;
  assert_equal_values x1 bt;
  assert_equal_values x2 bt;
  assert_equal_values x3 bf;
  assert_equal_values x5 bf
;;

(* Name the test cases and group them together *)
let tests =
  "Test_BDDs"
  >::: [ "BddMap find/update/create" >:: test1
       ; "BddMap with nested types" >:: test2
       ; "BddMap merge/equality" >:: test3
       ; "BddMap from/to bindings" >:: test4
       ; "BddMap map_when/leq " >:: test5
       ; "BddMap map_when/lt/add" >:: test6
       ; "BddMap map_when/ite" >:: test7 ]
;;
