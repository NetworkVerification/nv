open OUnit2
open Syntax
open Unsigned

(* Unit tests for the BddMap data structure *)

let zero_u = Unsigned.UInt32.zero

let one_u = Unsigned.UInt32.one

let two_u = Unsigned.UInt32.of_int 2

let three_u = Unsigned.UInt32.of_int 3

let five_u = Unsigned.UInt32.of_int 5

let zero = VUInt32 zero_u |> value

let one = VUInt32 one_u |> value

let two = VUInt32 two_u |> value

let three = VUInt32 three_u |> value

let five = VUInt32 five_u |> value

let zero_opt = value (VOption (Some zero))

let two_opt = value (VOption (Some two))

let five_opt = value (VOption (Some five))

let ty_int = TInt zero_u

let tru = value (VBool true)

let fal = value (VBool false)

let assert_equal_values =
  assert_equal ~cmp:equal_values ~printer:Printing.value_to_string

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
  assert_equal_values x bt ;
  assert_equal_values y bf ;
  let map = BddMap.map (fun v -> value (VBool true)) map in
  let x = BddMap.find map v2 in
  let y = BddMap.find map v1 in
  assert_equal_values x bt ;
  assert_equal_values y bt

let test2 _ =
  let k1 = value (VTuple [zero_opt; five_opt]) in
  let k2 = value (VTuple [zero_opt; zero_opt]) in
  let v1 = value (VOption None) in
  let v2 = value (VOption (Some two_opt)) in
  let ty = TTuple [ty_int; ty_int] in
  let map = BddMap.create ~key_ty:ty v1 in
  let map = BddMap.update map k1 v2 in
  let x = BddMap.find map k1 in
  let y = BddMap.find map k2 in
  assert_equal_values x v2 ;
  assert_equal_values y v1

let test3 _ =
  let k1 = value (VTuple [zero; five]) in
  let k2 = value (VTuple [zero; zero]) in
  let v1 = value (VOption None) in
  let v2 = value (VOption (Some two)) in
  let ty = TTuple [ty_int; ty_int] in
  let map1 = BddMap.create ~key_ty:ty v1 in
  let map2 = BddMap.create ~key_ty:ty v2 in
  let merged =
    BddMap.merge
      (fun v1 v2 ->
        match (v1.v, v2.v) with
        | VOption None, VOption (Some _) -> v2
        | VOption (Some _), VOption None -> v1
        | _ -> failwith "" )
      map1 map2
  in
  let x = BddMap.find merged k1 in
  let y = BddMap.find merged k2 in
  assert_equal_values x v2 ;
  assert_equal_values y v2 ;
  assert_equal_maps merged map2

let test4 _ =
  let default = value (VOption None) in
  let k1 = zero in
  let k2 = two in
  let v1 = value (VOption (Some zero)) in
  let v2 = value (VOption (Some two)) in
  let vs = [(k1, v1); (k2, v2)] in
  let map = BddMap.from_bindings ~key_ty:ty_int (vs, default) in
  let bs, df = BddMap.bindings map in
  assert_equal_values default df ;
  List.iter
    (fun b ->
      let k1, v1 = b in
      let k2, v2 =
        List.find
          (fun (k2, v2) -> equal_values k1 k2 && equal_values v1 v2)
          vs
      in
      assert_equal_values k1 k2 ;
      assert_equal_values v1 v2 )
    bs

let test5 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = exp (EVar x) in
  let cmp = exp (EOp (ULeq, [var; exp (EVal two)])) in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env cmp in
  let value = match value with BBool b -> b | _ -> failwith "" in
  let map = BddMap.create ~key_ty:ty_int bf in
  let map = BddMap.map_when value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt ;
  assert_equal_values x1 bt ;
  assert_equal_values x2 bt ;
  assert_equal_values x3 bf ;
  assert_equal_values x5 bf

let test6 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = exp (EVar x) in
  let sum = EOp (UAdd, [var; exp (EVal one)]) |> exp in
  let cmp = exp (EOp (ULess, [sum; exp (EVal two)])) in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env cmp in
  let value = match value with BBool b -> b | _ -> failwith "" in
  let map = BddMap.create ~key_ty:ty_int bf in
  let map = BddMap.map_when value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt ;
  assert_equal_values x1 bf ;
  assert_equal_values x2 bf ;
  assert_equal_values x3 bf ;
  assert_equal_values x5 bf

let test7 _ =
  let v0 = zero in
  let v1 = one in
  let v2 = two in
  let v3 = three in
  let v5 = five in
  let bt = tru in
  let bf = fal in
  let x = Var.create "x" in
  let var = exp (EVar x) in
  let e1 = exp (EOp (ULess, [var; exp (EVal three)])) in
  let e2 = exp (EOp (ULess, [var; exp (EVal five)])) in
  let e3 = exp (EOp (ULess, [var; exp (EVal two)])) in
  let e = EIf (e1, e2, e3) |> exp in
  let init_x = BddFunc.create_value ty_int in
  let env = Env.update Env.empty x init_x in
  let value = BddFunc.eval env e in
  let value = match value with BBool b -> b | _ -> failwith "" in
  let map = BddMap.create ~key_ty:ty_int bf in
  let map = BddMap.map_when value (fun _ -> bt) map in
  let x0 = BddMap.find map v0 in
  let x1 = BddMap.find map v1 in
  let x2 = BddMap.find map v2 in
  let x3 = BddMap.find map v3 in
  let x5 = BddMap.find map v5 in
  assert_equal_values x0 bt ;
  assert_equal_values x1 bt ;
  assert_equal_values x2 bt ;
  assert_equal_values x3 bf ;
  assert_equal_values x5 bf

(* Name the test cases and group them together *)
let suite =
  "suite"
  >::: [ "BddMap find/update/create" >:: test1
       ; "BddMap with nested types" >:: test2
       ; "BddMap merge/equality" >:: test3
       ; "BddMap from/to bindings" >:: test4
       ; "BddMap map_when/leq " >:: test5
       ; "BddMap map_when/lt/add" >:: test6
       ; "BddMap map_when/ite" >:: test7 ]

let () = run_test_tt_main suite
