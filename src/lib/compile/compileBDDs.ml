open Nv_lang
open Syntax
open Cudd
    
(* Expression map cache used to avoid recompiling mapIf predicates. First
   element of the value is the bdd, second one is the identifier used to look it
   up in the compiled BDDs module *)
let bddfunc_cache : (bool Cudd.Mtbdd.t * int) Collections.ExpMap.t ref = ref Collections.ExpMap.empty

let bddfunc_id = ref 0

let fresh_bdd_id () =
  let x = !bddfunc_id in
  incr bddfunc_id;
  x

let bdd_array = ref (BatArray.create 0 ((BddFunc.bdd_of_bool true) |> BddFunc.wrap_mtbdd))

let build_bdd_array () =
  let arr = BatArray.create (!bddfunc_id) ((BddFunc.bdd_of_bool true) |> BddFunc.wrap_mtbdd) in
  Collections.ExpMap.iter (fun _ (bdd, bdd_id) -> BatArray.set arr bdd_id bdd) !bddfunc_cache;
  bdd_array := arr

let get_bdd =
  fun i -> BatArray.get !bdd_array i

let type_cache : int Collections.TypeMap.t ref = ref Collections.TypeMap.empty
let type_id = ref 0

let fresh_type_id () =
  let x = !type_id in
  incr type_id;
  x

let type_array = ref (BatArray.create 0 TUnit)

let build_type_array () =
  let arr = BatArray.create (!type_id) (TUnit) in
  Collections.TypeMap.iter (fun typ ty_id -> BatArray.set arr ty_id typ) !type_cache;
  type_array := arr

let get_type i =
  BatArray.get !type_array i

(* Gets a fresh id and adds it to the cache or returns an existing one *)
let get_fresh_type_id typ =
  match Collections.TypeMap.Exceptionless.find typ !type_cache with
  | None ->
    let new_id = fresh_type_id () in
    type_cache := Collections.TypeMap.add typ new_id !type_cache;
    new_id
  | Some id -> id
