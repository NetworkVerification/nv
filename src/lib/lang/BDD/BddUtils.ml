open Syntax
open Cudd
open Nv_utils
open Nv_datastructures

let mgr = Man.make_v ()

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for _ = 1 to sz - num_vars do ignore (Bdd.newvar mgr) done

let ithvar i =
  set_size (i + 1) ;
  Bdd.ithvar mgr i

let rec ty_to_size ty =
  match get_inner_type ty with
  | TUnit -> 1 (* I don't understand how Cudd BDDs work, so encode TUnit as false *)
  | TBool -> 1
  | TInt _ -> 32
  | TOption tyo -> 1 + ty_to_size tyo
  | TTuple ts ->
    List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TRecord tmap -> ty_to_size (TTuple (RecordUtils.get_record_entries tmap))
  | TNode -> ty_to_size (TInt 32) (* Encode as int *)
  | TEdge -> ty_to_size (TTuple [TNode; TNode]) (* Encode as node pair *)
  | TArrow _ | TMap _ | TVar _ | QVar _ ->
    failwith ("internal error (ty_to_size): " ^ (PrintingRaw.show_ty ty))

let tbl =
  Mtbdd.make_table
    ~hash:(hash_value ~hash_meta:false)
    ~equal:(equal_values ~cmp_meta:false)

let tbl_bool =
  Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

let get_bit (n: Integer.t) (i: int) : bool =
  let z = Integer.value n in
  let marker = (Z.shift_left Z.one i) in
  Z.logand z marker <> Z.zero

let mk_int i idx =
  let acc = ref (Bdd.dtrue mgr) in
  let sz = Integer.size i in
  for j = 0 to sz - 1 do
    let var = ithvar (idx + j) in
    let bit = get_bit i j in
    let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
    acc := Bdd.dand !acc (Bdd.eq var bdd)
  done ;
  !acc

let tbool_to_bool tb =
  match tb with Man.False | Man.Top -> false | Man.True -> true
