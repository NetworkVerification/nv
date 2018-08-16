open BddUtils
open Cudd
open Syntax
open Unsigned

(* TODO: 
    1. optimize variable ordering
    2. more efficient operations
    3. preprocessing of filter statements *)

type t = Syntax.value Mtbdd.t * ty

(* let res = User.map_op2
  ~commutative:true ~idempotent:true
  ~special:(fun bdd1 bdd2 ->
    if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
    else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
    else None)
  (fun b1 b2 -> b1 && b2) *)

let map (f: value -> value) ((vdd, ty): t) : t =
  let g x = f (Mtbdd.get x) |> Mtbdd.unique tbl in
  (Mapleaf.mapleaf1 g vdd, ty)

let map_when (pred: Bdd.vt) (f: value -> value) ((vdd, ty): t) : t =
  let f b v = if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique tbl else v in
  let tru = Mtbdd.cst mgr tbl_bool true in
  let fal = Mtbdd.cst mgr tbl_bool false in
  let pred = Mtbdd.ite pred tru fal in
  (Mapleaf.mapleaf2 f pred vdd, ty)

let merge (f: value -> value -> value) ((x, tyx): t) ((y, tyy): t) : t =
  let g x y = f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique tbl in
  (Mapleaf.mapleaf2 g x y, tyx)

let find ((map, _): t) (v: value) : value =
  let bdd = value_to_bdd v in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update ((map, ty): t) (k: value) (v: value) : t =
  let leaf = Mtbdd.cst mgr tbl v in
  let key = value_to_bdd k in
  (Mtbdd.ite key leaf map, ty)

let create ~key_ty:ty (v: value) : t =
  set_size (ty_to_size ty) ;
  (Mtbdd.cst mgr tbl v, ty)

let count_tops arr =
  Array.fold_left
    (fun acc tb -> match tb with Man.Top -> acc + 1 | _ -> acc)
    0 arr

let pick_default_value map =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
      let c = count_tops vars in
      if c > !count then count := c ;
      value := Some v )
    map ;
  oget !value

let bindings ((map, ty): t) : (value * value) list * value =
  let bs = ref [] in
  let dv = pick_default_value map in
  Mtbdd.iter_cube
    (fun vars v ->
      (* Array.iteri (fun i x -> Printf.printf "vars %d is %b\n" i (tbool_to_bool x)) vars; *)
      if compare_values v dv <> 0 then
        let k = vars_to_value vars ty in
        bs := (k, v) :: !bs )
    map ;
  (!bs, dv)

let from_bindings ~key_ty:ty ((bs, default): (value * value) list * value) : t =
  let map = create ~key_ty:ty default in
  List.fold_left (fun acc (k, v) -> update acc k v) map bs

let compare_maps (bm1, _) (bm2, _) = Mtbdd.topvar bm1 - Mtbdd.topvar bm2

let equal_maps bm1 bm2 = compare bm1 bm2 = 0

let hash_map (bm, _) = Mtbdd.topvar bm

let show_map bm =
  let bs, dv = bindings bm in
  let str =
    List.fold_left
      (fun acc (k, v) ->
        let sep = if acc = "" then "" else ";" in
        Printf.sprintf "%s:=%s%s%s"
          (Printing.value_to_string k)
          (Printing.value_to_string v)
          sep acc )
      "" bs
  in
  let str = if str = "" then "" else str ^ ";...;" in
  Printf.sprintf "[%sdefault:=%s]" str (Printing.value_to_string dv)
