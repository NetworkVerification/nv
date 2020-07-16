open Syntax
open Cudd
open Nv_datastructures
open Nv_utils

(* module type BddMapSig (B: BddUtilsSig) =
sig
  val create: key_ty:Syntax.ty -> Syntax.value -> t
  val map: op_key:ExpMap.key -> (Syntax.value -> Syntax.value) -> t -> t
  val map_when: op_key:ExpMap.key -> bool Cudd.Mtbdd.t -> (Syntax.value -> Syntax.value) -> t -> t
  val map_ite: op_key1:ExpMap.key -> op_key2:ExpMap.key -> bool Cudd.Mtbdd.t -> (Nv_lang.Syntax.value -> Nv_lang.Syntax.value) 
            -> (Nv_lang.Syntax.value -> Nv_lang.Syntax.value) -> t -> t
  val find: t -> Nv_lang.Syntax.value -> Nv_lang.Syntax.value
  val update: t -> Nv_lang.Syntax.value -> Nv_lang.Syntax.value -> t *)


(* TODO: optimize variable ordering  *)
type t = mtbdd


module B = BddUtils

let create ~key_ty:ty (v: value) : t =
  B.set_size (B.ty_to_size ty) ;
  (Mtbdd.cst B.mgr B.tbl_nv v, ty)

let rec default_value ty =
  match ty with
  | TUnit -> avalue (vunit (), Some ty, Span.default)
  | TBool -> avalue (vbool false, Some ty, Span.default)
  | TInt size ->
    avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default)
  | TRecord map -> avalue (vtuple (BatList.map default_value @@ RecordUtils.get_record_entries map),
                           Some ty, Span.default)
  | TTuple ts ->
    avalue (vtuple (BatList.map default_value ts), Some ty, Span.default)
  | TOption _ ->
    avalue (voption None, Some ty, Span.default)
  | TMap (ty1, ty2) ->
    avalue (vmap (create ~key_ty:ty1 (default_value ty2)), Some ty, Span.default)
  | TNode -> avalue (vnode 0, Some ty, Span.default)
  | TEdge -> avalue (vedge (0, 1), Some ty, Span.default)
  | TVar {contents= Link t} ->
    default_value t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

let value_to_bdd (v: value) : Bdd.vt =
  let rec aux v idx =
    match v.v with
    | VUnit -> (* Encode unit as if it were a true boolean *)
      Cudd.Bdd.dtrue B.mgr, idx 
    | VBool b ->
      let var = B.ithvar idx in
      ((if b then var else Bdd.dnot var), idx + 1)
    | VInt i ->
      B.mk_int i idx, idx + Integer.size i
    | VTuple vs ->
      let base = Bdd.dtrue B.mgr in
      List.fold_left
        (fun (bdd_acc, idx) v ->
           let bdd, i = aux v idx in
           (Bdd.dand bdd_acc bdd, i) )
        (base, idx) vs
    | VRecord map ->
      (* Convert this to a tuple type, then encode that *)
      let tup = vtuple (RecordUtils.get_record_entries map) in
      aux tup idx
    | VNode n ->
      (* Encode same way as we encode ints *)
      aux (vint (Integer.create ~value:n ~size:tnode_sz)) idx
    | VEdge (e1, e2) ->
      (* Encode same way as we encode tuples of nodes *)
      let tup = vtuple [vnode e1; vnode e2] in
      aux tup idx
    | VOption None ->
      let var = B.ithvar idx in
      let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
      let dv = default_value (Nv_utils.OCamlUtils.oget v.vty) in
      let value, idx = aux dv (idx + 1) in
      (Bdd.dand tag value, idx)
    | VOption (Some dv) ->
      let var = B.ithvar idx in
      let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
      let value, idx = aux dv (idx + 1) in
      (Bdd.dand tag value, idx)
    | VMap _ | VClosure _ ->
      failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux v 0 in
  bdd

(* Treats Top as false *)
let vars_to_value vars ty =
  let open RecordUtils in
  let rec aux idx ty =
    let v, i =
      match get_inner_type ty with
      | TUnit -> vunit (), idx + 1 (* Same as a bool *)
      | TBool ->
        (vbool (B.tbool_to_bool vars.(idx)), idx + 1)
      | TInt size ->
        let acc = ref (Integer.create ~value:0 ~size:size) in
        for i = 0 to size-1 do
          let bit = B.tbool_to_bool vars.(idx + i) in
          if bit then
            let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
            acc := Integer.add !acc add
        done ;
        (vint !acc, idx + size)
      | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
               let v, i = aux idx ty in
               (v :: vs, i) )
            ([], idx) ts
        in
        (vtuple (List.rev vs), i)
      | TRecord map ->
        (* This will have been encoded as if it's a tuple.
           So get the tuple type and use that to decode *)
        let tup = TTuple (get_record_entries map) in
        let vals, i = aux idx tup in
        let vals = match vals with | {v = VTuple vs; _} -> vs | _ -> failwith "impossible" in
        (* Reconstruct the record *)
        let open PrimitiveCollections in
        let recmap =
          List.fold_left2 (fun acc l v -> StringMap.add l v acc)
            StringMap.empty
            (RecordUtils.get_record_labels map)
            vals
        in
        vrecord recmap, i
      | TNode ->
        (* Was encoded as int, so decode same way *)
        (match aux idx (TInt tnode_sz) with
         | {v = VInt n; _}, i ->  vnode (Integer.to_int n), i
         | _ -> failwith "impossible")
      | TEdge ->
        (* Was encoded as tuple of nodes *)
        (match aux idx (TTuple [TNode; TNode]) with
         | {v = VTuple [{v= VNode n1; _}; {v= VNode n2; _}]; _}, i -> vedge (n1, n2), i
         | _ -> failwith "impossible")
      | TOption tyo ->
        let tag = B.tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v =
          if tag then voption (Some v)
          else voption None
        in
        (v, i)
      | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (bdd_to_value)"
    in
    let ty =
      match ty with
      | TRecord map -> TTuple (get_record_entries map)
      | _ -> ty
    in
    (annotv ty v, i)
  in
  fst (aux 0 ty)

let vars_to_values vars ty =
  let open RecordUtils in
  let rec aux idx ty =
    let v, i =
      match get_inner_type ty with
      | TUnit -> vunit (), idx + 1 (* Same as a bool *)
      | TBool ->
        (vbool (B.tbool_to_bool vars.(idx)), idx + 1)
      | TInt size ->
        let acc = ref (Integer.create ~value:0 ~size:size) in
        for i = 0 to size-1 do
          let bit = B.tbool_to_bool vars.(idx + i) in
          if bit then
            let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
            acc := Integer.add !acc add
        done ;
        (vint !acc, idx + size)
      | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
               let v, i = aux idx ty in
               (v :: vs, i) )
            ([], idx) ts
        in
        (vtuple (List.rev vs), i)
      | TRecord map ->
        (* This will have been encoded as if it's a tuple.
           So get the tuple type and use that to decode *)
        let tup = TTuple (get_record_entries map) in
        aux idx tup
      | TNode ->
        (* Was encoded as int, so decode same way *)
        (match aux idx (TInt tnode_sz) with
         | {v = VInt n; _}, i ->  vnode (Integer.to_int n), i
         | _ -> failwith "impossible")
      | TEdge ->
        (* Was encoded as tuple of nodes *)
        (match aux idx (TTuple [TNode; TNode]) with
         | {v = VTuple [{v= VNode n1; _}; {v= VNode n2; _}]; _}, i -> vedge (n1, n2), i
         | _ -> failwith "impossible")
      | TOption tyo ->
        let tag = B.tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v =
          if tag then voption (Some v)
          else voption None
        in
        (v, i)
      | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (bdd_to_value)"
    in
    let ty =
      match ty with
      | TRecord map -> TTuple (get_record_entries map)
      | _ -> ty
    in
    (annotv ty v, i)
  in
  fst (aux 0 ty)

module ExpMap = BatMap.Make (struct
    type t = exp * value BatSet.PSet.t

    let compare = Pervasives.compare
  end)

let map_cache = ref ExpMap.empty

let map ~op_key (f: value -> value) ((vdd, ty): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl_nv in
  if cfg.no_caching then (Mapleaf.mapleaf1 g vdd, ty)
  else
    let op =
      match ExpMap.Exceptionless.find op_key !map_cache with
      | None ->
        let o =
          User.make_op1
            ~memo:(Cudd.Memo.Global)
            (* ~memo:(Memo.Cache (Cache.create1 ~maxsize:4096 ())) *)
            g
        in
        map_cache := ExpMap.add op_key o !map_cache ;
        o
      | Some op -> op
    in
    (User.apply_op1 op vdd, ty)

let pick_default_value (map,ty) =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
       let c = B.count_tops vars (B.ty_to_size ty) in
       if c > !count then count := c ;
       value := Some v )
    map ;
  Nv_utils.OCamlUtils.oget !value

(* Should be deprecated *)
let bindings ((map, ty): t) : (value * value) list * value =
  let bs = ref [] in
  let dv = pick_default_value (map, ty) in
  Mtbdd.iter_cube
    (fun vars v ->
       let lst = Array.to_list vars in
       let sz = B.ty_to_size ty in
       let expanded =
         if B.count_tops vars sz <= 2 then B.expand lst sz else [lst]
       in
       List.iter
         (fun vars ->
            if not (equal_values ~cmp_meta:false v dv) then
              let k = vars_to_value (Array.of_list vars) ty in
              bs := (k, v) :: !bs )
         expanded )
    map ;
  (!bs, dv)

(* Returns a single map entry for each value in a map.
 * Used for printing *)
let bindings_repr ((map, ty): t) : (value * value) list =
  let bs = ref [] in
  let seen = Hashtbl.create 30 in
  Mtbdd.iter_cube_u
    (fun vars v ->
       if not (Hashtbl.mem seen v) then
         begin
           let k = vars_to_value vars ty in
           Hashtbl.add seen v ();
           bs := (k, Mtbdd.get v) :: !bs
         end) map ;
  !bs

module HashValue : (Hashtbl.HashedType with type t = Syntax.value) =
struct
  type t = Syntax.value
  let hash = hash_value ~hash_meta:false
  let equal = equal_values ~cmp_meta:false
end

module HashTblValue : (Hashtbl.S with type key = Syntax.value) = Hashtbl.Make(HashValue)

let bindings_all ((map, ty): t) : (value * value) list =
  let bs = ref [] in
  let seen = HashTblValue.create 30 in
  Mtbdd.iter_cube
    (fun vars v ->
       if not (HashTblValue.mem seen v) then
         begin
           HashTblValue.add seen v ();
           let lst = Array.to_list vars in
           let sz = B.ty_to_size ty in
           let expanded =
             if B.count_tops vars sz <= 2 then B.expand lst sz else [lst]
           in
           List.iter
             (fun vars ->
                let k = vars_to_value (Array.of_list vars) ty in
                bs := (k, v) :: !bs )
             expanded
         end)
    map ;
  !bs


let mapw_op_cache = ref ExpMap.empty

let map_when ~op_key (pred: bool Mtbdd.t) (f: value -> value)
    ((vdd, ty): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl_nv
    else v
  in
  if cfg.no_caching then (Mapleaf.mapleaf2 g pred vdd, ty)
  else
    let op =
      match ExpMap.Exceptionless.find op_key !mapw_op_cache with
      | None ->
        let special =
          if cfg.no_cutoff then fun _ _ -> None
          else fun bdd1 bdd2 ->
            if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
            then Some bdd2
            else None
        in
        let op =
          User.make_op2
            ~memo:(Cudd.Memo.Global)
            (* ~memo:(Memo.Cache (Cache.create2 ~maxsize:8000 ())) *)
            ~commutative:false ~idempotent:false ~special g
        in
        mapw_op_cache := ExpMap.add op_key op !mapw_op_cache ;
        op
      | Some op ->
        op
    in
    (User.apply_op2 op pred vdd, ty)

let mapite_op_cache = ref ExpMap.empty

(* For map_ite we have two operations hence we maintain a map from expressions to another map for the cache *)
let map_ite ~op_key1 ~op_key2 (pred: bool Mtbdd.t) (f1: value -> value) (f2: value -> value)
    ((vdd, ty): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f1 (Mtbdd.get v) |> Mtbdd.unique B.tbl_nv
    else f2 (Mtbdd.get v) |> Mtbdd.unique B.tbl_nv
  in
  if cfg.no_caching then (Mapleaf.mapleaf2 g pred vdd, ty)
  else
    let op =
      match ExpMap.Exceptionless.find op_key1 !mapite_op_cache with
      | None ->
        let op =
          User.make_op2
            ~memo:(Cudd.Memo.Global)
            (* ~memo:(Memo.Cache (Cache.create2 ())) *)
            ~commutative:false ~idempotent:false g
        in
        let newMap = ExpMap.singleton op_key2 op in
        mapite_op_cache := ExpMap.add op_key1 newMap !mapite_op_cache ;
        op
      | Some map2 ->
        (match ExpMap.Exceptionless.find op_key2 map2 with
         | None ->
           let op =
             User.make_op2
               ~memo:(Cudd.Memo.Global)
               (* ~memo:(Memo.Cache (Cache.create2 ())) *)
               ~commutative:false ~idempotent:false g
           in
           mapite_op_cache := ExpMap.modify op_key1 (fun map2 -> ExpMap.add op_key2 op map2) !mapite_op_cache ;
           op
         | Some op -> op)
    in
    (User.apply_op2 op pred vdd, ty)


(* Cache for map forall expressions *)
let forall_op_cache = ref ExpMap.empty

let forall ~op_key (pred: bool Mtbdd.t) (f: value -> value) ((vdd, _): t) : value =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl_nv
    else vbool true |> Mtbdd.unique B.tbl_nv
  in
    let op =
      match ExpMap.Exceptionless.find op_key !forall_op_cache with
      | None ->
        let special =
          if cfg.no_cutoff then fun _ _ -> None
          else fun bdd1 _ ->
            if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
            then Some (Mtbdd.cst B.mgr B.tbl_nv (vbool true))
            else None
        in
        let op =
          User.make_op2
            ~memo:(Cudd.Memo.Global)
            (* ~memo:(Memo.Cache (Cache.create2 ~maxsize:4096 ())) *)
            ~commutative:false ~idempotent:false ~special g
        in
        forall_op_cache := ExpMap.add op_key op !forall_op_cache ;
        op
      | Some op ->
        op
    in
    let op_result = User.apply_op2 op pred vdd in
    Array.fold_left (fun acc v -> (match v.v with | VBool b -> (b && acc) | _ -> failwith "Mistyped map")) true
      (Mtbdd.leaves op_result) |> vbool

module MergeMap = BatMap.Make (struct
    type t =
      (exp * value BatSet.PSet.t) * (value * value * value * value) option

    let compare = Pervasives.compare
  end)

let unwrap x =
  match x with
  | {v= VOption (Some v)} ->
    (true, v)
  | _ -> (false, vbool false)

let merge_op_cache = ref MergeMap.empty

let merge ?opt ~op_key (f: value -> value -> value) ((x, tyx): t)
    ((y, _): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g x y =
    f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl_nv
  in
  if cfg.no_caching then (Mapleaf.mapleaf2 g x y, tyx)
  else
    let key = (op_key, opt) in
    let op =
      match MergeMap.Exceptionless.find key !merge_op_cache with
      | None ->
        let special =
          match (opt, cfg.no_cutoff) with
          | None, _ | _, true -> fun _ _ -> None
          | Some (el0, el1, er0, er1), false ->
            let bl0, vl0 = unwrap el0 in
            let bl1, vl1 = unwrap el1 in
            let br0, vr0 = unwrap er0 in
            let br1, vr1 = unwrap er1 in
            fun left right ->
              if
                bl0 && Vdd.is_cst left
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval left))
                  vl0
              then Some right
              else if
                bl1 && Vdd.is_cst left
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval left))
                  vl1
              then Some left
              else if
                br0 && Vdd.is_cst right
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval right))
                  vr0
              then Some left
              else if
                br1 && Vdd.is_cst right
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval right))
                  vr1
              then Some right
              else None
        in
        let o = User.make_op2
            ~memo:(Cudd.Memo.Global)
            ~commutative:false ~idempotent:false ~special g
            (* User.make_op2
             *   ~memo:(Memo.Cache (Cache.create2 ~maxsize:4096 ()))
             *   ~commutative:false ~idempotent:false ~special g *)
        in
        merge_op_cache := MergeMap.add key o !merge_op_cache ;
        o
      | Some op -> op
    in
    (User.apply_op2 op x y, tyx)

let find ((map, _): t) (v: value) : value =
  let bdd = value_to_bdd v in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update ((map, ty): t) (k: value) (v: value) : t =
  let leaf = Mtbdd.cst B.mgr B.tbl_nv v in
  let key = value_to_bdd k in
  (Mtbdd.ite key leaf map, ty)

let from_bindings ~key_ty:ty
    ((bs, default): (value * value) list * value) : t =
  let map = create ~key_ty:ty default in
  List.fold_left (fun acc (k, v) -> update acc k v) map bs

let equal (bm1, _) (bm2, _) = Mtbdd.is_equal bm1 bm2


(** * Printing BDD values*)

(** Type of multivalues*)
type multiValue =
  | MUnit
  | MBool of bool option (* Booleans are either true, false, or "Top" *)
  | MInt of ((Integer.t * Integer.t) list) (* Integers are represented as ranges *)
  | MBit of (bool option) array
  | MOption of (bool option * multiValue)
  | MTuple of multiValue list (* Tuple of elements *)
  | MNode of (bool option) array
  | MEdge of (bool option) array * (bool option) array

let splitArray vars i j elt =
  Array.init (Array.length vars)
    (fun k -> if k >= i && k <= j then elt else vars.(k))

let rec bintRange i vars acc =
  let sz = Array.length vars in
  if i = sz then acc
  else
    match vars.(i) with
    | Man.True | Man.False ->
      bintRange (i+1) vars acc
    | Man.Top ->
      ((* let j = ref (i-1) in
        * while (!j < (sz - 1)) && (vars.(!j+1) = Man.Top) do
        *   incr j
        * done; *)
        bintRange (i+1) vars
          ((List.map
              (fun arr -> (splitArray arr i i Man.False) ::
                          [splitArray arr i i Man.True]) acc)
           |> List.concat))

let int_of_bint vars =
  let size = Array.length vars in
  let acc = ref (Integer.create ~value:0 ~size:size) in
  for i = 0 to size-1 do (*LSB is in array index 0*)
    let bit = B.tbool_to_bool vars.(i) in
    if bit then
      let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
      acc := Integer.add !acc add
  done ;
  !acc


let createRanges i vars =
  let rec aux acc =
    match acc with
    | [] -> []
    | [x] -> let x = int_of_bint x in [(x,x)]
    | x :: y :: acc ->
      (int_of_bint x, int_of_bint y) :: (aux acc)
  in
  aux (bintRange i vars [vars])

let vars_to_multivalue vars ty =
  let open RecordUtils in
  let rec aux idx ty =
    let v, i =
      match get_inner_type ty with
      | TUnit -> MUnit, idx + 1
      | TBool ->
        MBool (B.tbool_to_obool vars.(idx)), idx + 1
      | TInt size ->
        let arr = Array.init (size) (fun i -> vars.(idx + size - 1 - i)) in
        MBit (Array.map (fun b -> B.tbool_to_obool b) arr), idx + size
      (* let arr = Array.init (size) (fun i -> vars.(idx + i)) in
       * let ranges = createRanges 0 arr in
       * MInt ranges, idx + size *)
      | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
               let v, i = aux idx ty in
               (v :: vs, i) )
            ([], idx) ts
        in
        (MTuple (List.rev vs), i)
      | TRecord map ->
        (* This will have been encoded as if it's a tuple.
           So get the tuple type and use that to decode *)
        let tup = TTuple (get_record_entries map) in
        aux idx tup
      | TNode ->
        (* Was encoded as int, so decode same way *)
        (match aux idx (TInt tnode_sz) with
         (* | MInt rs, i ->  MNode rs, i *)
         | MBit rs, i -> MNode rs, i
         | _ -> failwith "impossible")
      | TEdge ->
        (* Was encoded as tuple of nodes *)
        (match aux idx (TTuple [TNode; TNode]) with
         (* | MTuple [MInt r1; MInt r2], i -> MEdge (r1, r2), i *)
         | MTuple [MBit r1; MBit r2], i -> MEdge (r1, r2), i
         | _ -> failwith "impossible")
      | TOption tyo ->
        let tag = B.tbool_to_obool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        MOption (tag, v), i
      | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (bdd_to_value)"
    in
    (v, i)
  in
  fst (aux 0 ty)

let bindingsExact ((map, ty): t) : (multiValue * value) list =
  let bs = ref [] in
  Mtbdd.iter_cube
    (fun vars v ->
       let k = vars_to_multivalue vars ty in
       bs := (k, v) :: !bs )
    map ;
  !bs

let rec multiValue_to_string (mv : multiValue) =
  match mv with
  | MUnit -> "()"
  | MBool o -> (match o with | None -> "T" | Some b -> Printf.sprintf "%b" b)
  | MInt rs ->
    PrimitiveCollections.printList (fun (a,b) -> Printf.sprintf "[%s, %s]" (Integer.to_string a) (Integer.to_string b)) rs "{" "," "}"
  | MBit bs ->
    String.init (Array.length bs) (fun i -> match bs.(i) with | None -> '*' | Some true -> '1' | Some false -> '0')
  | MOption (tag, v) ->
    (match tag with
     | None -> Printf.sprintf "OptionT (%s)" (multiValue_to_string v)
     | Some true -> Printf.sprintf "Some (%s)" (multiValue_to_string v)
     | Some false -> Printf.sprintf "None")
  | MTuple ts ->
    PrimitiveCollections.printList multiValue_to_string ts "[" "; " "]"
  | MNode rs ->
    Printf.sprintf "%sn" (multiValue_to_string (MBit rs))
  | MEdge _ ->
    failwith "Todo printing of edges"

(* Very dangerous! Changes the bdd to think it has keys of the given type.
   This will cause everything to break unless the new type uses exactly the
   same encoding as the original type, in which case this will only affect
   printing. *)
let change_key_type ty (map, _) = (map, ty)

(*
let splitArray vars i j elt =
  Array.init (Array.length vars)
    (fun k -> if k >= i && k <= j then elt else vars.(k))

let rec bintRange i vars acc =
  let sz = Array.length vars in
  if i = sz then acc
  else
    match vars.(i) with
    | Some true | Some false ->
      bintRange (i+1) vars acc
    | None ->
      (bintRange (i+1) vars
         ((List.map
            (fun arr -> (splitArray arr i i (Some false)) ::
                        [splitArray arr i i (Some true)]) acc)
          |> List.concat))

let int_of_bint vars =
  let size = Array.length vars in
  let acc = ref 0 in
  for i = size-1 downto 0 do
    let bit = match vars.(i) with | None | Some false -> false | Some true -> true in
    if bit then
      let add = 1 lsl (size-1-i) in
      acc := !acc + add
  done ;
  !acc

let createRanges i vars =
  let rec aux acc =
    match acc with
    | [] -> []
    | [x] -> let x = int_of_bint x in [(x,x)]
    | x :: y :: acc ->
      (int_of_bint x, int_of_bint y) :: (aux acc)
  in
  aux (bintRange i vars [vars])
*)
