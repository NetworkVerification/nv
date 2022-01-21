(*** Option utilities ***)
let oget (x : 'a option) : 'a =
  (* BatOption.get_exn x (failwith "internal error (oget)") *)
  match x with
  | None -> failwith "internal error (oget)"
  | Some y -> y
;;

let omap (f : 'a -> 'b) (x : 'a option) : 'b option =
  (* BatOption.map f x *)
  match x with
  | None -> None
  | Some y -> Some (f y)
;;

let ostring (f : 'a -> string) (x : 'a option) : string =
  match x with
  | None -> "None"
  | Some v -> "Some " ^ f v
;;

(*** Delayed computation ***)
type 'a delayed = unit -> 'a

let dmap (f : 'a -> 'b) (x : 'a delayed) : 'b delayed = fun () -> f (x ())

(*** List Utilities ***)

(** Generate an ascending list of numbers [0,n). *)
let rec list_seq n =
  match n with
  | 0 -> []
  | _ -> if n < 0 then failwith "list_seq: given negative n" else list_seq (n - 1) @ [n - 1]
;;

(** Given a string representing a range of numbers, return a list of all integers in the range.
 ** The string should match the regular expression "(A-B|C)(,A-B|C)*".
 *)
let range_str_to_set s : int BatSet.t =
  let seqs = BatString.split_on_char ',' s in
  let range_to_list rs =
    let (start, stop) = try (BatString.split rs ~by:"-") with
    | Not_found -> (rs, rs)
    in BatList.range (int_of_string start) `To (int_of_string stop)
  in
  (* insert every element into the set *)
  List.fold_left (fun set x -> BatSet.add x set) BatSet.empty (List.flatten (List.map range_to_list seqs))
;;


let rec list_to_string f lst =
  Printf.sprintf "[%s]" @@ BatString.concat ";" @@ List.map f lst
;;

let map2i f lst1 lst2 =
  let rec aux count lst1 lst2 =
    match lst1, lst2 with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 -> f count hd1 hd2 :: aux (count + 1) tl1 tl2
    | _ -> raise (Invalid_argument "map3i: lists have different lengths")
  in
  aux 0 lst1 lst2
;;

let rec map3 f lst1 lst2 lst3 =
  match lst1, lst2, lst3 with
  | [], [], [] -> []
  | hd1 :: tl1, hd2 :: tl2, hd3 :: tl3 -> f hd1 hd2 hd3 :: map3 f tl1 tl2 tl3
  | _ -> raise (Invalid_argument "map3: lists have different lengths")
;;

let map3i f lst1 lst2 lst3 =
  let rec aux count lst1 lst2 lst3 =
    match lst1, lst2, lst3 with
    | [], [], [] -> []
    | hd1 :: tl1, hd2 :: tl2, hd3 :: tl3 ->
      f count hd1 hd2 hd3 :: aux (count + 1) tl1 tl2 tl3
    | _ -> raise (Invalid_argument "map3i: lists have different lengths")
  in
  aux 0 lst1 lst2 lst3
;;

let rec split3 lst =
  match lst with
  | [] -> [], [], []
  | (h1, h2, h3) :: t ->
    let t1, t2, t3 = split3 t in
    h1 :: t1, h2 :: t2, h3 :: t3
;;

let rec combine3 lst1 lst2 lst3 =
  match lst1, lst2, lst3 with
  | [], [], [] -> []
  | hd1 :: tl1, hd2 :: tl2, hd3 :: tl3 -> (hd1, hd2, hd3) :: combine3 tl1 tl2 tl3
  | _ -> raise (Invalid_argument "combine3: lists have different lengths")
;;

let sublist lo hi lst = lst |> BatList.drop lo |> BatList.take (hi - lo + 1)

let replace_sublist lo hi sub full =
  let sub_ref = ref sub in
  let pop () =
    let hd = List.hd !sub_ref in
    sub_ref := List.tl !sub_ref;
    hd
  in
  List.mapi (fun i e -> if i < lo || i > hi then e else pop ()) full
;;

let replaceSlice lo hi ls slice =
  BatList.fold_righti
    (fun i x (vs, acc) ->
      if i >= lo && i <= hi then BatList.tl vs, BatList.hd vs :: acc else vs, x :: acc)
    ls
    (BatList.rev slice, [])
  |> snd
;;

let printList
    (printer : 'a -> string)
    (ls : 'a list)
    (first : string)
    (sep : string)
    (last : string)
  =
  let buf = Buffer.create 500 in
  let rec loop ls =
    match ls with
    | [] -> ()
    | [l] -> Buffer.add_string buf (printer l)
    | l :: ls ->
      Buffer.add_string buf (printer l);
      Buffer.add_string buf sep;
      loop ls
  in
  Buffer.add_string buf first;
  loop ls;
  Buffer.add_string buf last;
  Buffer.contents buf
;;

let printListi
    (printer : int -> 'a -> string)
    (ls : 'a list)
    (first : string)
    (sep : string)
    (last : string)
  =
  let buf = Buffer.create 500 in
  let rec loop i ls =
    match ls with
    | [] -> ()
    | [l] -> Buffer.add_string buf (printer i l)
    | l :: ls ->
      Buffer.add_string buf (printer i l);
      Buffer.add_string buf sep;
      loop (i + 1) ls
  in
  Buffer.add_string buf first;
  loop 0 ls;
  Buffer.add_string buf last;
  Buffer.contents buf
;;
