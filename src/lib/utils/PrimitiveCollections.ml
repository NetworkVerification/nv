open Batteries

(* Extends BatMap with an easier-to-use printing function. Can also be further
   extended if we see a need for it *)
module BetterMap = struct
  module type KeyType = sig
    type t

    val compare : t -> t -> int
    val to_string : t -> string
  end

  module type S = sig
    include Map.S

    val to_string : ('a -> string) -> 'a t -> string
  end

  module Make (K : KeyType) : S with type key = K.t = struct
    include Map.Make (K)

    let to_string f t =
      let output = BatIO.output_string () in
      print
        (fun out k -> Printf.fprintf out "%s" (K.to_string k))
        (fun out v -> Printf.fprintf out "%s" (f v))
        output
        t;
      BatIO.close_out output
    ;;
  end
end

(* As above, but for BatSet *)
module BetterSet = struct
  module type EltType = sig
    type t

    val compare : t -> t -> int
    val to_string : t -> string
  end

  module type S = sig
    include Set.S

    val to_string : t -> string
  end

  module Make (E : EltType) : S with type elt = E.t = struct
    include Set.Make (E)

    let to_string t =
      let output = BatIO.output_string () in
      print (fun out e -> Printf.fprintf out "%s" (E.to_string e)) output t;
      BatIO.close_out output
    ;;
  end
end

module IntMap = BetterMap.Make (Int)
module IntSet = BetterSet.Make (Int)

module StringMap = BetterMap.Make (struct
  type t = string

  let compare = compare
  let to_string x = x
end)

module StringSet = BetterSet.Make (struct
  include String

  let to_string x = x
end)

module StringSetSet = BetterSet.Make (StringSet)

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

module type ArrayIdSig = sig
  (** The type of elements cached *)
  type elt

  type t

  (** Create an id store *)
  val create : unit -> t

  (** [fresh_id store e] takes as input an id store, and an element and returns a unique identifier for it. *)
  val fresh_id : t -> elt -> int

  (** Once the store is sealed we can perform constant-time lookups using the identifiers*)
  val seal : t -> unit

  val get_elt : t -> int -> elt
  val get_id : t -> elt -> int
  val to_array : t -> elt BatArray.t
end

module ArrayIdMake (M : BatMap.S) : ArrayIdSig with type elt = M.key = struct
  type elt = M.key

  type t =
    { mutable id : int
    ; mutable cache : int M.t
    ; mutable arr : elt Array.t
    }

  let create () : t = { id = 0; cache = M.empty; arr = [||] }

  let fresh_id m =
    let x = m.id in
    m.id <- m.id + 1;
    x
  ;;

  let fresh_id m elt =
    match M.Exceptionless.find elt m.cache with
    | None ->
      let new_id = fresh_id m in
      m.cache <- M.add elt new_id m.cache;
      new_id
    | Some id -> id
  ;;

  let get_id m e = M.find e m.cache

  let seal m =
    if m.id > 0
    then begin
      let arr = BatArray.create m.id (fst (M.any m.cache)) in
      M.iter (fun elt elt_id -> arr.(elt_id) <- elt) m.cache;
      m.arr <- arr
    end
  ;;

  let get_elt m i = m.arr.(i)
  let to_array m = m.arr
end
