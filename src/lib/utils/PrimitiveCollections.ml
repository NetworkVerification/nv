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

  module Make (K : KeyType) : (S with type key = K.t) = struct
    include Map.Make(K)

    let to_string f t =
      let output = BatIO.output_string () in
      print
        (fun out k -> Printf.fprintf out "%s" (K.to_string k))
        (fun out v -> Printf.fprintf out "%s" (f v))
        output t;
      BatIO.close_out output
  end
end
;;

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

  module Make (E : EltType) : (S with type elt = E.t) = struct
    include Set.Make(E)

    let to_string t =
      let output = BatIO.output_string () in
      print
        (fun out e -> Printf.fprintf out "%s" (E.to_string e))
        output t;
      BatIO.close_out output
  end
end
;;

module IntMap = BetterMap.Make(Int)
module IntSet = BetterSet.Make(Int)

module StringMap = BetterMap.Make (struct
    type t = string
    let compare = compare
    let to_string x = x
  end)

module StringSet = BetterSet.Make (struct
    include String
    let to_string x = x
  end)

module StringSetSet = BetterSet.Make(StringSet)
