open Syntax

module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module Memoize (K : Lru_cache.Key) :
  MEMOIZER with type t = K.t =
struct
  module L = Lru_cache.Make (K)

  type t = K.t

  let memoize ~size (f: 'a -> 'b) : 'a -> 'b =
    let map = L.init size in
    fun x ->
      let open Cmdline in
      let cfg = get_cfg () in
      if cfg.hashcons && cfg.memoize then L.get map x f else f x
end

module VKey = struct
  type t = value

  let compare v1 v2 = v1.vtag - v2.vtag

  let witness = vbool true
end

module EKey = struct
  type t = exp

  let compare e1 e2 = e1.etag - e2.etag

  let witness = e_val (vbool true)
end

module MemoizeValue = Memoize (VKey)
module MemoizeExp = Memoize (EKey)
