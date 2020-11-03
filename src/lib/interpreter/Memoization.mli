module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module MemoizeValue : MEMOIZER with type t = Nv_lang.Syntax.value
module MemoizeExp : MEMOIZER with type t = Nv_lang.Syntax.exp
