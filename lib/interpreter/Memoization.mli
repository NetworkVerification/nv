module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module MemoizeValue : MEMOIZER with type t = Syntax.value

module MemoizeExp : MEMOIZER with type t = Syntax.exp
