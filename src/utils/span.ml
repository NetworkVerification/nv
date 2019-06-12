type t = {start: int; finish: int} [@@deriving show, ord]

let extend (x: t) (y: t) : t =
  let s = min x.start y.start in
  let f = max x.finish y.finish in
  {start= s; finish= f}

let default = {start= -1; finish= -1}
