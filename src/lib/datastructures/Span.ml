type t = {fname: string; start: int; finish: int} [@@deriving show, ord]

let extend (x: t) (y: t) : t =
  assert (x.fname = y.fname);
  let s = min x.start y.start in
  let f = max x.finish y.finish in
  {x with start= s; finish= f}

let default = {fname = ""; start= -1; finish= -1}

let show_span (span: t) =
  Printf.sprintf "%s:(%d,%d)" span.fname span.start span.finish
