module T = ANSITerminal

type info

val read_file : string -> info

val error : string -> 'a

val warning : string -> unit

val error_position : info -> Span.t -> string -> 'a

val warning_position : info -> Span.t -> string -> unit

val get_position : int -> info -> int * int

val get_position_opt : int -> info -> (int * int) option

val show_message : string -> T.color -> string -> unit
