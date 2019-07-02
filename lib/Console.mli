module T = ANSITerminal

type info

val read_files : string list -> info

val error : string -> 'a

val warning : string -> unit

val show_message : string -> T.color -> string -> unit

val error_position : info -> Span.t -> string -> 'a

val warning_position : info -> Span.t -> string -> unit

val get_start_position : Span.t -> info -> (int * int) option

val get_end_position : Span.t -> info -> (int * int) option
