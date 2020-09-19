module T = ANSITerminal

exception Error of string

type info

val read_files : string list -> info
val error : string -> 'a
val warning : string -> unit
val show_message : string -> T.color -> string -> unit
val error_position : info -> Nv_datastructures.Span.t -> string -> 'a
val warning_position : info -> Nv_datastructures.Span.t -> string -> unit
val get_start_position : Nv_datastructures.Span.t -> info -> (int * int) option
val get_end_position : Nv_datastructures.Span.t -> info -> (int * int) option
