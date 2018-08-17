type info = {input: string array; linenums: (int * int) array}

val error : string -> 'a

val warning : string -> unit

val error_position : info -> Span.t -> string -> 'a

val warning_position : info -> Span.t -> string -> unit
