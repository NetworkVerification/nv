open Syntax

val read : ?filename:string option -> Lexing.lexbuf -> declarations

val read_from_in : in_channel -> declarations

val read_from_str : string -> declarations

val read_from_file : string -> declarations

val parse : string -> declarations * Console.info
