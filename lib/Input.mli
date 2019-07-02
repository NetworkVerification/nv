open Syntax

val read : Lexing.lexbuf -> declarations

val read_from_in : in_channel -> declarations

val read_from_str : string -> declarations

val read_from_file : string -> declarations

val parse : string -> declarations * Console.info
