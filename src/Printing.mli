(* Printing utilities *)

open Syntax

val op_to_string : op -> string
val value_to_string : value -> string
val exp_to_string : exp -> string
val func_to_string : func -> string
val closure_to_string : closure -> string
val declaration_to_string : declaration -> string
val declarations_to_string : declarations -> string
