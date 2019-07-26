open Batteries
open PrimitiveCollections

val print_record : sep:string -> ('a -> string) -> 'a StringMap.t -> string

(* Returns record entries/labels in their canonical order *)
val get_record_labels: 'a StringMap.t -> string list
val get_record_entries: 'a StringMap.t -> 'a list

(* Test if the two maps have the same set of keys *)
val same_labels : 'a StringMap.t -> 'b StringMap.t -> bool

(* Given a label and a list of record types, retrieve the type in
   the list which uses the label. If no such type exists, call the
   error function with an error message *)
val get_type_with_label :
  'a StringMap.t list ->
  (string -> unit) ->
  string ->
  'a StringMap.t
