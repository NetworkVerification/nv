open Collections
open Syntax

val random_value :
  hints:ValueSet.t TypeMap.t -> max_map_size:int -> ty -> value

val random_symbolics :
     ?hints:ValueSet.t TypeMap.t
  -> ?max_map_size:int
  -> network
  -> network
