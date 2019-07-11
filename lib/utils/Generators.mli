val default_value : Nv_lang.Syntax.ty -> value

val random_value :
  hints:ValueSet.t Nv_lang.Collections.TypeMap.t -> max_map_size:int -> ty -> value

val random_symbolics :
     ?hints:ValueSet.t Nv_lang.Collections.TypeMap.t
  -> ?max_map_size:int
  -> network
  -> network
