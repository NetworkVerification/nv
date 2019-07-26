val default_value : Syntax.ty -> Syntax.value

val default_value_exp : Syntax.ty -> Syntax.exp

val random_value :
  hints:Collections.ValueSet.t Collections.TypeMap.t -> max_map_size:int -> Syntax.ty -> Syntax.value

val random_symbolics :
     ?hints:Collections.ValueSet.t Collections.TypeMap.t
  -> ?max_map_size:int
  -> Syntax.network
  -> Syntax.network
