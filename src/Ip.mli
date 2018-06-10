(* ipv4 *)
type ip

(* ipv4 prefix *)
type ipprefix

(* create bits *)
val ip_from_bits : bool list -> ip
val ip_to_bits : ip -> bool list

(* int32 is signed so we use int64 *)
val ip_from_int : int64 -> ip
val ip_to_int : ip -> int64

(* bits *)
val get_bit : int -> ip -> bool
val set_bit : ip -> int -> bool -> ip

(* comparisons *)
val ip_equals : ip -> ip -> bool
val ip_compare : ip -> ip -> int
  
(* returns 0 bits for wildcards *)
val get_network_addr : ipprefix -> ip
val get_prefix_length : ipprefix -> int

(* lower and upper bounds on the ips *)
val ip_range : ipprefix -> ip * ip

(* comparisons *)
val ipprefix_equals : ip -> ip -> bool
val ipprefix_compare : ip -> ip -> int

val parse : string -> ip option
val print : ip -> string

  
