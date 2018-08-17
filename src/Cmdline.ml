
type t =
  { debug: bool       [@short "-d"]    (** enable debugging of nv                  *)
  ; verbose: bool     [@short "-v"]    (** print out the policy definition file    *)
  ; simulate: bool    [@short "-s"]    (** simulate the network on given inputs    *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; random_test: bool [@short "-r"]    (** perform randomized network testing      *)
  ; ntests: int                        (** number of random test cases to try      *)
  ; smart_gen: bool   [@short "-g"]    (** generate relevant randomized inputs     *)
  ; smt: bool         [@short "-m"]    (** search for bugs using an smt solver     *)
  ; unroll_maps: bool [@short "-u"]    (** unroll dictionaries into finite values  *)
  ; no_caching: bool                   (** disables mtbdd operation caching        *)}
[@@deriving
  show
  , argparse
      { positional= [("file", "nv policy file")]
      ; description= "nv: a network verification framework" }]

let default =
  { debug= false
  ; verbose= false
  ; simulate= false
  ; bound= None
  ; random_test= false
  ; ntests = 100
  ; smart_gen= false
  ; smt= false
  ; unroll_maps= false
  ; no_caching=false }

let cfg = ref default 

let get_cfg () = !cfg

let set_cfg c = cfg := c