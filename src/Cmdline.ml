
type t =
  { debug: bool       [@short "-d"]    (** enable a debugging backtrace for nv     *)
  ; verbose: bool     [@short "-v"]    (** print out the policy definition file    *)
  ; simulate: bool    [@short "-s"]    (** simulate the network on given inputs    *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; random_test: bool [@short "-r"]    (** perform randomized network testing      *)
  ; ntests: int                        (** number of random test cases to try      *)
  ; smart_gen: bool   [@short "-g"]    (** generate relevant randomized inputs     *)
  ; smt: bool         [@short "-m"]    (** search for bugs using an smt solver     *)
  ; unroll_maps: bool [@short "-u"]    (** try to unroll dictionaries as tuples    *)
  ; no_hashcons: bool                  (** disables hashconsing of ast terms       *)
  ; no_caching: bool                   (** disables mtbdd operation caching        *)
  ; no_cutoff: bool                    (** disables mtbdd early termination        *)}
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
  ; no_hashcons=false
  ; no_caching=false
  ; no_cutoff=false }

let cfg = ref default 

let get_cfg () = !cfg

let set_cfg c = cfg := c