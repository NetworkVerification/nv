
type t =
  { debug: bool       [@short "-d"]    (** enable a debugging backtrace for nv     *)
  ; verbose: bool     [@short "-v"]    (** print out the srp solution              *)
  ; simulate: bool    [@short "-s"]    (** simulate the network on given inputs    *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; random_test: bool [@short "-r"]    (** perform randomized network testing      *)
  ; ntests: int                        (** number of random test cases to try      *)
  ; smart_gen: bool   [@short "-g"]    (** generate relevant randomized inputs     *)
  ; smt: bool         [@short "-m"]    (** search for bugs using an smt solver     *)
  ; unroll_maps: bool [@short "-u"]    (** try to unroll dictionaries as tuples    *)
  ; hashcons: bool    [@short "-c"]    (** enables hashconsing of all ast terms    *)
  ; memoize: bool     [@short "-z"]    (** memoizes the interpreter for reuse      *)
  ; no_caching: bool                   (** disables mtbdd operation caching        *)
  ; no_cutoff: bool                    (** disables mtbdd early termination        *)
  ; inline: bool      [@short "-i"]    (** inline the policy before simulation     *)
  ; compress: bool                     (** compress the network before simulation  *)
  }
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
  ; hashcons=false
  ; memoize = false
  ; no_caching=false
  ; no_cutoff=false
  ; inline=false
  ; compress=false}

let cfg = ref default 

let get_cfg () = !cfg

let set_cfg c = cfg := c
