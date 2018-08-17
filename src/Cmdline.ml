
type t =
  { debug: bool       [@short "-d"]    (** enable debugging of nv                  *)
  ; verbose: bool     [@short "-v"]    (** print out the policy definition file    *)
  ; simulate: bool    [@short "-s"]    (** simulate the network on real inputs     *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; random_test: bool [@short "-r"]    (** perform randomized network testing      *)
  ; smart_gen: bool   [@short "-g"]    (** generate relevant randomized inputs     *)
  ; smt: bool         [@short "-m"]    (** search for bugs using an smt solver     *)
  ; unroll_maps: bool [@short "-u"]    (** unroll dictionaries into finite values  *)}
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
  ; smart_gen= false
  ; smt= false
  ; unroll_maps= false }
