type t =
  { verbose : bool [@short "-v"] (** print the srp topology info              *)
  ; simulate : bool [@short "-s"] (** simulate the network to produce a cut    *)
  }
[@@deriving
  show
  , argparse
      { positional = ["file", "nv policy file"]
      ; description = "nv: a network verification framework"
      }]

let default = { verbose = false; simulate = false }
let cfg = ref default
let get_cfg () = !cfg
let set_cfg c = cfg := c
