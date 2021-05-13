type t =
  { verbose : bool [@short "-v"] (** print the srp topology info              *)
  ; simulate : bool [@short "-s"] (** simulate the network to produce a cut    *)
  ; leak : bool [@short "-l"] (** leak the route when performing a hijack     *)
  }
[@@deriving
  show
  , argparse
      { positional =
          ["file", "nv policy file"; "operation", "one of 'notrans', 'cut' or 'hijack'"]
      ; description = "nv: a network verification framework"
      }]

let default = { verbose = false; simulate = false; leak = false }
let cfg = ref default
let get_cfg () = !cfg
let set_cfg c = cfg := c
