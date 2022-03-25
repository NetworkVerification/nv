type t =
  { debug : bool [@short "-d"] (** enable a debugging backtrace for nv     *)
  ; verbose : bool [@short "-v"] (** print out the srp solution              *)
  ; simulate : bool [@short "-s"] (** simulate the network on given inputs    *)
  ; bound : int option (** bound the number of simulation steps    *)
  ; smt : bool [@short "-m"] (** search for bugs using an smt solver     *)
  ; query : bool (** emit the query used by the smt solver   *)
  ; unbox : bool (** unboxes options and flattens tuples     *)
  ; hiding : bool (** Use the hiding abstraction during SMT solving *)
  ; smt_parallel : bool (** use parallel smt/sat solving*)
  ; finite_arith : bool (** set to false to use finite arithmetic in SMT *)
  ; hashcons : bool [@short "-c"] (** enables hashconsing of all ast terms    *)
  ; memoize : bool [@short "-z"] (** memoizes the interpreter for reuse      *)
  ; no_caching : bool (** disables mtbdd operation caching        *)
  ; no_cutoff : bool (** disables mtbdd early termination        *)
  ; inline : bool [@short "-i"] (** inline the policy before simulation     *)
  ; compile : bool (** compile network to OCaml code before simulation *)
  ; unroll : bool (** whether to unroll maps or not           *)
  ; kirigami : bool [@short "-k"] (** enable partitioning features           *)
  ; ranked : bool (** use the ranked check for kirigami       *)
  ; print_partitions : bool (** print the partitioned declarations in kirigami *)
  ; fragments : string option [@short "-f"] (** only check the given fragments *)
  ; parallelize : int option [@short "-p"] (** Try to parallelize solving using n cores **)
  ; timeout : int [@short "-t"] (** Time out Z3 solving after n seconds (UNIX only) **)
  }
[@@deriving
  show
  , argparse
      { positional = ["file", "nv policy file"]
      ; description = "nv: a network verification framework"
      }]

let default =
  { debug = false
  ; verbose = false
  ; simulate = false
  ; bound = None
  ; smt = false
  ; smt_parallel = false
  ; query = false
  ; hashcons = false
  ; memoize = false
  ; no_caching = false
  ; no_cutoff = false
  ; inline = false
  ; compile = false
  ; unroll = false
  ; unbox = false
  ; finite_arith = false
  ; hiding = false
  ; kirigami = false
  ; ranked = false
  ; print_partitions = false
  ; fragments = None
  ; parallelize = None
  ; timeout = 0
  }
;;

let cfg = ref default
let get_cfg () = !cfg
let set_cfg c = cfg := c

(* Some of our flags only make sense if we have other ones -- for example,
   we can't do map unrolling unless we also do inlining. Make sure all the
   appropriate flags are set, so we don't have to check for lots of different
   variables at the site of each transformation *)
let update_cfg_dependencies () =
  if !cfg.smt then cfg := { !cfg with unroll = true; unbox = true; inline = true };
  if !cfg.unroll then cfg := { !cfg with inline = true };
  if !cfg.hiding then cfg := { !cfg with unbox = true };
  if !cfg.smt_parallel then cfg := { !cfg with finite_arith = true };
  if !cfg.print_partitions || !cfg.ranked then cfg := { !cfg with kirigami = true };
  ()
;;
