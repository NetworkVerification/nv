open Nv_lang
open Nv_datastructures
open Nv_lang.Syntax

type predicate =
  | True
  | Custom of string
[@@deriving show]

let parse_predicate = function
  | "true" -> True
  | s -> Custom s
;;

let predicate_to_exp p =
  let body =
    match p with
    | True -> ebool true
    | Custom s -> Parser.expreof Lexer.token (Lexing.from_string s)
  in
  efun (func (Var.create "x") body)
;;

type t =
  { verbose : bool [@short "-v"] (** print the srp topology info              *)
  ; simulate : bool [@short "-s"] (** simulate the network to produce a cut    *)
  ; leak : bool [@short "-l"] (** leak the route when performing a hijack     *)
  ; destination : int [@short "-d"] (** destination node for cuts and hijacks *)
  ; nfaults : int [@short "-f"] (** number of failures to consider *)
  ; predicate : predicate [@short "-p"] [@parse parse_predicate]
        (** predicate to use for cuts and hijacks: references should be in terms of a variable "x" *)
  ; topology : string option [@short "-t"] (** type of topology to generate    *)
  ; outfile : string [@short "-o"] (** file to output NV program to; '-' for stdout *)
  }
[@@deriving
  show
  , argparse
      { positional =
          ["file", "nv policy file"; "operation", "one of 'topology', 'ft', 'maintenance', 'notrans', 'cut' or 'hijack'"]
      ; description = "nv: a network verification framework"
      }]

let default =
  { verbose = false
  ; simulate = false
  ; leak = false
  ; destination = -1
  ; predicate = True
  ; nfaults = 0
  ; topology = None
  ; outfile = "-"
  }
;;

let cfg = ref default
let get_cfg () = !cfg
let set_cfg c = cfg := c
