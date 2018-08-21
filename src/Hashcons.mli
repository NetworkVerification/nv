(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)
(* This is a modified version of Jean-Christophe Filliatre's hashconsing library  *)

type ('a, 'b) meta =
  { hash: 'a -> int
  ; equal: 'a -> 'a -> bool
  ; node: 'b -> 'a
  ; make: tag:int -> hkey:int -> 'a -> 'b
  ; hkey: 'b -> int }

type ('a, 'b) table

val create : ('a, 'b) meta -> int -> ('a, 'b) table

val clear : ('a, 'b) table -> unit

val hashcons : ('a, 'b) table -> 'a -> 'b

val iter : ('b -> unit) -> ('a, 'b) table -> unit

val stats : ('a, 'b) table -> int * int * int * int * int * int
