open Nv_lang.Syntax
open Nv_solution

type recursors = {
  recurse_ty: ty -> ty;
  recurse_pattern: pattern -> ty -> pattern;
  recurse_value: value -> value;
  recurse_exp: exp -> exp;
}

type 'a mutator = recursors -> 'a -> 'a option
type pattern_mutator = recursors -> pattern -> ty -> pattern option
type map_back_mutator = (value -> ty -> value) -> value -> ty -> value option
type mask_mutator = map_back_mutator

type 'a toplevel_mutator =
  name:string ->
  ty mutator ->
  pattern_mutator ->
  value mutator ->
  exp mutator ->
  map_back_mutator ->
  mask_mutator ->
  'a ->
  'a * Solution.map_back

val mutate_declarations: declarations toplevel_mutator
val mutate_network: network toplevel_mutator
val mutate_srp: srp_unfold toplevel_mutator
