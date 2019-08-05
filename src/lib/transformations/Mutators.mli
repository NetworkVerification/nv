open Nv_lang.Syntax
open Nv_solution

type 'a mutator = 'a -> 'a option
type map_back_mutator = value -> ty -> value option
type mask_mutator = value -> ty -> value

val mutate_declarations:
  ty mutator ->
  pattern mutator ->
  value mutator ->
  exp mutator ->
  map_back_mutator ->
  mask_mutator ->
  (declarations -> declarations * (Solution.t -> Solution.t))

val mutate_network:
  ty mutator ->
  pattern mutator ->
  value mutator ->
  exp mutator ->
  map_back_mutator ->
  mask_mutator ->
  (network -> network * (Solution.t -> Solution.t))
