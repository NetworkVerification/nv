open Nv_lang.Syntax
open Nv_solution

type 'a mutator = ('a -> 'a) -> 'a -> 'a option
type map_back_mutator = (value -> ty -> value) -> value -> ty -> value option
type mask_mutator = map_back_mutator

val mutate_declarations:
  name:string ->
  ty mutator ->
  pattern mutator ->
  value mutator ->
  exp mutator ->
  map_back_mutator ->
  mask_mutator ->
  declarations ->
  declarations * Solution.map_back

val mutate_network:
  name:string ->
  ty mutator ->
  pattern mutator ->
  value mutator ->
  exp mutator ->
  map_back_mutator ->
  mask_mutator ->
  network ->
  network * Solution.map_back
