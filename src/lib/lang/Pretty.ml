(* Pretty printing utilities.
 * Based on Phil Wadler's pretty printing paper,
 * https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf *)
open Batteries
open Syntax

type doc =
  | Nil
  | Text of string * doc
  | Line of int * doc

let rec layout = function
  | Nil -> ""
  | Text (s, x) -> s ^ layout x
  | Line (i, x) -> "\n" ^ String.make i ' ' ^ layout x
;;

type layouts =
  | LNil
  (* concatenation of documents *)
  | LCat of layouts * layouts
  | LNest of int * layouts
  | LText of string
  | LLine
  (* union of documents: multiple possible layouts *)
  | LUnion of layouts * layouts

let nil = LNil
let cat d1 d2 = LCat (d1, d2)
let nest i d = LNest (i, d)
let text s = LText s
let line = LLine
let union d1 d2 = LUnion (d1, d2)

let rec group doc = union (flatten doc) doc

and flatten = function
  | LNil -> LNil
  | LCat (d1, d2) -> LCat (flatten d1, flatten d2)
  | LNest (i, d) -> flatten d
  | LText s -> LText s
  | LLine -> LText " "
  | LUnion (d1, d2) -> flatten d1
;;

let rep z = List.fold_left cat nil (List.map (fun (i, d) -> nest i d) z)

let rec be w k : (int * layouts) list -> doc = function
  | [] -> Nil
  | (i, d) :: z ->
    (match d with
    | LNil -> be w k z
    | LCat (d1, d2) -> be w k ((i, d1) :: (i, d2) :: z)
    | LNest (j, d) -> be w k ((i + j, d) :: z)
    | LText s -> Text (s, be w (k + String.length s) z)
    | LLine -> Line (i, be w i z)
    | LUnion (d1, d2) -> better w k (be w k ((i, d1) :: z)) (be w k ((i, d2) :: z)))

and better w k (x : doc) (y : doc) = if fits (w - k) x then x else y

and fits w (x : doc) =
  if w < 0
  then false
  else (
    match x with
    | Text (s, x) -> fits (w - String.length s) x
    | _ -> true)
;;

(* [best w k x] determines the best layout among a set given width w and
 * number of already-placed characters k, i.e. it takes a document with
 * unions and produces one without. *)
let best w k x : doc = be w k [0, x]

(* [pretty w x] determines the pretty-printed version of the given document. *)
let pretty w x = layout (best w 0 x)
let space d1 d2 = cat d1 (cat (text " ") d2)
let lb d1 d2 = cat d1 (cat line d2)

let rec folddoc f = function
  | [] -> nil
  | [x] -> x
  | h :: t -> f h (folddoc f t)
;;

let spread = folddoc space
let stack = folddoc lb
let bracket l x r = group (cat (text l) (cat (nest 2 (cat line x)) (cat line (text r))))
let space_lb d1 d2 = cat d1 (cat (union (text " ") line) d2)

let rec fill = function
  | [] -> nil
  | [x] -> x
  | x :: y :: zs ->
    union (space (flatten x) (fill (flatten y :: zs))) (lb x (fill (y :: zs)))
;;
