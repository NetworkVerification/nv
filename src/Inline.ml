open Syntax

(* 
let a = 4 in
let x = if y then fun z -> z + 1 else fun z -> z + 2 in 
let y = x a in
let z = y + 4

let a = 4 in
let x = if y then fun z -> z + 1 else fun z -> z + 2 in 
let y = (if y then fun z -> z + 1 else fun z -> z + 2) a in
let z = y + 4

let a = 4 in
let x = if y then fun z -> z + 1 else fun z -> z + 2 in 
let y = (if y then (fun z -> z + 1) a else (fun z -> z + 2) a ) in
let z = y + 4

let a = 4 in
let x = if y then fun z -> z + 1 else fun z -> z + 2 in 
let y = (if y then a+1 else a+2) in
let z = y + 4

we should also delete x afterwards because it has a function type
*)

let inline_exp (env : exp Env.t) aty (e : exp) = 
  failwith ""

let inline_declaration (env : exp Env.t) aty (d : declaration) = 
  match d with
  | DLet (x, tyo, e) -> 
      let (env, e) = inline_exp env aty e in
      let env = Env.update env x e in
      (env, DLet(x,tyo,e))
  | DMerge e -> inline_exp env aty e
  | DTrans e -> inline_exp env aty e
  | DInit e -> inline_exp env aty e
  | DATy _ | DNodes _ | DEdges _ -> (env, d)

let rec inline_declarations (ds: declarations) =
  match get_attr_type ds with
  | None -> Console.error "attribute type not declared: type attribute = ..."
  | Some ty -> inline_declarations_aux Env.empty ty ds

and inline_declarations_aux env aty (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = inline_declaration env aty d in
      d' :: inline_declarations_aux env' aty ds'