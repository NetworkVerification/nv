open Unsigned
open Syntax

(* encoding in the smt-lib format *)
type smt_encoding =
  { defs: string
  ; merge: string
  ; merge_args: string list
  ; trans: string
  ; trans_args: string list
  ; init: string
  ; init_args: string list }

let rec ty_to_smtlib (ty: ty) : string =
  match ty with
  | TBool -> "Bool"
  | TInt i -> "_ BitVec " ^ UInt32.to_string i
  | TTuple ts -> (
    match ts with
    | [] -> Console.error "empty tuple"
    | [t] -> ty_to_smtlib t
    | t :: ts -> "Pair " ^ ty_to_smtlib t ^ " " ^ ty_to_smtlib (TTuple ts) )
  | TOption ty -> Console.error "unimplemented"
  | TMap _ | TAll _ -> Console.error "unimplemented"
  | TVar _ | QVar _ | TArrow _ -> Console.error "internal error (ty_to_smtlib)"


let create_const name ty =
  Printf.sprintf "(declare-const %s %s)\n" name (ty_to_smtlib ty)


let rec encode_exp (e: exp) : string * string =
  match e.e with
  | EVar x -> ("", Var.to_string x)
  | EVal v -> encode_value e
  | EOp (op, es) -> failwith ""
  | EIf (e1, e2, e3) ->
      let a1, e1 = encode_exp e1 in
      let a2, e2 = encode_exp e2 in
      let a3, e3 = encode_exp e3 in
      (a1 ^ a2 ^ a3, Printf.sprintf "(ite %s %s %s)" e1 e2 e3)
  | ELet (x, e1, e2) ->
      let xstr = Var.to_string x in
      let a = create_const xstr (oget e1.ety) in
      let a1, e1 = encode_exp e1 in
      let a2, e2 = encode_exp e2 in
      let a = Printf.sprintf "%s\n(assert (= %s %s))\n" a xstr e1 in
      (a ^ a1 ^ a2, e2)
  | ETuple es -> failwith ""
  | EProj (i, e) -> failwith ""
  | ESome e ->
      let a, e = encode_exp e in
      (a, Printf.sprintf "(some (%s))" e)
  | EMatch (e, bs) -> failwith ""
  | ETy (e, ty) -> encode_exp e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"


and encode_value v = failwith ""

let encode (ds: declarations) : smt_encoding =
  let defs =
    "(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))\n\
     (declare-datatypes (T) ((Option none (some (val T)))))\n\
     "
  in
  match (get_merge ds, get_trans ds, get_init ds) with
  | Some emerge, Some etrans, Some einit ->
      let merge, mnode, x, y =
        match emerge.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body=
                { e=
                    EFun
                      { arg= x
                      ; argty= xty
                      ; body= {e= EFun {arg= y; argty= yty; body= e}} } } } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let ystr = Var.to_string y in
            let xty, yty = (oget xty, oget yty) in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let yparam = create_const ystr yty in
            let result = create_const "result" (oget e.ety) in
            let a, e = encode_exp e in
            ( Printf.sprintf "%s%s%s%s%s(assert (= result %s))" nparam xparam
                yparam a result e
            , nodestr
            , xstr
            , ystr )
        | _ -> Console.error "internal error"
      in
      let trans, tnode, z =
        match emerge.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body= {e= EFun {arg= x; argty= xty; body= e}} } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let xty = oget xty in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let result = create_const "result" (oget e.ety) in
            let a, e = encode_exp e in
            ( Printf.sprintf "%s%s%s%s(assert (= result %s))" nparam xparam a
                result e
            , nodestr
            , xstr )
        | _ -> Console.error "internal error"
      in
      let init, inode =
        match emerge.e with
        | EFun {arg= node; argty= nodety; body= e} ->
            let nodestr = Var.to_string node in
            let nparam = create_const nodestr (oget nodety) in
            let result = create_const "result" (oget e.ety) in
            let a, e = encode_exp e in
            ( Printf.sprintf "%s%s%s\n(assert (= result %s))" nparam a result e
            , nodestr )
        | _ -> Console.error "internal error"
      in
      { defs
      ; merge
      ; merge_args= [mnode; x; y]
      ; trans
      ; trans_args= [tnode; z]
      ; init
      ; init_args= [inode] }
  | _ -> Console.error "attribute type not declared: type attribute = ..."
