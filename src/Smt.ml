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
  | TVar {contents= Link t} -> ty_to_smtlib t
  | TBool -> "Bool"
  | TInt i -> Printf.sprintf "(_ BitVec %s)" (UInt32.to_string i)
  | TTuple ts -> (
    match ts with
    | [] -> Console.error "empty tuple"
    | [t] -> ty_to_smtlib t
    | t :: ts ->
        Printf.sprintf "Pair (%s) (%s)" (ty_to_smtlib t)
          (ty_to_smtlib (TTuple ts)) )
  | TOption ty -> Printf.sprintf "Option (%s)" (ty_to_smtlib ty)
  | TMap _ | TAll _ -> Console.error "unimplemented"
  | TVar _ | QVar _ | TArrow _ ->
      Console.error
        (Printf.sprintf "internal error (ty_to_smtlib): %s"
           (Printing.ty_to_string ty))


let create_const name ty =
  Printf.sprintf "(declare-const %s %s)\n" name (ty_to_smtlib ty)


let rec encode_exp (e: exp) : string * string =
  match e.e with
  | EVar x -> ("", Var.to_string x)
  | EVal v -> ("", encode_value v.v)
  | EOp (op, es) -> (
    match op with
    | And -> encode_op "and" es
    | Or -> encode_op "or" es
    | Not ->
        let a, e = List.hd es |> encode_exp in
        (a, Printf.sprintf "(not %s)" e)
    | UAdd -> encode_op "+" es
    | USub -> encode_op "-" es
    | UEq -> encode_op "=" es
    | ULess -> encode_op "<" es
    | ULeq -> encode_op "<=" es
    | MCreate _ | MGet | MSet | MMap | MMerge ->
        Console.error "unsupported map operation" )
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
      let a = Printf.sprintf "%s(assert (= %s %s))\n" a xstr e1 in
      (a ^ a1 ^ a2, e2)
  | ETuple es -> (
    match es with
    | [] -> Console.error "internal error (encode_exp)"
    | [e] -> encode_exp e
    | e :: es ->
        let a, e1 = encode_exp e in
        let b, e2 = encode_exp (ETuple es |> exp) in
        (a ^ b, Printf.sprintf "(mk-pair %s %s)" e1 e2) )
  | EProj (i, e) -> Console.error "unimplemented: EProj"
  | ESome e ->
      let a, e = encode_exp e in
      (a, Printf.sprintf "(some (%s))" e)
  | EMatch (e, bs) ->
      let x = Var.fresh "match" in
      let name = Var.to_string x in
      let a = create_const name (oget e.ety) in
      let b, e = encode_exp e in
      let a = Printf.sprintf "%s%s(assert (= %s %s))" a b name e in
      let c, e = encode_branches name bs ("", "(false)") in
      (a ^ c, e)
  | ETy (e, ty) -> encode_exp e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"


and encode_op op_str es =
  match es with
  | [] -> Console.error "internal error (encode_op)"
  | [e] -> encode_exp e
  | e :: es ->
      let a, e1 = encode_exp e in
      let b, e2 = encode_op op_str es in
      (a ^ b, Printf.sprintf "(%s %s %s)" op_str e1 e2)


(* I'm assuming here that the cases are exhaustive *)
and encode_branches name bs acc =
  let a, acc = acc in
  match bs with
  | [] -> (a, acc)
  | (p, e) :: bs ->
      let b, e = encode_exp e in
      let c, p = encode_pattern name p in
      let acc = Printf.sprintf "(ite (%s) %s %s)" p e acc in
      encode_branches name bs (a ^ c ^ b, acc)


(* TODO: need to get the types of pattern variables *)
and encode_pattern name p =
  match p with
  | PWild -> ("", "(true)")
  | PVar x ->
      let local_name = Var.to_string x in
      let a = create_const local_name TBool in
      let binding = Printf.sprintf "%s(assert (= %s %s))" a local_name name in
      (binding, local_name)
  | PBool b -> ("", Printf.sprintf "(= %s %s)" name (string_of_bool b))
  | PUInt32 i -> ("", Printf.sprintf "(= %s %s)" name (UInt32.to_string i))
  | PTuple ps -> (
    match ps with
    | [] -> Console.error "internal error (encode_pattern)"
    | [p] -> encode_pattern name p
    | p :: ps ->
        let fst_name = Var.fresh "first" |> Var.to_string in
        let fst = create_const fst_name TBool in
        let snd_name = Var.fresh "second" |> Var.to_string in
        let snd = create_const snd_name TBool in
        let fst_decl =
          Printf.sprintf "\n%s(assert (= %s (first %s)))" fst fst_name name
        in
        let snd_decl =
          Printf.sprintf "\n%s(assert (= %s (first %s)))" snd snd_name name
        in
        let a, p = encode_pattern snd_name (PTuple ps) in
        (fst_decl ^ snd_decl ^ a, p) )
  | POption None -> ("", Printf.sprintf "(is-none %s)" name)
  | POption Some p ->
      let new_name = Var.fresh "option" |> Var.to_string in
      (* TODO: correct type here *)
      let a = create_const new_name TBool in
      let a = Printf.sprintf "\n%s(assert (= %s (val %s)))" a new_name name in
      let b, p = encode_pattern new_name p in
      (a ^ b, Printf.sprintf "(and (is-some %s) %s)" name p)


and encode_value v : string =
  match v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VUInt32 i -> UInt32.to_string i
  | VTuple vs -> (
    match vs with
    | [] -> Console.error "internal error (encode_value)"
    | [v] -> encode_value v.v
    | v :: vs ->
        Printf.sprintf "(mk-pair %s %s)" (encode_value v.v)
          (encode_value (VTuple vs)) )
  | VOption (None, _) -> "none"
  | VOption (Some v, _) -> Printf.sprintf "(some (val %s))" (encode_value v.v)
  | VClosure _ -> Console.error "internal error (closure in smt)"
  | VMap _ -> Console.error "unimplemented: map"


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
                      ; body= {e= EFun {arg= y; argty= yty; body= exp}} } } } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let ystr = Var.to_string y in
            let xty, yty = (oget xty, oget yty) in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let yparam = create_const ystr yty in
            let result = create_const "result" (oget exp.ety) in
            let a, e = encode_exp exp in
            ( Printf.sprintf "%s%s%s%s%s(assert (= result %s))" nparam xparam
                yparam a result e
            , nodestr
            , xstr
            , ystr )
        | _ -> Console.error "internal error"
      in
      let trans, tnode, z =
        match etrans.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let xty = oget xty in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let result = create_const "result" (oget exp.ety) in
            let a, e = encode_exp exp in
            ( Printf.sprintf "%s%s%s%s(assert (= result %s))" nparam xparam a
                result e
            , nodestr
            , xstr )
        | _ -> Console.error "internal error"
      in
      let init, inode =
        match einit.e with
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
