open Syntax
open Nv_datastructures

let show_opt s o =
  match o with
  | None -> "None"
  | Some x -> Printf.sprintf "Some (%s)" (s x)

let show_list s ls =
  "[" ^ List.fold_left (fun acc x -> acc ^ "," ^ s x) "" ls ^ "]"

let show_record f prefix map =
  let str = Collections.StringMap.fold
      (fun l elt acc -> Printf.sprintf "%s; %s: %s" acc l (f elt))
      map ""
  in
  Printf.sprintf "%s { %s }" prefix str

let rec show_ty ?(show_links=false) ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, _) ->
        Printf.sprintf "TVar (Unbound %s)" (Var.to_string name)
      | Link t ->
        if show_links then Printf.sprintf "Link (%s)" (show_ty t)
        else Printf.sprintf "%s" (show_ty t))
  | QVar name -> Printf.sprintf "QVar (%s)" (Var.to_string name)
  | TBool -> "TBool"
  | TInt n -> Printf.sprintf "TInt %d" n
  | TArrow (ty1, ty2) ->
    Printf.sprintf "TArrow (%s,%s)" (show_ty ty1) (show_ty ty2)
  | TTuple ts ->
    let str = show_list show_ty ts in
    Printf.sprintf "TTuple %s" str
  | TOption t -> Printf.sprintf "TOption (%s)" (show_ty t)
  | TMap (ty1, ty2) ->
    Printf.sprintf "TMap (%s,%s)" (show_ty ty1) (show_ty ty2)
  | TRecord map -> show_record show_ty "TRecord" map
  | TUnit -> "TUnit"
  | TNode -> "TNode"
  | TEdge -> "TEdge"

let rec show_exp ~show_meta e =
  if show_meta then
    Printf.sprintf "{e=%s; ety=%s; espan=%s; etag=%d; ehkey=%d}"
      (show_e ~show_meta e.e)
      (show_opt show_ty e.ety)
      (Span.show_span e.espan) e.etag e.ehkey
  else
    Printf.sprintf "e=%s" (show_e ~show_meta e.e)

and show_e ~show_meta e =
  match e with
  | EVar x -> Printf.sprintf "EVar %s" (Var.to_string x)
  | EVal v -> Printf.sprintf "EVal (%s)" (show_value ~show_meta v)
  | EOp (op, es) ->
    Printf.sprintf "EOp (%s,%s)" (show_op op)
      (show_list (show_exp ~show_meta) es)
  | EFun f -> Printf.sprintf "EFun %s" (show_func ~show_meta f)
  | EApp (e1, e2) ->
    Printf.sprintf "EApp (%s,%s)" (show_exp ~show_meta e1) (show_exp ~show_meta e2)
  | EIf (e1, e2, e3) ->
    Printf.sprintf "EIf (%s,%s,%s)" (show_exp ~show_meta e1) (show_exp ~show_meta e2)
      (show_exp ~show_meta e3)
  | ELet (x, e1, e2) ->
    Printf.sprintf "ELet (%s,%s,%s)" (Var.to_string x)
      (show_exp ~show_meta e1) (show_exp ~show_meta e2)
  | ETuple es -> Printf.sprintf "ETuple %s" (show_list (show_exp ~show_meta) es)
  | ESome e -> Printf.sprintf "ESome (%s)" (show_exp ~show_meta e)
  | EMatch (e, bs) ->
    Printf.sprintf "EMatch (%s,%s)" (show_exp ~show_meta e)
      (show_list (show_branch ~show_meta) (branchToList bs))
  | ETy (e, ty) ->
    Printf.sprintf "ETy (%s,%s)" (show_exp ~show_meta e) (show_ty ty)
  | ERecord map ->
    show_record (show_exp ~show_meta) "ERecord" map
  | EProject (e, label) ->
    Printf.sprintf "%s.%s" (show_exp ~show_meta e) label

and show_func ~show_meta f =
  Printf.sprintf "{arg=%s; argty=%s; resty=%s; body=%s}"
    (Var.to_string f.arg)
    (show_opt show_ty f.argty)
    (show_opt show_ty f.resty)
    (show_exp ~show_meta f.body)

and show_branch ~show_meta (p, e) =
  Printf.sprintf "(%s,%s)" (show_pattern p) (show_exp ~show_meta e)

and show_pattern p =
  match p with
  | PWild -> "PWild"
  | PUnit -> "PUnit"
  | PVar x -> Printf.sprintf "PVar %s" (Var.to_string x)
  | PBool b -> Printf.sprintf "PBool %b" b
  | PInt n -> Printf.sprintf "PInt %s" (Integer.to_string n)
  | PTuple ps ->
    Printf.sprintf "PTuple %s" (show_list show_pattern ps)
  | POption None -> "POption None"
  | POption (Some p) ->
    Printf.sprintf "POption (Some %s)" (show_pattern p)
  | PRecord map ->
    show_record show_pattern "PRecord" map
  | PNode node ->
    Printf.sprintf "PNode %d" node
  | PEdge (p1, p2) ->
    Printf.sprintf "PEdge %s~%s" (show_pattern p1) (show_pattern p2)

and show_value ~show_meta v =
  if show_meta then
    Printf.sprintf "{e=%s; ety=%s; espan=%s; etag=%d; ehkey=%d}"
      (show_v ~show_meta v.v)
      (show_opt show_ty v.vty)
      (Span.show_span v.vspan) v.vtag v.vhkey
  else
    Printf.sprintf "{v=%s;}"
      (show_v ~show_meta v.v)

and show_v ~show_meta v =
  match v with
  | VUnit -> "VUnit"
  | VBool b -> Printf.sprintf "VBool %b" b
  | VInt i -> Printf.sprintf "VInt %s" (Integer.to_string i)
  | VMap _ -> "VMap <opaque>"
  | VTuple vs -> Printf.sprintf "VTuple %s" (show_list (show_value ~show_meta) vs)
  | VOption vo ->
    Printf.sprintf "VOption (%s)" (show_opt (show_value ~show_meta) vo)
  | VClosure c -> Printf.sprintf "VClosure %s" (show_closure ~show_meta c)
  | VRecord map -> show_record (show_value ~show_meta) "VRecord" map
  | VNode node -> Printf.sprintf "VNode %dn" node
  | VEdge (n1, n2) -> Printf.sprintf "VEdge %dn-%dn" n1 n2

and show_closure ~show_meta (e, f) =
  Printf.sprintf "{env=%s; func=%s}" (show_env ~show_meta e) (show_func ~show_meta f)

and show_env ~show_meta e =
  Printf.sprintf "{ty=%s; value=%s}"
    (Env.to_string show_ty e.ty)
    (Env.to_string (show_value ~show_meta) e.value)
