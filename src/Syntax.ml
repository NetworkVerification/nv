(* Abstract syntax of SRP attribute processing expressions *)
open Cudd
open Hashcons
open RecordUtils

type node = int
[@@deriving eq, ord, show]

type edge = node * node
[@@deriving eq, ord, show]

type bitwidth = int
[@@deriving eq, ord, show]

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int
[@@deriving ord, eq]

type var = Var.t
[@@deriving ord, eq]

type tyname = Var.t
[@@deriving ord, eq]

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TUnit
  | TBool
  | TInt of bitwidth
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty
  | TRecord of ty StringMap.t
  | TNode
  | TEdge
[@@deriving ord, eq]

and tyvar = Unbound of tyname * level | Link of ty

type op =
  | And
  | Or
  | Not
  | Eq
  | UAdd of bitwidth
  | USub of bitwidth
  | ULess of bitwidth
  | ULeq of bitwidth
  | NLess
  | NLeq
  | AtMost of int
  | TGet of int (* Tuple size *) * int (* lo index *) * int (* hi index *)
  | TSet of int (* TUple size *) * int (* lo index *) * int (* hi index *)
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge
  | MFoldNode
  | MFoldEdge
[@@deriving show, ord, eq]

type pattern =
  | PWild
  | PVar of var
  | PUnit
  | PBool of bool
  | PInt of Integer.t
  | PTuple of pattern list
  | POption of pattern option
  | PRecord of pattern StringMap.t
  | PNode of node
  | PEdge of pattern * pattern
[@@deriving ord, eq]

module Pat =
struct
  type t = pattern

  let rec isConcretePat p =
    match p with
    | PInt _ | PBool _ | PNode _ | POption None -> true
    | PEdge (p1, p2) -> isConcretePat p1 && isConcretePat p2
    | POption (Some p) -> isConcretePat p
    | PTuple ps ->
      BatList.for_all (isConcretePat) ps
    | _ -> false

  let rec compare p1 p2 =
    match p1, p2 with
    | PInt n1, PInt n2 ->
      Pervasives.compare n1 n2
    | PBool b1, PBool b2 ->
      Pervasives.compare b1 b2
    | PNode n1, PNode n2 ->
      Pervasives.compare n1 n2
    | PEdge (p1, p2), PEdge (p1', p2') ->
      Pervasives.compare (p1, p2) (p1', p2')
    | POption p1, POption p2 ->
      Pervasives.compare p1 p2
    | PTuple ps1, PTuple ps2 ->
      BatList.fold_left2 (fun b p1 p2 ->
          if b = 0 then
            begin
              let c = compare p1 p2 in
              if (c = 0) then b
              else c
            end
          else b) 0 ps1 ps2
    | _, _ -> failwith "No comparison between non-concrete patterns"
end

module PatMap = BatMap.Make(Pat)

type v =
  | VUnit
  | VBool of bool
  | VInt of Integer.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure
  | VRecord of value StringMap.t
  | VNode of node
  | VEdge of edge
[@@deriving ord]

and value =
  {v: v;
   vty: ty option [@compare fun _ _ -> 0];
   vspan: Span.t [@compare fun _ _ -> 0];
   vtag: int [@compare fun _ _ -> 0];
   vhkey: int [@compare fun _ _ -> 0];
  }
[@@deriving ord]

and mtbdd = (value Mtbdd.t * ty)
    [@compare fun _ _ -> failwith "Map value comparison not supported"]
[@@deriving ord]

and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty
  | ERecord of exp StringMap.t
  | EProject of exp * string
[@@deriving ord]

and exp =
  {e: e;
   ety: ty option [@compare fun _ _ -> 0];
   espan: Span.t [@compare fun _ _ -> 0];
   etag: int [@compare fun _ _ -> 0];
   ehkey: int [@compare fun _ _ -> 0];
  }
[@@deriving ord]

and branches = { pmap              : exp PatMap.t;
                 plist             : (pattern * exp) list
               }

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = (env * func)
    [@compare fun _ _ -> failwith "Map value comparison not supported"]
[@@deriving ord]

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty (* Declaration of the attribute type *)
  | DUserTy of var * ty (* Declaration of a record type *)
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of int
  | DEdges of (node * node) list

type declarations = declaration list

type network =
  { attr_type : ty;
    init : exp;
    trans : exp;
    merge : exp;
    assertion : exp option;
    symbolics : (var * ty_or_exp) list;
    defs : (var * ty option * exp) list;
    utys : (ty StringMap.t) list;
    requires : exp list;
    graph : AdjGraph.t;
  }

type srp_unfold =
  { srp_attr : ty;
    srp_constraints : exp AdjGraph.VertexMap.t;
    srp_labels : (var * ty) list AdjGraph.VertexMap.t;
    srp_symbolics : (var * ty_or_exp) list;
    srp_assertion : exp option;
    srp_requires : exp list;
    srp_graph : AdjGraph.t
  }

(** * Handling branches *)

type branchLookup = Found of exp | Rest of (pattern * exp) list
(* adding to the right place won't really work.. *)
let addBranch p e b =
  {b with plist = (p,e) :: b.plist}

(* f should preserve concrete patterns *)
let mapBranches f b =
  {pmap = PatMap.fold (fun p e pmap ->
       let p, e = f (p, e) in
       PatMap.add p e pmap) b.pmap PatMap.empty;
   plist = BatList.map f b.plist}

let iterBranches f b =
  PatMap.iter (fun p e -> f (p,e)) b.pmap;
  BatList.iter f b.plist

let foldBranches f acc b =
  BatList.fold_left (fun acc x -> f x acc)
    (PatMap.fold (fun p e acc -> f (p,e) acc) b.pmap acc) b.plist

let lookUpPat p b =
  match PatMap.Exceptionless.find p b.pmap with
  | Some e ->
    Found e
  | None ->
    Rest b.plist

let popBranch b =
  if PatMap.is_empty b.pmap then
    match b.plist with
    | [] -> raise Not_found
    | (p,e) :: bs ->
      (p,e), {b with plist = bs}
  else
    let (pe, pmap) = PatMap.pop b.pmap in
    (pe, {b with pmap = pmap})

let emptyBranch =
  { pmap = PatMap.empty;
    plist = []
  }

let isEmptyBranch b =
  PatMap.is_empty b.pmap && BatList.is_empty b.plist

let optimizeBranches b =
  let rec loop map lst =
    match lst with
    | [] -> {pmap = map; plist = []}
    | (p,e) :: lst' ->
      if Pat.isConcretePat p = true then
        loop (PatMap.add p e map) lst'
      else
        {pmap = map; plist = lst}
  in
  loop b.pmap b.plist

let branchToList b =
  (PatMap.fold (fun p e acc -> (p,e) :: acc) b.pmap b.plist)

let branchSize b =
  Printf.printf "%d\n" (PatMap.cardinal b.pmap)

(* structural printing *)
(* TODO: This should probably be its own file *)

let show_span (span: Span.t) =
  Printf.sprintf "(%d,%d)" span.start span.finish

let show_opt s o =
  match o with
  | None -> "None"
  | Some x -> Printf.sprintf "Some (%s)" (s x)

let show_list s ls =
  "[" ^ List.fold_left (fun acc x -> acc ^ "," ^ s x) "" ls ^ "]"

let show_record f prefix map =
  let str = StringMap.fold
      (fun l elt acc -> Printf.sprintf "%s; %s: %s" acc l (f elt))
      map ""
  in
  Printf.sprintf "%s { %s }" prefix str

let rec show_ty ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, _) ->
        Printf.sprintf "TVar (Unbound %s)" (Var.to_string name)
      | Link t -> Printf.sprintf "Link (%s)" (show_ty t) )
  | QVar name -> Printf.sprintf "QVar (%s)" (Var.to_string name)
  | TBool -> "TBool"
  | TInt _ -> "TInt"
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
      (show_span e.espan) e.etag e.ehkey
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
      (show_span v.vspan) v.vtag v.vhkey
  else
    Printf.sprintf "{v=%s;}"
      (show_v ~show_meta v.v)

and show_v ~show_meta v =
  match v with
  | VUnit -> "VUnit"
  | VBool b -> Printf.sprintf "VBool %b" b
  | VInt i -> Printf.sprintf "VInt %s" (Integer.to_string i)
  | VMap m -> "VMap <opaque>"
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

(* equality / hashing *)

let equal_spans (s1: Span.t) (s2: Span.t) =
  s1.start = s2.start && s1.finish = s2.finish

let equal_opt e o1 o2 =
  match (o1, o2) with
  | None, None -> true
  | None, Some _ | Some _, None -> false
  | Some x, Some y -> e x y

let rec equal_lists eq_elts lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> true
  | [], _ :: _ | _ :: _, [] -> false
  | t1 :: ts1, t2 :: ts2 -> eq_elts t1 t2 && equal_lists eq_elts ts1 ts2

let rec equal_tys ty1 ty2 =
  match (ty1, ty2) with
  | TBool, TBool
  | TInt _, TInt _
  | TNode, TNode
  | TEdge, TEdge -> true
  | TVar t1, TVar t2 -> (
      match (!t1, !t2) with
      | Unbound (n1, x1), Unbound (n2, x2) ->
        Var.equals n1 n2 && x1 = x2
      | Link t1, Link t2 -> equal_tys t1 t2
      | _ -> false )
  | QVar n1, QVar n2 -> Var.equals n1 n2
  | TArrow (t1, t2), TArrow (s1, s2) ->
    equal_tys t1 s1 && equal_tys t2 s2
  | TTuple ts1, TTuple ts2 -> equal_lists equal_tys ts1 ts2
  | TRecord map1, TRecord map2 -> StringMap.equal equal_tys map1 map2
  | TOption t1, TOption t2 -> equal_tys t1 t2
  | TMap (t1, t2), TMap (s1, s2) ->
    equal_tys t1 s1 && equal_tys t2 s2
  | _ -> false

let rec equal_values ~cmp_meta (v1: value) (v2: value) =
  let cfg = Cmdline.get_cfg () in
  let b =
    if cfg.hashcons then v1.vtag = v2.vtag
    else equal_vs ~cmp_meta v1.v v2.v
  in
  if cmp_meta then
    b
    && equal_opt equal_tys v1.vty v2.vty
    && equal_spans v1.vspan v2.vspan
  else b

and equal_vs ~cmp_meta v1 v2 =
  match (v1, v2) with
  | VBool b1, VBool b2 -> b1 = b2
  | VNode n1, VNode n2 -> n1 = n2
  | VEdge e1, VEdge e2 -> e1 = e2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VMap (m1, ty1), VMap (m2, ty2) ->
    Mtbdd.is_equal m1 m2 && equal_tys ty1 ty2
  | VTuple vs1, VTuple vs2 -> equal_lists ~cmp_meta vs1 vs2
  | VOption vo1, VOption vo2 -> (
      match (vo1, vo2) with
      | None, None -> true
      | None, Some _ -> false
      | Some _, None -> false
      | Some x, Some y -> equal_values ~cmp_meta x y )
  | VClosure (e1, f1), VClosure (e2, f2) ->
    let {ty= ty1; value= value1} = e1 in
    let {ty= ty2; value= value2} = e2 in
    Env.equal equal_tys ty1 ty1
    && Env.equal (equal_values ~cmp_meta) value1 value2
    && equal_funcs ~cmp_meta f1 f2
  | VRecord map1, VRecord map2 ->
    StringMap.equal (equal_values ~cmp_meta) map1 map2
  | _, _ -> false

and equal_lists ~cmp_meta vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | v1 :: vs1, v2 :: vs2 ->
    equal_values ~cmp_meta v1 v2 && equal_lists ~cmp_meta vs1 vs2

and equal_exps ~cmp_meta (e1: exp) (e2: exp) =
  let cfg = Cmdline.get_cfg () in
  let b =
    if cfg.hashcons then e1.etag = e2.etag
    else equal_es ~cmp_meta e1.e e2.e
  in
  if cmp_meta then
    b
    && equal_opt equal_tys e1.ety e2.ety
    && equal_spans e1.espan e2.espan
  else b

and equal_es ~cmp_meta e1 e2 =
  match (e1, e2) with
  | EVar x1, EVar x2 -> Var.equals x1 x2
  | EVal v1, EVal v2 -> equal_values ~cmp_meta v1 v2
  | EOp (op1, es1), EOp (op2, es2) ->
    equal_op op1 op2 && equal_lists_es ~cmp_meta es1 es2
  | EFun f1, EFun f2 -> equal_funcs ~cmp_meta f1 f2
  | EApp (e1, e2), EApp (e3, e4) ->
    equal_exps ~cmp_meta e1 e3 && equal_exps ~cmp_meta e2 e4
  | EIf (e1, e2, e3), EIf (e4, e5, e6) ->
    equal_exps ~cmp_meta e1 e4
    && equal_exps ~cmp_meta e2 e5
    && equal_exps ~cmp_meta e3 e6
  | ELet (x1, e1, e2), ELet (x2, e3, e4) ->
    Var.equals x1 x2
    && equal_exps ~cmp_meta e1 e3
    && equal_exps ~cmp_meta e2 e4
  | ETuple es1, ETuple es2 -> equal_lists_es ~cmp_meta es1 es2
  | ESome e1, ESome e2 -> equal_exps ~cmp_meta e1 e2
  | EMatch (e1, bs1), EMatch (e2, bs2) ->
    equal_exps ~cmp_meta e1 e2 && equal_branches ~cmp_meta bs1 bs2
  | ETy (e1, ty1), ETy (e2, ty2) ->
    equal_exps ~cmp_meta e1 e2 && ty1 = ty2
  | ERecord map1, ERecord map2 ->
    StringMap.equal (equal_exps ~cmp_meta) map1 map2
  | EProject (e1, label1), EProject (e2, label2) ->
    String.equal label1 label2 && equal_exps ~cmp_meta e1 e2
  | _, _ -> false

and equal_lists_es ~cmp_meta es1 es2 =
  match (es1, es2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | e1 :: es1, e2 :: es2 ->
    equal_exps ~cmp_meta e1 e2 && equal_lists_es ~cmp_meta es1 es2

and equal_branches ~cmp_meta bs1 bs2 =
  let rec equal_branches_lst bs1 bs2 =
    match (bs1, bs2) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | (p1, e1) :: bs1, (p2, e2) :: bs2 ->
      equal_patterns p1 p2
      && equal_exps ~cmp_meta e1 e2
      && equal_branches_lst bs1 bs2
  in
  let equal_branches_map bs1 bs2 =
    PatMap.cardinal bs1.pmap = PatMap.cardinal bs2.pmap &&
    PatMap.for_all (fun p e -> match PatMap.Exceptionless.find p bs2.pmap with
        | None -> false
        | Some e' -> equal_exps ~cmp_meta e e') bs1.pmap
  in
  (equal_branches_map bs1 bs2) && (equal_branches_lst bs1.plist bs2.plist)

and equal_patterns p1 p2 =
  match (p1, p2) with
  | PWild, PWild -> true
  | PVar x1, PVar x2 -> Var.equals x1 x2
  | PBool b1, PBool b2 -> b1 = b2
  | PInt i, PInt j -> Integer.equal i j
  | PTuple ps1, PTuple ps2 -> equal_patterns_list ps1 ps2
  | POption None, POption None -> true
  | POption (Some p1), POption (Some p2) -> equal_patterns p1 p2
  | PRecord map1, PRecord map2 -> StringMap.equal equal_patterns map1 map2
  | PNode n1, PNode n2 -> n1 = n2
  | PEdge (p1, p2), PEdge (p1', p2') -> equal_patterns p1 p1' && equal_patterns p2 p2'
  | _ -> false

and equal_patterns_list ps1 ps2 =
  match (ps1, ps2) with
  | [], [] -> true
  | _ :: _, [] | [], _ :: _ -> false
  | p1 :: ps1, p2 :: ps2 ->
    equal_patterns p1 p2 && equal_patterns_list ps1 ps2

and equal_funcs ~cmp_meta f1 f2 =
  let {arg= x; argty= aty1; resty= rty1; body= e1} = f1 in
  let {arg= y; argty= aty2; resty= rty2; body= e2} = f2 in
  let b =
    if cmp_meta then
      equal_opt equal_tys aty1 aty2 && equal_opt equal_tys rty1 rty2
    else true
  in
  b && Var.equals x y && equal_exps ~cmp_meta e1 e2

let hash_string str =
  let acc = ref 7 in
  for i = 0 to String.length str - 1 do
    let c : char = str.[i] in
    acc := (31 * !acc) + int_of_char c
  done ;
  !acc

let rec hash_ty ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, x) -> hash_string (Var.to_string name) + x
      | Link t -> 2 + hash_ty t )
  | QVar name -> 3 + hash_string (Var.to_string name)
  | TBool -> 4
  | TInt _ -> 5
  | TArrow (ty1, ty2) -> 6 + hash_ty ty1 + hash_ty ty2
  | TTuple ts ->
    List.fold_left (fun acc t -> acc + hash_ty t) 0 ts + 7
  | TOption t -> 8 + hash_ty t
  | TMap (ty1, ty2) -> 9 + hash_ty ty1 + hash_ty ty2
  | TRecord map ->
    StringMap.fold (fun l t acc -> acc + + hash_string l + hash_ty t) map 0 + 10
  | TUnit -> 11
  | TNode -> 12
  | TEdge -> 13

let hash_span (span: Span.t) = (19 * span.start) + span.finish

let hash_opt h o =
  match o with None -> 1 | Some x -> (19 * h x) + 2

let rec hash_value ~hash_meta v : int =
  let cfg = Cmdline.get_cfg () in
  let m =
    if hash_meta then
      (19 * hash_opt hash_ty v.vty) + hash_span v.vspan
    else 0
  in
  if cfg.hashcons then (19 * v.vhkey) + m
  else (19 * hash_v ~hash_meta v.v) + m

and hash_v ~hash_meta v =
  match v with
  | VBool b -> if b then 1 else 0
  | VInt i -> (19 * Integer.to_int i) + 1
  | VMap m -> (19 * Hashtbl.hash m) + 2
  | VTuple vs ->
    let acc =
      List.fold_left
        (fun acc v -> acc + hash_value ~hash_meta v)
        0 vs
    in
    (19 * acc) + 3
  | VOption vo -> (
      match vo with
      | None -> 4
      | Some x -> (19 * hash_value ~hash_meta x) + 4 )
  | VClosure (e1, f1) ->
    let {ty= ty1; value= v} = e1 in
    let vs = Env.to_list v in
    let acc =
      List.fold_left
        (fun acc (x, v) ->
           let x = hash_string (Var.to_string x) in
           acc + x + hash_value ~hash_meta v )
        0 vs
    in
    (19 * acc) + 5
  | VRecord map ->
    let acc =
      StringMap.fold
        (fun l v acc -> acc + + hash_string l + hash_value ~hash_meta v)
        map 0
    in
    (19 * acc) + 7
  | VUnit -> 8
  | VNode n -> (19 * n) + 9
  | VEdge (e1, e2) -> (19 * (e1 + 19 * e2)) + 10

and hash_exp ~hash_meta e =
  let cfg = Cmdline.get_cfg () in
  let m =
    if hash_meta then
      (19 * hash_opt hash_ty e.ety) + hash_span e.espan
    else 0
  in
  if cfg.hashcons then (19 * e.ehkey) + m
  else (19 * hash_e ~hash_meta e.e) + m

and hash_e ~hash_meta e =
  match e with
  | EVar x -> hash_var x
  | EVal v -> (19 * hash_value ~hash_meta v) + 1
  | EOp (op, es) ->
    (19 * ((19 * hash_op op) + hash_es ~hash_meta es)) + 2
  | EFun f ->
    let i =
      if hash_meta then
        hash_opt hash_ty f.argty + hash_opt hash_ty f.resty
      else 0
    in
    19
    * ( (19 * ((19 * hash_var f.arg) + hash_exp ~hash_meta f.body))
        + i )
    + 3
  | EApp (e1, e2) ->
    (19 * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2))
    + 4
  | EIf (e1, e2, e3) ->
    19
    * ( 19
        * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2)
        + hash_exp ~hash_meta e3 )
    + 5
  | ELet (x, e1, e2) ->
    19
    * ( (19 * ((19 * hash_var x) + hash_exp ~hash_meta e1))
        + hash_exp ~hash_meta e2 )
    + 6
  | ETuple es -> (19 * hash_es ~hash_meta es) + 7
  | ESome e -> (19 * hash_exp ~hash_meta e) + 8
  | EMatch (e, bs) ->
    19
    * ((19 * hash_exp ~hash_meta e) + hash_branches ~hash_meta bs)
    + 9
  | ETy (e, ty) ->
    (19 * ((19 * hash_exp ~hash_meta e) + hash_ty ty)) + 10
  | ERecord map ->
    (19 *
     StringMap.fold
       (fun l e acc -> acc + + hash_string l + hash_exp ~hash_meta e) map 0
     + 11)
  | EProject (e, label) ->
    (19 * hash_exp ~hash_meta e + hash_string label + 12)

and hash_var x = hash_string (Var.to_string x)

and hash_es ~hash_meta es =
  List.fold_left (fun acc e -> acc + hash_exp ~hash_meta e) 0 es

and hash_branches ~hash_meta bs =
  let acc1 = BatList.fold_left
      (fun acc (p, e) -> acc + hash_pattern p + hash_exp ~hash_meta e)
      0 bs.plist
  in
  PatMap.fold
    (fun p e acc -> acc + hash_pattern p + hash_exp ~hash_meta e) bs.pmap acc1

and hash_pattern p =
  match p with
  | PUnit -> 0
  | PWild -> 1
  | PVar x -> (19 * hash_var x) + 2
  | PBool b -> (19 * if b then 1 else 0) + 3
  | PInt i -> (19 * Integer.to_int i) + 4
  | PTuple ps -> (19 * hash_patterns ps) + 5
  | POption None -> 6
  | POption (Some p) -> (19 * hash_pattern p) + 7
  | PRecord map ->
    (19 *
     StringMap.fold (fun l p acc -> acc + + hash_string l + hash_pattern p) map 0
     + 8)
  | PNode n -> (19 * n) + 9
  | PEdge (p1, p2) -> (19 * (hash_pattern p1 + 19 * hash_pattern p2)) + 10

and hash_patterns ps =
  List.fold_left (fun acc p -> acc + hash_pattern p) 0 ps

and hash_op op =
  match op with
  | And -> 1
  | Or -> 2
  | Not -> 3
  | Eq -> 4
  | MCreate -> 5
  | MGet -> 6
  | MSet -> 7
  | MMap -> 8
  | MMapFilter -> 9
  | MMerge -> 10
  | UAdd n -> 11  + n + 256
  | USub n -> 11  + n + 256 * 2
  | ULess n -> 11 + n + 256 * 3
  | ULeq n -> 11  + n + 256 * 4
  | AtMost n -> 12 + n
  | NLess -> 13
  | NLeq -> 14
  | MFoldNode -> 15
  | MFoldEdge -> 16
  | TGet (n1, n2, n3) -> 17 + n1 + n2 + n3 + 256 * 5
  | TSet (n1, n2, n3) -> 17 + n1 + n2 + n3 + 256 * 6
(* hashconsing information/tables *)

let meta_v : (v, value) meta =
  { hash= hash_v ~hash_meta:true
  ; equal= equal_vs ~cmp_meta:true
  ; node= (fun v -> v.v)
  ; make=
      (fun ~tag ~hkey v ->
         {v; vty= None; vspan= Span.default; vtag= tag; vhkey= hkey}
      )
  ; hkey= (fun v -> v.vhkey) }

let meta_e : (e, exp) meta =
  { hash= hash_e ~hash_meta:true
  ; equal= equal_es ~cmp_meta:true
  ; node= (fun e -> e.e)
  ; make=
      (fun ~tag ~hkey e ->
         {e; ety= None; espan= Span.default; etag= tag; ehkey= hkey}
      )
  ; hkey= (fun e -> e.ehkey) }

let tbl_v = Hashcons.create meta_v 251

let tbl_e = Hashcons.create meta_e 251

(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd _ -> 2
  | USub _ -> 2
  | Eq -> 2
  | ULess _ -> 2
  | ULeq _ -> 2
  | NLess -> 2
  | NLeq -> 2
  | AtMost _ -> 3
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMapFilter -> 3
  | MMerge -> 3
  | MFoldNode -> 3
  | MFoldEdge -> 3
  | TGet _ -> 1
  | TSet _ -> 2

(* Useful constructors *)

let tint_of_size n = TInt n

let tint_of_value n = TInt (Integer.size n)

let exp e =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then Hashcons.hashcons tbl_e e
  else {e; ety= None; espan= Span.default; etag= 0; ehkey= 0}

let value v =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then Hashcons.hashcons tbl_v v
  else {v; vty= None; vspan= Span.default; vtag= 0; vhkey= 0}

let aexp (e, t, span) = {e with ety= t; espan= span}

let avalue (v, t, span) = {v with vty= t; vspan= span}

let wrap exp e = {e with ety= exp.ety; espan= exp.espan}

(* Constructors *)

let vunit () = value VUnit

let vbool b = {(value (VBool b)) with vty = Some TBool}

let vnode n = value (VNode n)

let vedge e = value (VEdge e)

let vint i = value (VInt i)

let vmap m = value (VMap m)

let vtuple vs = value (VTuple vs)

let vrecord map = value (VRecord map)

let voption vo = value (VOption vo)

let vclosure c = value (VClosure c)

let evar x = exp (EVar x)

let e_val v = exp (EVal v)

let eop op es = exp (EOp (op, es))

let efun f = exp (EFun f)

let eapp e1 e2 = exp (EApp (e1, e2))

let eif e1 e2 e3 = exp (EIf (e1, e2, e3))

let elet x e1 e2 = exp (ELet (x, e1, e2))

let etuple es = exp (ETuple es)

let eproject e l = exp (EProject (e,l))

let erecord map = exp (ERecord map)

let esome e = exp (ESome e)

let ematch e bs = exp (EMatch (e, bs))

let ety e ty = exp (ETy (e, ty))

let deconstructFun exp =
  match exp.e with
  | EFun f ->
    f
  | _ -> failwith "expected a function"

let rec is_value e =
  match e.e with
  | EVal _ -> true
  | ETuple es -> BatList.for_all is_value es
  | ERecord map -> StringMap.for_all (fun _ e -> is_value e) map
  | ESome e -> is_value e
  | ETy (e, _) -> is_value e
  | EVar _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _
  | EProject _ ->
    false

let rec to_value e =
  match e.e with
  | EVal v -> v
  | ETy (e, _) -> to_value e
  | ETuple es ->
    avalue (vtuple (BatList.map to_value es), e.ety, e.espan)
  | ESome e1 -> avalue (voption (Some (to_value e1)), e.ety, e.espan)
  | _ -> failwith "internal error (to_value)"


let exp_of_v x = exp (EVal (value x))

let rec exp_of_value v =
  match v.v with
  | VUnit | VBool _ | VInt _ | VMap _ | VClosure _ | VOption None | VNode _ | VEdge _->
    let e = e_val v in
    {e with ety= v.vty; espan=v.vspan}
  | VTuple vs ->
    let e = etuple (BatList.map exp_of_value vs) in
    {e with ety= v.vty; espan=v.vspan}
  | VRecord map ->
    let e = erecord (StringMap.map exp_of_value map) in
    {e with ety= v.vty; espan=v.vspan}
  | VOption (Some v1) ->
    let e = esome (exp_of_value v1) in
    {e with ety= v.vty; espan=v.vspan}

let rec val_to_pattern v =
  match v.v with
  | VUnit -> PUnit
  | VNode n -> PNode n
  | VEdge (n1, n2) -> PEdge (PNode n1, PNode n2)
  | VBool b -> PBool b
  | VInt i -> PInt i
  | VTuple vs -> PTuple (BatList.map val_to_pattern vs)
  | VOption None -> POption None
  | VOption (Some v) -> POption (Some (val_to_pattern v))
  | VRecord rs -> PRecord (StringMap.map val_to_pattern rs)
  | VClosure _ | VMap _ -> failwith "can't use these type of values as patterns"

let rec exp_to_pattern e =
  match e.e with
  | EVal v ->
    val_to_pattern v
  | ETuple es -> PTuple (BatList.map exp_to_pattern es)
  | ESome e -> POption (Some (exp_to_pattern e))
  | ETy (e, _) -> exp_to_pattern e
  | EVar x -> PVar x
  | ERecord rs -> PRecord (StringMap.map exp_to_pattern rs)
  | EProject _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _ ->
    failwith "can't use these expressions as patterns"

let func x body = {arg= x; argty= None; resty= None; body}

let funcFull x argty resty body = {arg= x; argty= argty; resty= resty; body}

let efunc f =
  match f.argty, f.resty with
  | Some argty, Some resty ->
    aexp (exp (EFun f), Some (TArrow (argty, resty)), Span.default)
  | _, _ ->
    exp (EFun f)

let lam x body = exp (EFun (func x body))

let annot ty e = {e with ety= Some ty; espan= e.espan}

let annotv ty v = {v with vty= Some ty; vspan= v.vspan}

let oget (x: 'a option) : 'a =
  match x with
  | None -> failwith "internal error (oget)"
  | Some y -> y

let omap (f : 'a -> 'b) (x: 'a option): 'b option =
  match x with
  | None -> None
  | Some y -> Some(f y)

let rec lams params body =
  match params with
  | [] -> failwith "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> failwith "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let apply_closure cl (args: value list) =
  apps (exp_of_v (VClosure cl)) (List.map (fun a -> e_val a) args)

(* Requires that e is of type TTuple *)
let tupleToList (e : exp) =
  match e.e with
  | ETuple es -> es
  | EVal v ->
    (match v.v with
     | VTuple vs ->
       BatList.map (fun v -> aexp(e_val v, v.vty, v.vspan)) vs
     | _ -> failwith "Not a tuple type")
  | _ -> failwith "Not a tuple type"

let tupleToListSafe (e : exp) =
  match e.e with
  | ETuple _| EVal _ -> tupleToList e
  | _ -> [e]


let get_decl ds f =
  try
    let daty : declaration =
      List.find
        (fun d -> match f d with None -> false | Some _ -> true)
        ds
    in
    f daty
  with _ -> None

let get_lets ds =
  BatList.filter_map (fun d -> match d with DLet (x,ty,e) -> Some (x,ty,e) | _ -> None) ds

let get_attr_type ds =
  get_decl ds (fun d -> match d with DATy ty -> Some ty | _ -> None)

let get_merge ds =
  get_decl ds (fun d -> match d with DMerge e -> Some e | _ -> None)

let get_trans ds =
  get_decl ds (fun d -> match d with DTrans e -> Some e | _ -> None)

let get_init ds =
  get_decl ds (fun d -> match d with DInit e -> Some e | _ -> None)

let get_assert ds =
  get_decl ds (fun d ->
      match d with DAssert e -> Some e | _ -> None )

let get_edges ds =
  get_decl ds (fun d ->
      match d with DEdges es -> Some es | _ -> None )

let get_nodes ds =
  get_decl ds (fun d -> match d with DNodes i -> Some i | _ -> None)

let get_symbolics ds =
  List.fold_left
    (fun acc d ->
       match d with DSymbolic (x, e) -> (x, e) :: acc | _ -> acc )
    [] ds
  |> List.rev

let get_requires ds =
  List.fold_left
    (fun acc d -> match d with DRequire e -> e :: acc | _ -> acc)
    [] ds
  |> List.rev

let get_record_types ds =
  List.fold_left
    (fun acc d ->
       match d with
       | DUserTy (_, TRecord lst) -> (lst) :: acc
       | _ -> acc
    )
    [] ds

let rec get_inner_type t : ty =
  match t with TVar {contents= Link t} -> get_inner_type t | _ -> t

let get_ty_from_tyexp (et : ty_or_exp) : ty =
  match et with
  | Ty t -> t
  | Exp e -> oget (e.ety)

let bool_of_val (v : value) : bool option =
  match v.v with
  | VBool b -> Some b
  | _ -> None

let proj_var (n: int) (x: var) =
  let (s,i) = Var.from_var x in
  Var.to_var (Printf.sprintf "%s-proj-%d" s n,i)

let unproj_var (x : var) =
  let (s,i) = Var.from_var x in
  let name, n = BatString.split s "-proj-" in
  (int_of_string n, Var.to_var (name, i))

open BatSet

let rec free (seen: Var.t PSet.t) (e: exp) : Var.t PSet.t =
  match e.e with
  | EVar v ->
    if PSet.mem v seen then PSet.create Var.compare
    else PSet.singleton ~cmp:Var.compare v
  | EVal _ -> PSet.create Var.compare
  | EOp (_, es) | ETuple es ->
    List.fold_left
      (fun set e -> PSet.union set (free seen e))
      (PSet.create Var.compare)
      es
  | ERecord map ->
    StringMap.fold
      (fun _ e set -> PSet.union set (free seen e))
      map
      (PSet.create Var.compare)
  | EFun f -> free (PSet.add f.arg seen) f.body
  | EApp (e1, e2) -> PSet.union (free seen e1) (free seen e2)
  | EIf (e1, e2, e3) ->
    PSet.union (free seen e1)
      (PSet.union (free seen e2) (free seen e3))
  | ELet (x, e1, e2) ->
    let seen = PSet.add x seen in
    PSet.union (free seen e1) (free seen e2)
  | ESome e | ETy (e, _) | EProject (e, _) -> free seen e
  | EMatch (e, bs) ->
    let bs1 =
      PatMap.fold
        (fun p e set ->
           let seen = PSet.union seen (pattern_vars p) in
           PSet.union set (free seen e) )
        bs.pmap
        (PSet.create Var.compare)
    in
    let bs =
      BatList.fold_left
        (fun set (p, e) ->
           let seen = PSet.union seen (pattern_vars p) in
           PSet.union set (free seen e) )
        bs1
        bs.plist
    in
    PSet.union (free seen e) bs

and pattern_vars p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | POption None | PNode _ ->
    PSet.create Var.compare
  | PVar v -> PSet.singleton ~cmp:Var.compare v
  | PEdge (p1, p2) -> pattern_vars (PTuple [p1; p2])
  | PTuple ps ->
    List.fold_left
      (fun set p -> PSet.union set (pattern_vars p))
      (PSet.create Var.compare)
      ps
  | PRecord map ->
    StringMap.fold
      (fun _ p set -> PSet.union set (pattern_vars p))
      map
      (PSet.create Var.compare)
  | POption (Some p) -> pattern_vars p

let rec free_dead_vars (e : exp) =
  match e.e with
  | ETy (e, _) -> free_dead_vars e
  | EVal v ->
    (match v.v with
     | VClosure (env, f) ->
       let fv = free (PSet.empty) f.body in
       vclosure ({env with value = Env.filter env.value (fun x _ -> PSet.mem x fv)},
                 {f with body = free_dead_vars f.body})
       |> exp_of_value
       |> wrap e
     | _ -> e)
  | EVar _ | EFun _ -> e
  | EOp (op, es) ->
    eop op (List.map free_dead_vars es)
  | EApp (e1, e2) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    eapp e1 e2
  | EIf (e1, e2, e3) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    let e3 = free_dead_vars e3 in
    eif e1 e2 e3
  | ELet (x, e1, e2) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    elet x e1 e2
  | ETuple es ->
    etuple (List.map free_dead_vars es)
  | ERecord map ->
    erecord (StringMap.map free_dead_vars map)
  | ESome e -> esome (free_dead_vars e)
  | EMatch (e1, branches) ->
    let e1 = free_dead_vars e1 in
    ematch e1
      (mapBranches (fun (ps, e) -> (ps, free_dead_vars e)) branches)
  | EProject (e, l) -> eproject (free_dead_vars e) l


(* This is used because for SMT we represent maps as map expression
   and not values, and we want some type of default value for them as
   well *)
let rec default_exp_value ty =
  match ty with
  | TUnit -> exp_of_value (avalue (vunit (), Some ty, Span.default))
  | TBool -> exp_of_value (avalue (vbool false, Some ty, Span.default))
  | TNode -> exp_of_value (avalue (vnode 0, Some TNode, Span.default))
  | TEdge -> exp_of_value (avalue (vedge (0, 1), Some TEdge, Span.default))
  | TInt size ->
    exp_of_value (avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default))
  | TTuple ts ->
    aexp (etuple (BatList.map default_exp_value ts), Some ty, Span.default)
  | TRecord map -> aexp (etuple (BatList.map default_exp_value @@ get_record_entries map),
                         Some ty, Span.default)
  | TOption _ ->
    exp_of_value (avalue (voption None, Some ty, Span.default))
  | TMap (ty1, ty2) ->
    aexp(eop MCreate [default_exp_value ty2], Some ty, Span.default)
  | TVar {contents= Link t} ->
    default_exp_value t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

let compare_vs = compare_value
let compare_es = compare_exp

let compare_values v1 v2 =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then v1.vtag - v2.vtag
  else Pervasives.compare v1 v2

let compare_exps e1 e2 =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then e1.etag - e2.etag
  else Pervasives.compare e1 e2
