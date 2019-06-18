(** Compiles an NV program to an OCaml program*)
open Syntax

(** Translating nv records to OCaml records (type or values depending on f)*)
let record_to_ocaml_record
      (sep: string)
      (f : 'a -> string)
      (map : 'a RecordUtils.StringMap.t)
  : string
  =
  let entries =
    RecordUtils.StringMap.fold
      (fun l e acc ->
         Printf.sprintf "%s%s %s %s;" acc l sep (f e)
      )
      map ""
  in
  Printf.sprintf "{ %s }" entries

let is_keyword_op op =
  match op with
  | And | Or | Not | UAdd _ | USub _ | Eq | ULess _ | ULeq _ | MGet | NLess | NLeq -> false
  | MCreate | MSet | MMap | MMerge | MMapFilter | AtMost _ -> true

(** Translating NV operators to OCaml operators*)
let op_to_ocaml_string op =
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | UAdd n -> "+"
  | USub n -> "-"
  | Eq -> "="
  | ULess n -> "<"
  | ULeq n -> "<="
  | NLess -> "<"
  | NLeq -> "<="
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge -> failwith "Map ops are still todo"
  | AtMost _ -> failwith "todo: atmost"

(** Translating NV patterns to OCaml patterns*)
let rec pattern_to_ocaml_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> Var.name x
  | PUnit -> "()"
  | PBool true -> "true"
  | PBool false -> "false"
  | PInt i -> string_of_int (Integer.to_int i)
  | PTuple ps ->
     Collections.printList pattern_to_ocaml_string ps "(" ", "  ")"
  | POption None -> "None"
  | POption (Some p) -> Printf.sprintf "Some %s" (pattern_to_ocaml_string p)
  | PRecord map -> record_to_ocaml_record "=" pattern_to_ocaml_string map
  | PNode n -> Printf.sprintf "%d" n
  | PEdge (p1, p2) -> Printf.sprintf "(%s, %s)" (pattern_to_ocaml_string p1)
                        (pattern_to_ocaml_string p2)


(** NV types to OCaml types*)
let rec ty_to_ocaml_string t =
  match t with
  | TVar {contents= Link ty } ->
     ty_to_ocaml_string ty
  | TVar {contents= Unbound _ } -> failwith "Unbound type variable"
  | QVar name ->
     Printf.sprintf "'%s" (Var.name name)
  | TUnit -> "unit"
  | TBool -> "bool"
  | TInt _ -> "int"
  | TNode -> "int"
  | TEdge -> "int"
  | TArrow (t1, t2) ->
     Printf.sprintf "%s -> %s"
       (ty_to_ocaml_string t1)
       (ty_to_ocaml_string t2)
  | TTuple ts ->
     Collections.printList ty_to_ocaml_string ts "(" " * " ")"
  | TOption t ->
     Printf.sprintf "(%s) option"
       (ty_to_ocaml_string t)
  | TMap (t1, t2) ->
     failwith "Map types not yet translated"
  | TRecord map ->
     record_to_ocaml_record ":" ty_to_ocaml_string map

(** Translating NV values and expressions to OCaml*)
let rec value_to_ocaml_string v =
  match v.v with
  | VUnit -> "()"
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> string_of_int (Integer.to_int i)
  | VMap m ->
     failwith "This seems doable, but later: map_to_ocaml_string m"
  | VTuple vs ->
     Collections.printList value_to_ocaml_string vs "(" "; " ")"
  | VOption None ->
     "None"
  | VOption (Some v) ->
     Printf.sprintf "Some (%s)" (value_to_ocaml_string v)
  | VClosure cl -> failwith "Closures shouldn't appear here."
  | VRecord map ->
     record_to_ocaml_record "=" value_to_ocaml_string map
  | VNode n -> string_of_int n
  | VEdge (n1, n2) -> Printf.sprintf "(%d, %d)" n1 n2

and exp_to_ocaml_string e =
    match e.e with
    | EVar x -> Var.name x
    | EVal v -> value_to_ocaml_string v
    | EOp (op, es) -> op_args_to_ocaml_string op es
    | EFun f -> func_to_ocaml_string f
    | EApp (e1, e2) ->
       Printf.sprintf "(%s %s)"
         (exp_to_ocaml_string e1)
         (exp_to_ocaml_string e2)
    | EIf (e1, e2, e3) ->
       Printf.sprintf "(if %s then\n %s else\n %s)"
         (exp_to_ocaml_string e1)
         (exp_to_ocaml_string e2)
         (exp_to_ocaml_string e3)
    | ELet (x, e1, e2) ->
       Printf.sprintf "(let %s = %s in\n %s)"
         (Var.name x)
         (exp_to_ocaml_string e1)
         (exp_to_ocaml_string e2)
    | ETuple es ->
       Collections.printList exp_to_ocaml_string es "(" ", " ")"
    | ESome e ->
       Printf.sprintf "(Some %s)" (exp_to_ocaml_string e)
    | EMatch (e1, bs) ->
       Printf.sprintf "(match %s with \n %s)"
         (exp_to_ocaml_string e1)
         (Collections.printList branch_to_ocaml_string
            (branchToList bs) "" "" "")
    | ETy (e, t) -> exp_to_ocaml_string e
    | ERecord map -> record_to_ocaml_record "=" exp_to_ocaml_string map
    | EProject (e, l) ->
       Printf.sprintf "(%s.%s)" (exp_to_ocaml_string e) l

and op_args_to_ocaml_string op es =
  if is_keyword_op op then
    Printf.sprintf "(%s %s)" (op_to_ocaml_string op)
      (Collections.printList exp_to_ocaml_string es "" " " "")
  else
    match es with
    | [] -> failwith "Empty operand list"
    | [e1] -> Printf.sprintf "(%s %s)" (op_to_ocaml_string op) (exp_to_ocaml_string e1)
    | [e1; e2] ->
       Printf.sprintf "(%s %s %s)" (exp_to_ocaml_string e1)
         (op_to_ocaml_string op) (exp_to_ocaml_string e1)
    | _ -> failwith "Should be a keyword op"

and func_to_ocaml_string f =
  Printf.sprintf "(fun %s -> %s)" (Var.name f.arg) (exp_to_ocaml_string f.body)

and branch_to_ocaml_string (p, e) =
  Printf.sprintf "| %s -> %s\n"
    (pattern_to_ocaml_string p)
    (exp_to_ocaml_string e)

let hasRequire = ref false
let hasAssertion = ref false

let rec declaration_to_ocaml_string d =
  match d with
  | DLet (x, tyo, e) ->
     Printf.sprintf "let %s = %s\n"
       (Var.name x) (exp_to_ocaml_string e)
  | DSymbolic (x, Exp e) ->
     Printf.sprintf "let %s = %s\n"
       (Var.name x) (exp_to_ocaml_string e)
  | DSymbolic (x, Ty ty) ->
     Printf.sprintf "let %s = %s\n"
       (Var.name x) (value_to_ocaml_string (default_value ty))
  | DMerge e ->
     Printf.sprintf "let merge = %s\n" (exp_to_ocaml_string e)
  | DTrans e ->
     Printf.sprintf "let trans = %s\n" (exp_to_ocaml_string e)
  | DAssert e ->
     hasAssertion := true;
     Printf.sprintf "let assertion = %s\n" (exp_to_ocaml_string e)
  | DRequire e ->
     hasRequire := true;
     Printf.sprintf "let require = %s\n" (exp_to_ocaml_string e)
  | DNodes n -> "let graph = AdjGraph.create n"
  | DEdges es ->
     Printf.sprintf
       "let graph = AdjGraph.add_edges graph\n %s"
       (Collections.printList (fun (u,v) ->
            Printf.sprintf "(%d,%d)" u v) es "[" ";\n" "]")
  | DInit e ->
     Printf.sprintf "let init = %s\n" (exp_to_ocaml_string e)
  | DATy t ->
     Printf.sprintf "type attribute = %s" (ty_to_ocaml_string t)
  | DUserTy (name, ty) ->
    Printf.sprintf "type %s = %s" (Var.name name) (ty_to_ocaml_string ty)

let rec declarations_to_ocaml_string ds =
  Collections.printList declaration_to_ocaml_string ds "" "\n" "\n"

let set_entry (name: string) =
  Printf.sprintf "let () = p := Some (module %s:SrpNative.NATIVE_SRP)" name

let generate_ocaml (name : string) ds =
  let name = Filename.basename name |>
               String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c)
  in
  let header = Printf.sprintf "module %s : NATIVE_SRP = struct\n" name in
  let ocaml_decls = declarations_to_ocaml_string ds in
  let s = if !hasRequire then ""
          else "let require = true\n"
  in
  let s = if !hasAssertion then s
          else (s ^ "let assertion = fun _ _ -> None\n")
  in
  Printf.sprintf "%s %s %s end\n %s" header ocaml_decls s (set_entry name)

let compile_ocaml name ds =
  let program = generate_ocaml name ds in
  Printf.printf "%s" program
