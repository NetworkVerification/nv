(** Compiles an NV program to an OCaml program*)
open Nv_lang
open Nv_utils
open PrimitiveCollections
open Syntax
open Nv_datastructures
open BddMap
open CompileBDDs

(** Translating NV records to OCaml records (type or values depending on f)*)
let record_to_ocaml_record
      (sep: string)
      (f : 'a -> string)
      (map : 'a StringMap.t)
  : string
  =
  let entries =
    StringMap.fold
      (fun l e acc ->
         Printf.sprintf "%s%s %s %s;" acc l sep (f e)
      )
      map ""
  in
  Printf.sprintf "{ %s }" entries

(** Keeps track of the tuple-sizes used throughout the nv program *)
let record_table = ref IntSet.empty

let proj_rec i n =
  record_table := IntSet.add n !record_table;
  Printf.sprintf "p%d__%d" i n

(* don't call with a negative n...*)
let rec fold_int (f: int -> 'a -> 'a) acc n =
  if (n = 0) then
    acc
  else
    fold_int f (f n acc) (n-1)

(** For each tuple of size n creates a corresponding record*)
let build_record_type n =
  let lst = BatList.init n (fun i -> i) in
  let type_vars =
    Collections.printList (fun i -> Printf.sprintf "'a%d" i) lst "(" ", " ")"
  in
  let proj_vars =
    Collections.printList (fun i -> Printf.sprintf "p%d__%d : 'a%d" i n i) lst "{" "; " "}"
  in
    Printf.sprintf "%s tup__%d = %s" type_vars n proj_vars

let build_record_types () =
  let lst = IntSet.to_list !record_table in
    Collections.printList (fun n -> build_record_type n) lst  "type " "\n and " "\n"

let build_proj_func n =
  let lst = BatList.init n (fun i -> i) in
    Collections.printList
      (fun i -> Printf.sprintf "| \"p%d__%d\" -> Obj.magic (fun x -> x.p%d__%d)" i n i n)
      lst  "" "\n" "\n"

(** Builds a table (function) that maps record projector names to the respective
   functions *)
let build_proj_funcs () =
  let branches =
    IntSet.fold (fun n acc -> Printf.sprintf "%s%s" (build_proj_func n) acc) !record_table ""
  in
  Printf.sprintf "let record_fns s = match s with \n\
                  %s" branches


(*TODO: string comparisons are more expensive than integer comparisons. In the
   future make an indirection on the matching for constructors and projections
*)
let build_constructor n =
  let lst = BatList.init n (fun i -> i) in
  let fun_args =
    Collections.printList (fun i -> Printf.sprintf "p%d__%d" i n) lst ("fun ") (" ") (" -> ")
  in
  let fun_body =
    Collections.printList (fun i -> Printf.sprintf "p%d__%d" i n) lst  ("{") ("; ") ("}\n")
  in
  Printf.sprintf "| \"%s\" -> Obj.magic (%s%s)" (string_of_int n) fun_args fun_body

(** Builds a table (function) that maps each record to a function that takes as
   arguments a value for each of its fields and creates the record*)
let build_constructors () =
  let branches =
    IntSet.fold (fun n acc -> Printf.sprintf "%s%s" (build_constructor n) acc) !record_table ""
  in
  Printf.sprintf "let record_cnstrs s = match s with \n\
                  %s" branches


let is_keyword_op op =
  match op with
  | And | Or | Not | UAdd _ | USub _ | Eq | ULess _ | ULeq _ | MGet | NLess | NLeq -> false
  | MCreate | MSet | MMap | MMerge | MMapFilter | AtMost _ -> true

let is_map_op op =
  match op with
    | MCreate | MGet | MSet | MMap | MMapFilter | MMerge -> true
    | And | Or | Not | UAdd _ | USub _ | Eq | ULess _ | ULeq _ | AtMost _ | NLess | NLeq | TGet _ | TSet _ -> false

(** Translating NV operators to OCaml operators*)
let op_to_ocaml_string op =
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "not"
  | UAdd _ -> "+"
  | USub _ -> "-"
  | Eq -> "="
  | ULess _ -> "<"
  | ULeq _ -> "<="
  | NLess -> "<"
  | NLeq -> "<="
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge -> failwith "Map ops are handled elsewhere"
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
    let n = BatList.length ps in
    Collections.printListi (fun i p -> Printf.sprintf "%s = %s" (proj_rec i n)
                               (pattern_to_ocaml_string p)) ps "{" "; "  "}"
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
  | TVar {contents= Unbound _ } -> failwith "unbound var"
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
    let n = BatList.length ts in
    let tup_typ = Printf.sprintf ") tup__%d" n in
      (*TODO:FIXME to apply types to record type.Did I fix that? not sure what I meant...*)
      Collections.printList (fun ty -> Printf.sprintf "%s" (ty_to_ocaml_string ty))
        ts "(" "," tup_typ
  | TOption t ->
     Printf.sprintf "(%s) option"
       (ty_to_ocaml_string t)
  | TMap _ ->
    Printf.sprintf "NativeBdd.t"
  | TRecord map ->
    record_to_ocaml_record ":" ty_to_ocaml_string map


let rec ty_to_nv_string ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, _) -> "TUnit"
      | Link t ->
        Printf.sprintf "%s" (ty_to_nv_string t))
  | QVar name -> failwith "QVar in compiler"
  | TBool -> "TBool"
  | TInt n -> Printf.sprintf "TInt %d" n
  | TArrow (ty1, ty2) ->
    Printf.sprintf "TArrow (%s,%s)" (ty_to_nv_string ty1) (ty_to_nv_string ty2)
  | TTuple ts ->
    let str = Collections.printList (fun ty -> ty_to_nv_string ty) ts "[" ";" "]" in
    Printf.sprintf "TTuple %s" str
  | TOption t -> Printf.sprintf "TOption (%s)" (ty_to_nv_string t)
  | TMap (ty1, ty2) ->
    Printf.sprintf "TMap (%s,%s)" (ty_to_nv_string ty1) (ty_to_nv_string ty2)
  | TRecord map ->
    let smap = PrimitiveCollections.StringMap.fold (fun k v acc ->
        let vs = ty_to_nv_string v in
        "PrimitiveCollections.StringMap.add \"%s\" (%s) (%s)" k vs acc
      ) map "StringMap.empty" in
    let record_type = Printf.sprintf "let record_type_%d = TRecord "
    failwith "not doing for now"
  | TUnit -> "TUnit"
  | TNode -> "TNode"
  | TEdge -> "TEdge"

(** Returns an OCaml string that contains the hashconsed int of the function
   body and a tuple with the free variables that appear in the function. Used
   for caching BDD operations.
    NOTE: In general this is sound only if you inline, because we do not capture the environment
    of any called function.
*)
let getFuncCache (e: exp) : string =
   match e.e with
     | EFun f ->
       let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
       let free = Syntax.free seen f.body in
       let closure = BatInnerIO.output_string () in
         BatSet.PSet.print ~first:"(" ~sep:"," ~last:")"
           (fun out x -> BatInnerIO.write_string out (Var.name x))
           closure free;
         Printf.sprintf "(%d, %s)" f.body.etag (BatInnerIO.close_out closure)
     | _ -> failwith "Expected a function"


(** Translating NV values and expressions to OCaml*)
let rec value_to_ocaml_string v =
  match v.v with
  | VUnit -> "()"
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> string_of_int (Integer.to_int i)
  | VMap _ ->
     failwith "Maps don't have values (I think)"
  | VTuple vs ->
    let n = BatList.length vs in
      Collections.printListi (fun i v -> Printf.sprintf "%s = %s" (proj_rec i n)
                                 (value_to_ocaml_string v)) vs "{" "; " "}"
  | VOption None ->
     "None"
  | VOption (Some v) ->
     Printf.sprintf "(Some %s)" (value_to_ocaml_string v)
  | VClosure _ -> failwith "Closures shouldn't appear here."
  | VRecord map ->
     record_to_ocaml_record "=" value_to_ocaml_string map
  | VNode n -> string_of_int n
  | VEdge (n1, n2) -> Printf.sprintf "(%d, %d)" n1 n2

and exp_to_ocaml_string e =
    match e.e with
    | EVar x -> Var.name x
    | EVal v -> value_to_ocaml_string v
    | EOp (op, es) when is_map_op op ->
      map_to_ocaml_string op es (OCamlUtils.oget e.ety)
    | EOp (op, es) -> op_args_to_ocaml_string op es
    | EFun f -> func_to_ocaml_string f
    | EApp (e1, e2) ->
       Printf.sprintf "(%s) (%s)"
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
      let n = BatList.length es in
        Collections.printListi (fun i e -> Printf.sprintf "%s = %s" (proj_rec i n)
                                   (exp_to_ocaml_string e)) es "{" "; " "}"
    | ESome e ->
       Printf.sprintf "Some (%s)" (exp_to_ocaml_string e)
    | EMatch (e1, bs) ->
       Printf.sprintf "(match %s with \n %s)"
         (exp_to_ocaml_string e1)
         (Collections.printList branch_to_ocaml_string
            (branchToList bs) "" "" "")
    | ETy (e, _) -> exp_to_ocaml_string e
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
         (op_to_ocaml_string op) (exp_to_ocaml_string e2)
    | _ -> failwith "Should be a keyword op"

and func_to_ocaml_string f =
  Printf.sprintf "(fun %s -> %s)" (Var.name f.arg) (exp_to_ocaml_string f.body)
  (* Printf.sprintf "(fun (%s : %s) -> %s)" (Var.name f.arg) (ty_to_ocaml_string (OCamlUtils.oget f.argty)) (exp_to_ocaml_string f.body) *)

and branch_to_ocaml_string (p, e) =
  Printf.sprintf "| %s -> %s\n"
    (pattern_to_ocaml_string p)
    (exp_to_ocaml_string e)

(* BDD based maps *)
and map_to_ocaml_string op es ty =
  match op with
    | MCreate ->
      (match ty with
        | TMap (kty,vty) ->
          Printf.sprintf "NativeBdd.create record_fns ~key_ty:(%s) ~val_ty:(%s) %s"
            (PrintingRaw.show_ty kty) (PrintingRaw.show_ty vty) (exp_to_ocaml_string (BatList.hd es))
        | _ -> failwith "Wrong type for map operation")
    | MSet ->
      (match es with
        | [e1;e2;e3] ->
          Printf.sprintf "(NativeBdd.update record_fns (%s) (%s) (%s))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments to MSet operation")
    | MGet ->
      (match es with
        | [e1;e2] ->
          Printf.sprintf "(NativeBdd.find record_cnstrs record_fns (%s) (%s))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
        | _ -> failwith "Wrong number of arguments to MGet operation")
    | MMap ->
      (match es with
        | [e1;e2] ->
          (match OCamlUtils.oget e1.ety with
           | TArrow (_, newty) ->
             (* Get e1's hashcons and closure *)
              let op_key = getFuncCache e1 in
              (*FIXME: this needs to be fresh, to avoid the case where it is
                 used inside e1 but our separator is not OCaml friendly*)
              let op_key_var = "op_key" in
              (*need the Obj.magic to op_key_var arg here because tuple may have
                 different type/size depending on the free vars*)
              Printf.sprintf "(let %s = %s in \n\
                               NativeBdd.map record_cnstrs record_fns (Obj.magic %s) (%s) (%s) (%s))"
                op_key_var op_key op_key_var (PrintingRaw.show_ty newty)
                (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
            | _ -> failwith "Wrong type for function argument")
        | _ -> failwith "Wrong number of arguments to map operation")
    | MMerge ->
      (match es with
        | (e1 :: e2 :: e3 :: rest) ->
          let op_key = getFuncCache e1 in
          let op_key_var = "op_key" in
          let opt = match rest with
            | [el0; el1; er0; er1] ->
              Printf.sprintf "~opt:(Obj.magic (Some (%s,%s,%s,%s)))" (exp_to_ocaml_string el0) (exp_to_ocaml_string el1)
                (exp_to_ocaml_string er0) (exp_to_ocaml_string er1)
            | _ -> ""
          in
          Printf.sprintf "(let %s = %s in \n\
                          NativeBdd.merge record_cnstrs record_fns %s (Obj.magic %s) (%s) (%s) (%s))"
            op_key_var op_key opt op_key_var (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments for merge operation")
    | MMapFilter ->
      (match es with
       | [pred; f; m] ->
         let pred =
           match pred.e with
           | EFun f -> f
           | _ -> failwith "predicate is not syntactically a function, cannot compile"
         in
         (* NOTE: for now considering that pred is closed (no free variables), as in the interpreter. FIXME. *)
         let bdd_id =
           match Collections.ExpMap.Exceptionless.find pred.body !bddfunc_cache with
           | None ->
             let bddf = BddFunc.create_value (OCamlUtils.oget pred.argty) in
             let env = Env.update Env.empty pred.arg bddf in
             let bddf = BddFunc.eval env pred.body in
             (match bddf with
              | BBool bdd ->
                let mtbdd = BddFunc.wrap_mtbdd bdd in
                let id = fresh_bdd_id () in
                bddfunc_cache :=
                  Collections.ExpMap.add pred.body (mtbdd, id) !bddfunc_cache ;
                id
              | _ -> failwith "A boolean bdd was expected but something went wrong")
           | Some (_, id) -> id
         in
         (match OCamlUtils.oget f.ety with
           | TArrow (_, newty) ->
             (* Get e1's hashcons and closure *)
              let op_key = getFuncCache f in
              (*FIXME: this needs to be fresh, to avoid the case where it is used
                 inside f but our separator is not OCaml friendly*)
              let op_key_var = "op_key" in
              (*need the Obj.magic to op_key_var arg here because tuple may
                   have different type/size depending on the free vars*)
              Printf.sprintf "(let %s = %s in \n\
                               NativeBdd.mapIf record_cnstrs record_fns %d (Obj.magic %s) (%s) (%s) (%s))"
                op_key_var op_key (*first let*)
                bdd_id op_key_var (PrintingRaw.show_ty newty)
                (exp_to_ocaml_string f) (exp_to_ocaml_string m)
            | _ -> failwith "Wrong type for function argument")
       | _ -> failwith "Wrong number of arguments to mapIf operation")
    | _ -> failwith "Not yet implemented"

(* BatMap maps*)
(*and map_to_ocaml_string op es ty =
  match op with
    | MCreate ->
      Printf.sprintf "BatMap.empty"
    | MSet ->
      (match es with
        | [e1;e2;e3] ->
          Printf.sprintf "(BatMap.add (%s) (%s) (%s))"
            (exp_to_ocaml_string e2)
            (exp_to_ocaml_string e3) (exp_to_ocaml_string e1)
        | _ -> failwith "Wrong number of arguments for set operation")
    | MGet ->
      (match es with
        | [e1;e2] ->
          Printf.sprintf "(BatMap.find (%s) (%s))"
            (exp_to_ocaml_string e2) (exp_to_ocaml_string e1)
        | _ -> failwith "Wrong number of arguments for get operation")
    | MMap ->
      (match es with
        | [e1;e2] ->
          Printf.sprintf "(BatMap.map (%s) (%s))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
        | _ -> failwith "Wrong number of arguments for map operation")
    | MMerge ->
      (match es with
        | (e1 :: e2 :: e3 :: _) ->
          let ty2 = match OCamlUtils.oget e2.ety |> get_inner_type  with
            | TMap (_, vty) -> vty
            | x -> Printf.printf "%s\n" (Printing.ty_to_string x); failwith "expected a map"
          in
          let ty3 = match OCamlUtils.oget e3.ety |> get_inner_type with
            | TMap (_, vty) -> vty
            | _ -> failwith "expected a map"
          in
          Printf.sprintf "(BatMap.merge (fun _ v1 v2 -> \n \
                                      let v1 = match v1 with | Some v1 -> v1 | None -> %s in\n\
                                      let v2 = match v2 with | Some v2 -> v2 | None -> %s in\n\
                          Some (%s v1 v2)) (%s) (%s))"
            (value_to_ocaml_string (default_value ty2)) (value_to_ocaml_string (default_value ty3))
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments for merge operation")
    | MMapFilter ->
      (match es with
        | [e1;e2;e3] ->
          Printf.sprintf "(BatMap.mapi (fun k v -> if (%s k) then (%s v) else v) (%s))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments for mapIf operation")
*)


(** Translate something of type [Syntax.network] to an OCaml program*)
let compile_net net =
  let utys_s =
    Collections.printList
      (fun (x, ty) -> Printf.sprintf "type %s = %s" (Var.name x) (ty_to_ocaml_string ty))
      net.utys "" "\n" "\n\n"
  in
  let attr_s = Printf.sprintf "type attribute = %s\n\n" (ty_to_ocaml_string net.attr_type) in

  (* Handling of symbolic values*)
  let symbs_s =
    Collections.printListi
      (fun i (x, _) ->
        Printf.sprintf "let %s = S.get_symb record_cnstrs record_fns %d" (Var.name x) i) net.symbolics "" "\n" "\n\n"
  in
  let requires_s =
    match net.requires with
    | [] -> ""
    | rs ->
       Collections.printList (fun e -> Printf.sprintf "let () = assert %s" (exp_to_ocaml_string e))
         rs "" "\n\n" "\n\n"
  in
  let defs_s =
    Collections.printList
      (fun (x, _, e) ->
         Printf.sprintf "let %s = %s"
           (Var.name x) (exp_to_ocaml_string e))
      net.defs "" "\n\n" "\n\n"
  in
  let init_s = Printf.sprintf "let init = %s\n\n" (exp_to_ocaml_string net.init) in
  let trans_s = Printf.sprintf "let trans = %s\n\n" (exp_to_ocaml_string net.trans) in
  let merge_s = Printf.sprintf "let merge = %s\n\n" (exp_to_ocaml_string net.merge) in
  let assert_s =
    match net.assertion with
    | None ->
       "let assertion = None\n"
    | Some e ->
       Printf.sprintf "let assertion = Some (%s)\n" (exp_to_ocaml_string e)
  in
  let tuple_s = build_record_types () in
  let record_fns = build_proj_funcs () in
  let record_cnstrs = build_constructors () in
  Printf.sprintf "%s %s %s %s %s %s %s %s %s %s %s %s"
    tuple_s utys_s attr_s record_cnstrs record_fns symbs_s defs_s init_s trans_s merge_s requires_s assert_s

let set_entry (name: string) =
  Printf.sprintf "let () = SrpNative.srp := Some (module %s:SrpNative.EnrichedSRPSig)" name

let generate_ocaml (name : string) net =
  let header = Printf.sprintf "open Nv_datastructures\n open Nv_lang\n open Syntax\nopen Nv_compile\n\n \
                               module %s (B: CompileBDDs.BDDs) (S: Symbolics.PackedSymbolics): SrpNative.NATIVE_SRP = struct\n" name in
  let ocaml_decls = Profile.time_profile "Compilation Time" (fun () -> compile_net net) in
  Printf.sprintf "%s %s end\n %s" header ocaml_decls (set_entry name)


(* Create the plugin that we will dynamically load later, do not print warnings
   do not treat them as errors*)
let build_dune_file name =
  Printf.sprintf
    "(library \n \
     (name %s_plugin) \n \
     (public_name %s.plugin)\n \
     (modes native)\n \
     (libraries nv_lib))\n \
     (env\n \
     (dev\n \
     (flags (:standard -warn-error -A -w -a))))" name name

let build_project_file name =
  Printf.sprintf "(lang dune 1.10)\n (name %s)" name

let build_opam_file name =
  Printf.sprintf "name: \"%s-plugin\"\n \
                  build: [ \"dune\" \"build\" \"-p\" name \"-j\" jobs ]" name

let print_file file s =
  let oc = open_out_gen [Open_rdonly; Open_wronly; Open_creat; Open_trunc] 0o777 file in
    Printf.fprintf oc "%s" s;
    close_out oc

(* TODO: should use srcdir env. Or even better get rid of source all together,
   find out how to generate and link cmxs files from build directory*)
let compile_command_ocaml name =
  let dune = build_dune_file name in
  let project = build_project_file name in
  let opam = build_opam_file name in
    print_file "dune" dune;
    print_file "dune-project" project;
    print_file (name ^ ".opam") opam;
    Sys.command "dune build; dune install"

    (* Sys.command "dune build command >>/dev/null 2>&1; sudo dune install command >>/dev/null 2>&1" *)

let compile_ocaml name net =
  let basename = Filename.basename name in
  let program = generate_ocaml basename net in
  let src_dir =
    try (Sys.getenv "NV_BUILD") ^ name
    with Not_found -> failwith "To use compiler, please set environment variable NV_BUILD to the directory to be used (use something different than NV's directory)"
  in
    (try Unix.mkdir src_dir (0o777) with
      | _ -> ());
    Unix.chdir src_dir;
    Printf.printf "Current dir: %s\n" (Unix.getcwd ());
    print_file (name ^ ".ml") program;
  compile_command_ocaml name
