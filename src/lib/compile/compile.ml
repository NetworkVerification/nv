(** Compiles an NV program to an OCaml program*)
open Nv_lang
open Nv_utils
open PrimitiveCollections
open Syntax
open Nv_datastructures
open BddMap
open CompileBDDs

let varname x = Var.to_string_delim "___" x

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
      (* (fun i -> Printf.sprintf "| \"p%d__%d\" -> Obj.magic (fun x -> x.p%d__%d)" i n i n) *)
      (fun i -> Printf.sprintf "| (%d,%d) -> Obj.magic (fun x -> x.p%d__%d)" i n i n)
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
    Collections.printList (fun i -> Printf.sprintf "p%d__%d" i n) lst  ("{") ("; ") ("}")
  in
  Printf.sprintf "| %d -> Obj.magic (%s%s)\n" n fun_args fun_body

(** Builds a table (function) that maps each record to a function that takes as
   arguments a value for each of its fields and creates the record*)
let build_constructors () =
  let branches =
    IntSet.fold (fun n acc -> Printf.sprintf "%s%s" (build_constructor n) acc) !record_table ""
  in
  Printf.sprintf "let record_cnstrs s = match s with \n\
                  %s" branches

let is_map_op op =
  match op with
    | MCreate | MGet | MSet | MMap | MMapFilter | MMerge | MMapIte | MFoldEdge | MFoldNode -> true
    | And | Or | Not | UAdd _ | USub _ | UAnd _ | Eq | ULess _ | ULeq _ | AtMost _ | NLess | NLeq | TGet _ | TSet _ -> false

(** Translating NV operators to OCaml operators*)
let op_to_ocaml_string op =
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "not"
  | UAdd _ -> "+"
  | USub _ -> "-"
  | UAnd _ -> "land"
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
  | MMapIte
  | MFoldEdge
  | MFoldNode
  | MMerge -> failwith "Map ops are handled elsewhere"
  | AtMost _ -> failwith "todo: atmost"
  | TGet _
  | TSet _ -> failwith "Todo: TGet/TSet"

(** Translating NV patterns to OCaml patterns*)
let rec pattern_to_ocaml_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> varname x
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
     Printf.sprintf "'%s" (varname name)
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
    record_table := IntSet.add n !record_table; (*add type to record table*)
    let tup_typ = Printf.sprintf ") tup__%d" n in
      Collections.printList (fun ty -> Printf.sprintf "%s" (ty_to_ocaml_string ty))
        ts "(" "," tup_typ
  | TOption t ->
     Printf.sprintf "(%s) option"
       (ty_to_ocaml_string t)
  | TMap (kty,vty) ->
    ignore (ty_to_ocaml_string kty); (* NOTE: doing this for the side effect in the case of TTuple, i.e. adding to record_table *)
    ignore (ty_to_ocaml_string vty);
    Printf.sprintf "CompileBDDs.t"
  | TRecord map ->
    record_to_ocaml_record ":" ty_to_ocaml_string map

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
       let freeList = BatSet.PSet.to_list free in
       let closure =
         Collections.printList (fun x -> varname x) freeList "(" "," ")"
       in
       Printf.sprintf "(%d, %s)" (get_fresh_exp_id f.body) closure
       (*FIXME: annoying BatSet printing outputs null character at the end so I am using the code above*)
       (* let closure = BatIO.output_string () in
        *   BatSet.PSet.print ~first:"(" ~sep:"," ~last:")"
        *     (fun out x -> BatIO.write_string out (varname x))
        *     closure free;
        *   Printf.sprintf "(%d, %s)" f.body.etag (BatInnerIO.close_out closure) *)
     | _ -> (*assume there are no free variables, but this needs to be fixed: always inline*)
       Printf.sprintf "(%d, ())" (get_fresh_exp_id e)


(** Function walking through an NV expression to record tuple types.
    This is done by the compiler on the go, but not for
    operations like mapIte because these expressions are never translated to OCaml, so we manually have to do it.
   Expect this function to be called somewhere in the MapIte case.*)

let rec track_tuples_exp e =
  match e.e with
  | ETuple es ->
    let n = BatList.length es in
    List.iteri (fun i _ -> ignore(proj_rec i n)) es
  | EMatch (_, bs) ->
    List.iter (fun (p,_) -> track_tuples_pattern p) (branchToList bs)
  | EVal v ->
    (match v.v with
     | VTuple vs ->
       let n = BatList.length vs in
       List.iteri (fun i _ -> ignore(proj_rec i n)) vs
     | _ -> ())
  | EOp (TGet (sz, lo, _), _) ->
    ignore(proj_rec lo sz)
  | EOp (TSet (sz, lo, _), _) ->
    ignore(proj_rec lo sz)
  | EVar _ | EFun _ | EApp _ | ELet _ | ESome _ | ETy _ | ERecord _ | EProject _ | EIf _ | EOp _ -> ()

and track_tuples_pattern p =
  match p with
  | PTuple ps ->
    let n = BatList.length ps in
    List.iteri (fun i p -> ignore(proj_rec i n); track_tuples_pattern p) ps
  | POption (Some p) -> track_tuples_pattern p
  (* records are already unrolled  *)
  | POption None | PWild | PVar _ | PUnit | PBool _ | PInt _ | PRecord _ | PNode _ | PEdge _ -> ()


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
    | EVar x -> varname x
    | EVal v -> value_to_ocaml_string v
    | EOp (op, es) when is_map_op op ->
      map_to_ocaml_string op es (OCamlUtils.oget e.ety)
    | EOp (TGet (sz, lo, hi), [e]) ->
      (if (lo != hi) then failwith "Can only handle TGet from one slot");
      let proj = proj_rec lo sz in
      Printf.sprintf "(%s).%s" (exp_to_ocaml_string e) proj
    | EOp (TSet (sz, lo, hi), [e1;e2]) ->
      (if (lo != hi) then failwith "Can only handle TSet from one slot");
      let proj = proj_rec lo sz in
      Printf.sprintf "{%s with %s=%s}" (exp_to_ocaml_string e1) proj (exp_to_ocaml_string e2)
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
         (varname x)
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
  match es with
  | [] -> failwith "Empty operand list"
  | [e1] -> Printf.sprintf "(%s %s)" (op_to_ocaml_string op) (exp_to_ocaml_string e1)
  | [e1; e2] ->
    Printf.sprintf "(%s %s %s)" (exp_to_ocaml_string e1)
      (op_to_ocaml_string op) (exp_to_ocaml_string e2)
  | _ -> failwith "Should be a keyword op"

and func_to_ocaml_string f =
  Printf.sprintf "(fun %s -> %s)" (varname f.arg) (exp_to_ocaml_string f.body)
  (* Printf.sprintf "(fun (%s : %s) -> %s)" (varname f.arg) (ty_to_ocaml_string (OCamlUtils.oget f.argty)) (exp_to_ocaml_string f.body) *)

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
          Printf.sprintf "NativeBdd.create ~key_ty_id:(%d) ~val_ty_id:(%d) (%s)"
            (get_fresh_type_id kty) (get_fresh_type_id vty) (exp_to_ocaml_string (BatList.hd es))
        | _ -> failwith "Wrong type for map operation")
    | MSet ->
      (match es with
        | [e1;e2;e3] ->
          Printf.sprintf "(NativeBdd.update (%d) (%s) (%s) (%s))"
            (get_fresh_type_id (OCamlUtils.oget e3.ety)) (exp_to_ocaml_string e1) (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments to MSet operation")
    | MGet ->
      (match es with
        | [e1;e2] ->
          Printf.sprintf "(NativeBdd.find %d (%s) (%s))"
            (get_fresh_type_id (OCamlUtils.oget e2.ety)) (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
        | _ -> failwith "Wrong number of arguments to MGet operation")
    | MMap ->
      (match es with
        | [e1;e2] ->
          (match get_inner_type (OCamlUtils.oget e1.ety) with
           | TArrow (_, newty) ->
             (* Get e1's hashcons and closure *)
              let op_key = getFuncCache e1 in
              (*FIXME: this needs to be fresh, to avoid the case where it is
                 used inside e1 but our separator is not OCaml friendly*)
              let op_key_var = "op_key" in
              (*need the Obj.magic to op_key_var arg here because tuple may have
                 different type/size depending on the free vars*)
              Printf.sprintf "(let %s = %s in \n \
                               NativeBdd.map (Obj.magic %s) (%d) (%s) (%s))"
                op_key_var op_key op_key_var (get_fresh_type_id newty)
                (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
            | _ -> failwith ("Wrong type for function argument" ^ (Printing.ty_to_string (OCamlUtils.oget e1.ety))))
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
                          NativeBdd.merge %s (Obj.magic %s) (%s) (%s) (%s))"
            op_key_var op_key opt op_key_var (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
        | _ -> failwith "Wrong number of arguments for merge operation")
    | MMapFilter ->
      (match es with
       | [pred; f; m] ->
         let pred_closure =
           match pred.e with
           | EFun predF ->
             (* Call track_tuples_exp to record any tuple types used in this predicate *)
             Visitors.iter_exp track_tuples_exp predF.body;
             let freeVars = Syntax.free_ty (BatSet.PSet.singleton ~cmp:Var.compare predF.arg) predF.body in
             let freeList = BatSet.PSet.to_list freeVars in
             Collections.printList (fun (x, ty) -> Printf.sprintf "(%s,%d)" (varname x) (get_fresh_type_id ty)) freeList "(" "," ")"
           | _ -> failwith "Predicate is not a function expression, try inlining"
         in
         let pred_id =
           match Collections.ExpMap.Exceptionless.find pred !pred_cache with
           | None ->
                let id = fresh_pred_id () in
                pred_cache :=
                  Collections.ExpMap.add pred id !pred_cache ;
                id
           | Some id -> id
         in
         (match get_inner_type (OCamlUtils.oget f.ety) with
           | TArrow (_, newty) ->
             (* Get e1's hashcons and closure *)
              let op_key = getFuncCache f in
              let op_key_var = "op_key" in
              let pred_key = Printf.sprintf "(%d, %s)" pred_id pred_closure in
              (*need the Obj.magic to op_key_var arg here because tuple may
                   have different type/size depending on the free vars*)
              Printf.sprintf "(let %s = %s in \n\
                               let pred_key = %s in \n\
                               NativeBdd.mapIf (Obj.magic pred_key) (Obj.magic %s) (%d) (%s) (%s))"
                op_key_var op_key (*first let*)
                pred_key op_key_var (get_fresh_type_id newty)
                (exp_to_ocaml_string f) (exp_to_ocaml_string m)
            | _ -> failwith ("Wrong type for function argument" ^ (Printing.ty_to_string (OCamlUtils.oget f.ety))))
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


(** Translate a declaration to an OCaml program*)
let symbolic_counter = ref 0
let compile_decl decl =
  match decl with
    | DUserTy (x, ty) ->
      Printf.sprintf "type %s = %s" (varname x) (ty_to_ocaml_string ty)
    | DSymbolic (x, _) ->
      let s = Printf.sprintf "let %s = S.get_symb record_cnstrs record_fns %d"
          (varname x) !symbolic_counter
      in
        incr symbolic_counter;
        s
    | DLet (x, _ , e) ->
      Printf.sprintf "let %s = %s" (varname x) (exp_to_ocaml_string e)
    | DRequire e ->
      Printf.sprintf "let () = assert %s" (exp_to_ocaml_string e)
    | DAssert e ->
      Printf.sprintf "let () = assert %s" (exp_to_ocaml_string e)
    | DSolve solve ->
      begin
        match solve.var_names.e with
          | EVar x ->
            (match solve.aty with
              | None -> failwith "cannot solve without an attribute type"
              | Some attr -> (*NOTE: this is just the attribute type, not including the map from nodes to attributes *)
                ignore (get_fresh_type_id TNode); (*need to register node types manually! *)
                let attr_id = get_fresh_type_id attr in
                  Printf.sprintf "let %s = SIM.simulate_solve (%d) (\"%s\") (%s) (%s) (%s)"
                    (varname x) attr_id (Var.name x) (exp_to_ocaml_string solve.init)
                    (exp_to_ocaml_string solve.trans) (exp_to_ocaml_string solve.merge)
              | _ -> failwith "Expected a map type for attributes")
        | _ -> failwith "Not implemented" (* Only happens if we did map unrolling *)
      end
    | DNodes _ | DEdges _ | DPartition _ | DInterface _ ->
      ""


let compile_decls decls =
  let s = Collections.printList compile_decl decls "" "\n\n" "\n" in
  let tuple_s = build_record_types () in
  let record_fns = build_proj_funcs () in
  let record_cnstrs = build_constructors () in
  let embeddings = "let _ = Embeddings.build_embed_cache record_fns\n \
                    let _ = Embeddings.build_unembed_cache record_cnstrs record_fns\n\n"
  in
  Printf.sprintf "%s %s %s %s %s"
    tuple_s record_cnstrs record_fns embeddings s

let set_entry (name: string) =
  Printf.sprintf "let () = SrpNative.srp := Some (module %s:SrpNative.CompleteSRPSig)" name

let generate_ocaml (name : string) decls =
  let header =
    Printf.sprintf "open Nv_datastructures\n open Nv_lang\n\
                    open Syntax\nopen Nv_compile\n\n\
                    module %s (S: Symbolics.PackedSymbolics) (SIM:SrpNative.SrpSimulationSig): SrpNative.NATIVE_SRP \
                               = struct\n" name in
  let ocaml_decls = Profile.time_profile "Compilation Time" (fun () -> compile_decls decls) in
    Printf.sprintf "%s %s end\n %s" header ocaml_decls (set_entry name)


(* Create the plugin that we will dynamically load later, do not print warnings
   do not treat them as errors*)
let build_dune_file name =
  Printf.sprintf
    "(library \n \
     (name %s_plugin) \n \
     (public_name %s.plugin)\n \
     (modes native)\n \
     (libraries nv))\n \
     (env\n \
     (dev\n \
     (flags (:standard -warn-error -A -w -a -opaque))))" name name

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
    with Not_found -> failwith "To use compiler, please set environment variable NV_BUILD to a directory in which to generate build files. Use something outside the nv directory."
  in
  (try Unix.mkdir src_dir (0o777) with
   | _ -> ());
  let curdir = Sys.getcwd () in
    Unix.chdir src_dir;
    print_file (name ^ ".ml") program;
    let ret = compile_command_ocaml name in
    Unix.chdir curdir;
    ret
