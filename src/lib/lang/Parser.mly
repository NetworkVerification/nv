%{
  open Syntax
  open Nv_datastructures
  open Collections
  open Batteries

  type user_type = Var.t (* name *) * ty (* type *)
  let user_types : user_type list ref = ref []

  let add_user_type (name : Var.t) (ty : ty) : unit =
    user_types := (name,ty)::!user_types

  let get_user_type (name : Var.t) : ty =
    match List.find_opt (fun (n,_) -> Var.equals name n) !user_types with
    | Some (_, ty) -> ty
    | None -> failwith @@ "Unknown user-defined type " ^ (Var.name name)

  let ensure_node_pattern p =
    match p with
    | PInt n -> PNode (Nv_datastructures.Integer.to_int n)
    | _ -> p

  let exp e span : exp = aexp (e, None, span)

  let value v span : value = avalue (v, None, span)

  let to_value v span : exp = exp (e_val (value v span)) span

  let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> exp e span
    | es -> exp (etuple es) span

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

  (* TODO: span not calculated correctly here? *)
  let rec make_fun params (body : exp) (body_span: Span.t) (span : Span.t) : exp =
    match params with
	| [] -> body
	| (x,tyopt)::rest ->
        let e = efun {arg=x; argty=tyopt; resty=None; body=make_fun rest body body_span body_span} in
        exp e span

  let local_let (id,params) body body_span span =
    (id, make_fun params body body_span span)

  let merge_identifier = "merge"
  let trans_identifier = "trans"
  let init_identifier = "init"
  let assert_identifier = "assert"
  (* partitioning identifiers *)
  let partition_identifier = "partition"
  let interface_identifier = "interface"

  let global_let (id,params) body body_span span =
    let e = make_fun params body body_span span in
    if Var.name id = merge_identifier then
      DMerge e
    else if Var.name id = trans_identifier then
      DTrans e
    else if Var.name id = init_identifier then
      DInit e
    else if Var.name id = assert_identifier then
      DAssert e
    (* partitioning cases *)
    else if Var.name id = partition_identifier then
      DPartition e
    else if Var.name id = interface_identifier then
      DInterface e
    (* end partitioning cases *)
    else
      DLet (id, None, e)

  let make_set exprs span =
    let tru = exp (e_val (value (vbool true) span)) span in
    let rec updates e exprs =
        match exprs with
        | [] -> e
        | expr :: tl ->
            let e = exp (eop MSet [e; expr; tru]) span in
            updates e tl
    in
    let e = exp (e_val (value (vbool false) span)) span in
    let e = exp (eop MCreate [e]) span in
    updates e exprs

  let find_record_type (lab : string) : 'a StringMap.t =
    let rec aux lst =
      match lst with
      | [] -> failwith @@ "No record type using label " ^ lab
      | (_, t) :: tl ->
        match t with
        | TRecord tmap ->
          if StringMap.mem lab tmap then tmap else aux tl
        | _ -> aux tl
    in
    aux !user_types

  (* Fill in a partial record specification, using the default provided for
     labels which do not already appear in the list *)
  let fill_record (lst : (Var.t * 'a) list) (default : Var.t -> 'a)
    : (Var.t * 'a) list
  =
    let record_type = find_record_type (List.hd lst |> fst |> Var.name) in
    (* FIXME: Strictly speaking, we should make sure that the elements of keys
       are a strict subset of the elements of record_type *)
    let keys = StringMap.keys record_type in
    BatEnum.fold
      (fun acc lab ->
        let lab = Var.create lab in
        match List.find_opt (fun (l,_) -> Var.equals l lab) lst with
        | None -> (lab, default lab) :: acc
        | Some elt -> elt :: acc
      ) [] keys

  let make_record_map (lst : (Var.t * 'a) list) : 'a StringMap.t =
    (* Ensure that no labels were used more than once *)
    let sorted =
      List.sort (fun (l1,_) (l2, _)-> Var.compare l1 l2) lst
    in
    let rec build_map map lst =
      match lst with
      | [] -> map
      | (l,x)::tl ->
        let l = Var.name l in
        if StringMap.mem l map
        then failwith @@ "Label used more than once in a record: " ^ l
        else build_map (StringMap.add l x map) tl
    in
    build_map StringMap.empty sorted

  let ip_to_dec b1 b2 b3 b4 =
    let b1 = Nv_datastructures.Integer.to_int b1 in
    let b2 = Nv_datastructures.Integer.to_int b2 in
    let b3 = Nv_datastructures.Integer.to_int b3 in
    let b4 = Nv_datastructures.Integer.to_int b4 in
    if (b1 > 255) || (b2 > 255) || (b3 > 255) || (b4 > 255) then
      failwith "Invalid ip address"
    else
      (b1 * 16777216) + (b2 * 65536) + (b3 * 256) + b4
      |> Integer.of_int

%}

%token <Nv_datastructures.Span.t * Nv_datastructures.Var.t> ID
%token <Nv_datastructures.Span.t * Nv_datastructures.Integer.t> NUM
%token <Nv_datastructures.Span.t * int> NODE
%token <Nv_datastructures.Span.t> AND
%token <Nv_datastructures.Span.t> OR
%token <Nv_datastructures.Span.t> NOT
%token <Nv_datastructures.Span.t> TRUE
%token <Nv_datastructures.Span.t> FALSE
%token <Nv_datastructures.Span.t * int> PLUS
%token <Nv_datastructures.Span.t * int> SUB
%token <Nv_datastructures.Span.t> EQ
%token <Nv_datastructures.Span.t * int> LESS
%token <Nv_datastructures.Span.t * int> GREATER
%token <Nv_datastructures.Span.t * int> LEQ
%token <Nv_datastructures.Span.t * int> GEQ
%token <Nv_datastructures.Span.t> NLESS
%token <Nv_datastructures.Span.t> NGREATER
%token <Nv_datastructures.Span.t> NLEQ
%token <Nv_datastructures.Span.t> NGEQ
%token <Nv_datastructures.Span.t> LET
%token <Nv_datastructures.Span.t> IN
%token <Nv_datastructures.Span.t> IF
%token <Nv_datastructures.Span.t> THEN
%token <Nv_datastructures.Span.t> ELSE
%token <Nv_datastructures.Span.t> FUN
%token <Nv_datastructures.Span.t> SOME
%token <Nv_datastructures.Span.t> NONE
%token <Nv_datastructures.Span.t> MATCH
%token <Nv_datastructures.Span.t> WITH
%token <Nv_datastructures.Span.t> BAR
%token <Nv_datastructures.Span.t> ARROW
%token <Nv_datastructures.Span.t> DOT
%token <Nv_datastructures.Span.t> SLASH
%token <Nv_datastructures.Span.t> SEMI
%token <Nv_datastructures.Span.t> LPAREN
%token <Nv_datastructures.Span.t> RPAREN
%token <Nv_datastructures.Span.t> LBRACKET
%token <Nv_datastructures.Span.t> RBRACKET
%token <Nv_datastructures.Span.t> LBRACE
%token <Nv_datastructures.Span.t> RBRACE
%token <Nv_datastructures.Span.t> COMMA
%token <Nv_datastructures.Span.t> TILDE
%token <Nv_datastructures.Span.t> UNDERSCORE
%token <Nv_datastructures.Span.t> CREATEMAP
%token <Nv_datastructures.Span.t> FOLDNODE
%token <Nv_datastructures.Span.t> FOLDEDGE
%token <Nv_datastructures.Span.t> MAP
%token <Nv_datastructures.Span.t> MAPIF
%token <Nv_datastructures.Span.t> MAPITE
%token <Nv_datastructures.Span.t> COMBINE
%token <Nv_datastructures.Span.t> TOPTION
%token <Nv_datastructures.Span.t> TDICT
%token <Nv_datastructures.Span.t> ATTRIBUTE
%token <Nv_datastructures.Span.t> TYPE
%token <Nv_datastructures.Span.t> COLON
%token <Nv_datastructures.Span.t> TBOOL
%token <Nv_datastructures.Span.t> TNODE
%token <Nv_datastructures.Span.t> TEDGE
%token <Nv_datastructures.Span.t * int> TINT
%token <Nv_datastructures.Span.t> EDGES
%token <Nv_datastructures.Span.t> NODES
%token <Nv_datastructures.Span.t> SYMBOLIC
%token <Nv_datastructures.Span.t> REQUIRE
%token <Nv_datastructures.Span.t> UNION
%token <Nv_datastructures.Span.t> INTER
%token <Nv_datastructures.Span.t> MINUS
%token <Nv_datastructures.Span.t> FILTER
%token <Nv_datastructures.Span.t> TSET

%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expreof
%type <Syntax.exp> expreof

%right ELSE IN     /* lowest precedence */
%right ARROW
%left AND OR
%nonassoc GEQ GREATER LEQ LESS EQ NLEQ NGEQ NLESS NGREATER
%left PLUS SUB UNION INTER MINUS
%right NOT
%right SOME
%nonassoc DOT
%left LBRACKET      /* highest precedence */

%%

ty:
   | ty ARROW ty                        { TArrow ($1,$3) }
   | TBOOL                              { TBool }
   | TNODE                              { TNode }
   | TEDGE                              { TEdge }
   | TINT                               { Syntax.TInt (snd $1) }
   | LPAREN tys RPAREN                  { if List.length $2 = 1 then List.hd $2 else TTuple $2 }
   | TOPTION LBRACKET ty RBRACKET       { TOption $3 }
   | TDICT LBRACKET ty COMMA ty RBRACKET{ TMap ($3,$5) }
   | TSET LBRACKET ty RBRACKET          { TMap ($3,TBool) }
   | LBRACE record_entry_tys RBRACE     { TRecord (make_record_map $2) }
   | ID                                 { get_user_type (snd $1) }
;

tys:
  | ty                                  { [$1] }
  | ty COMMA tys                        { $1::$3 }
;

record_entry_ty:
  | ID COLON ty                         { snd $1, $3 }
;

record_entry_tys:
  | record_entry_ty                       { [$1] }
  | record_entry_ty SEMI                  { [$1] }
  | record_entry_ty SEMI record_entry_tys { $1::$3 }

param:
   | ID                                 { (snd $1, None) }
   | LPAREN ID COLON ty RPAREN          { (snd $2, Some $4) }
;

params:
    | param                             { [$1] }
    | param params                      { $1::$2 }
;

letvars:
    | ID                                { (snd $1,[]) }
    | ID params                         { (snd $1, $2) }
;

component:
    | LET letvars EQ expr               { global_let $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | SYMBOLIC ID EQ expr               { DSymbolic (snd $2, Exp $4) }
    | SYMBOLIC ID COLON ty              { DSymbolic (snd $2, Ty $4) }
    | SYMBOLIC ID COLON ty EQ expr      { let ety = exp (ety $6 $4) $6.espan in
                                          DSymbolic (snd $2, Exp ety) }
    | REQUIRE expr                      { DRequire $2 }
    | LET EDGES EQ LBRACE RBRACE        { DEdges [] }
    | LET EDGES EQ LBRACE edges RBRACE  { DEdges $5 }
    | LET NODES EQ NUM                  { DNodes (Nv_datastructures.Integer.to_int (snd $4)) }
    | TYPE ATTRIBUTE EQ ty              { DATy $4 }
    | TYPE ID EQ ty                     { (add_user_type (snd $2) $4; DUserTy (snd $2, $4)) }

;

components:
    | component                         { [$1] }
    | component components              { $1 :: $2 }
;

record_entry_expr:
  | ID EQ expr                       { snd $1, $3 }
;

record_entry_exprs:
  | record_entry_expr                         { [$1] }
  | record_entry_expr SEMI                    { [$1] }
  | record_entry_expr SEMI record_entry_exprs { $1::$3 }

expreof:
    expr EOF    { $1 }
;

expr:
    | LET letvars EQ expr IN expr       { let span = (Span.extend $1 $6.espan) in
                                          let (id, e) = local_let $2 $4 $4.espan span in
                                          exp (elet id e $6) span }
    | LET LPAREN patterns RPAREN EQ expr IN expr
                                        { let p = tuple_pattern $3 in
                                          let e = ematch $6 (addBranch p $8 emptyBranch) in
                                          let span = Span.extend $1 $8.espan in
                                          exp e span }
    | IF expr THEN expr ELSE expr       { exp (eif $2 $4 $6) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (ematch $2 $4) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | FOLDNODE exprsspace               { exp (eop MFoldNode $2) $1 }
    | FOLDEDGE exprsspace               { exp (eop MFoldEdge $2) $1 }
    | MAP exprsspace                    { exp (eop MMap $2) $1 }
    | MAPIF exprsspace                  { exp (eop MMapFilter $2) $1 }
    | MAPITE exprsspace                 { exp (eop MMapIte $2) $1 }
    | COMBINE exprsspace                { exp (eop MMerge $2) $1 }
    | CREATEMAP exprsspace              { exp (eop MCreate $2) $1 }
    | SOME expr                         { exp (esome $2) (Span.extend $1 $2.espan) }
    | NOT expr                          { exp (eop Not [$2]) (Span.extend $1 $2.espan) }
    | expr AND expr                     { exp (eop And [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr OR expr                      { exp (eop Or [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr PLUS expr                    { exp (eop (UAdd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr SUB expr                     { exp (eop (USub (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr EQ expr                      { exp (eop Eq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr LESS expr                    { exp (eop (ULess (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GREATER expr                 { exp (eop (ULess (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr LEQ expr                     { exp (eop (ULeq (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GEQ expr                     { exp (eop (ULeq (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr NLESS expr                   { exp (eop NLess [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGREATER expr                { exp (eop NLess [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr NLEQ expr                    { exp (eop NLeq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGEQ expr                    { exp (eop NLeq [$3;$1]) (Span.extend $1.espan $3.espan) }
    | LPAREN expr COLON ty RPAREN       { exp (ety $2 $4) (Span.extend $1 $5) }
    | expr LBRACKET expr RBRACKET               { exp (eop MGet [$1;$3]) (Span.extend $1.espan $4) }
    | expr LBRACKET expr COLON EQ expr RBRACKET { exp (eop MSet [$1;$3;$6]) (Span.extend $1.espan $7) }
    | expr UNION expr                   { let el0 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool true)))) $2 in
                                          let er0 = el0 in
                                          let er1 = el1 in
                                          let varx = Nv_datastructures.Var.fresh "x" in
                                          let vary = Nv_datastructures.Var.fresh "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop Or [x;y]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | expr INTER expr                   { let el0 = exp (e_val (voption (Some (vbool true)))) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er0 = el0 in
                                          let er1 = el1 in
                                          let varx = Nv_datastructures.Var.create "x" in
                                          let vary = Nv_datastructures.Var.create "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop And [x;y]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | expr MINUS expr                   { let el0 = exp (e_val (voption None)) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er0 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er1 = el0 in
                                          let varx = Nv_datastructures.Var.create "x" in
                                          let vary = Nv_datastructures.Var.create "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop Not [y]) $2 in
                                          let e = exp (eop And [x;e]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | FILTER exprsspace                 { let span = $1 in
                                          let vark = Nv_datastructures.Var.create "k" in
                                          let e = exp (e_val (value (vbool false) span)) span in
                                          let e = exp (efun {arg=vark;argty=None;resty=None;body=e}) span in
                                          let args = match $2 with hd :: tl -> hd::e::tl | _ -> [e] in
                                          exp (eop MMapFilter args) $1 }
    | expr DOT ID                       { exp (eproject $1 (Nv_datastructures.Var.name (snd $3))) (Span.extend ($1.espan) (fst $3)) }
    | LBRACE record_entry_exprs RBRACE  { exp (erecord (make_record_map $2)) (Span.extend $1 $3) }
    | LBRACE expr WITH record_entry_exprs RBRACE {
                                          let mk_project v =
                                          exp (eproject $2 (Nv_datastructures.Var.name v)) (Span.extend $1 $3) in
                                          let lst = fill_record $4 mk_project in
                                          exp (erecord (make_record_map lst)) (Span.extend $1 $3)
                                        }
    | LBRACE exprs RBRACE               { make_set $2 (Span.extend $1 $3) }
    | LBRACE RBRACE                     { make_set [] (Span.extend $1 $2) }
    | expr2                             { $1 }
;

expr2:
    | expr2 expr3                       { exp (eapp $1 $2) (Span.extend $1.espan $2.espan) }
    | expr3                             { $1 }
;

expr3:
    | ID                                { exp (evar (snd $1)) (fst $1) }
    | ID DOT ID                         { exp (eproject (evar (snd $1)) (Nv_datastructures.Var.name (snd $3))) (Span.extend (fst $1) (fst $3)) }
    | NUM                               { to_value (vint (snd $1)) (fst $1) }
    | prefixes                          { $1 }
    | NODE                              { to_value (vnode (snd $1)) (fst $1)}
    | edge_arg TILDE edge_arg           { to_value (vedge (snd $1, snd $3)) (Span.extend (fst $1) (fst $3))}
    | TRUE                              { to_value (vbool true) $1 }
    | FALSE                             { to_value (vbool false) $1 }
    | NONE                              { to_value (voption None) $1 }
    | LPAREN exprs RPAREN               { tuple_it $2 (Span.extend $1 $3) }
;

ipaddr:
  | NUM DOT NUM DOT NUM DOT NUM         { to_value (vint (ip_to_dec (snd $1) (snd $3) (snd $5) (snd $7))) (fst $1) }

prefixes:
  | ipaddr SLASH NUM                    { let pre = to_value (vint (snd $3)) (fst $3) in
                                          etuple [$1; pre]}

edge_arg:
  | NUM                                 { (fst $1), (Nv_datastructures.Integer.to_int (snd $1))}
  | NODE                                { (fst $1), (snd $1) }

exprs:
    | expr                              { [$1] }
    | expr COMMA exprs                  { $1 :: $3 }
;

exprsspace:
    | expr3                             { [$1] }
    | expr3 exprsspace                  { $1 :: $2 }
;

edgenode:
    | NUM                               { Nv_datastructures.Integer.to_int (snd $1) }
    | NODE                              { snd $1 }
;

edge:
    | edgenode TILDE edgenode SEMI      { [($1, $3)] }
    | edgenode SUB edgenode SEMI        { [($1, $3)] }
    | edgenode EQ edgenode SEMI         { [($1, $3); ($3, $1)] }
;

edges:
    | edge                              { $1 }
    | edge edges                        { $1 @ $2 }
;

pattern:
    | UNDERSCORE                        { PWild }
    | ID                                { PVar (snd $1) }
    | TRUE                              { PBool true }
    | FALSE                             { PBool false }
    | NUM                               { PInt (snd $1) }
    | NODE                              { PNode (snd $1) }
    | pattern TILDE pattern             { PEdge (ensure_node_pattern $1, ensure_node_pattern $3)}
    | LPAREN patterns RPAREN            { tuple_pattern $2 }
    | NONE                              { POption None }
    | SOME pattern                      { POption (Some $2) }
    | LBRACE record_entry_ps RBRACE     { PRecord (make_record_map
                                          (if snd $2
                                           then fill_record (fst $2) (fun _ -> PWild)
                                           else fst $2)) }
;

patterns:
    | pattern                           { [$1] }
    | pattern COMMA patterns            { $1::$3 }
;

record_entry_p:
  | ID EQ pattern                    { snd $1, $3 }
;

record_entry_ps:
  | record_entry_p                      { ([$1], false) }
  | record_entry_p SEMI                 { ([$1], false) }
  | record_entry_p SEMI UNDERSCORE      { ([$1], true) }
  | record_entry_p SEMI record_entry_ps { ($1::(fst $3), snd $3) }

branch:
    | BAR pattern ARROW expr            { ($2, $4) }
;

branches:
    | branch                            { addBranch (fst $1) (snd $1) emptyBranch }
    | branch branches                   { addBranch (fst $1) (snd $1) $2 }
;

prog:
    | components EOF                    { $1 }
;
