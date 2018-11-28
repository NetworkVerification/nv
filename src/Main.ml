open Main_defs

let test cfg info decls : unit =
  ()
  (* let decls = Inline.inline_declarations info decls in
  let decls, f = Renaming.alpha_convert_declarations decls in
  let decls = Typing.infer_declarations info decls in

  let maplist =
    MapUnrollingUtils.collect_map_types_and_keys decls
  in
  print_endline @@ MapUnrollingUtils.maplist_to_string maplist;
  print_endline @@ "\n Old Decls: \n" ;
  (* Printing.declarations_to_string decls; *)
  let ty, keys = List.hd maplist in
  let new_decls = MapUnrolling2.unroll_one_map_type ty keys decls in
  print_endline @@ "\n New Decls \n" ^
                   Printing.declarations_to_string new_decls;
  (* ignore @@ 1/0; *) () *)
;;

let main =
  let cfg, info, decls = parse_input Sys.argv in

  (* test cfg info decls; *)
(* 
  let decls = Inline.inline_declarations info decls in
  let decls = Typing.infer_declarations info decls in

  let maplist =
    MapUnrollingUtils.collect_map_types_and_keys decls
  in
  let decls =
    if List.length maplist <> 0 then
      let ty, keys = List.hd maplist in
      let decls = MapUnrolling2.unroll_one_map_type ty keys decls in
      decls
    else decls
  in

  let decls = Typing.infer_declarations info decls in
  Typing.check_annot_decls decls;
  Wellformed.check info decls; *)

  if cfg.smt then ignore @@ run_smt cfg info decls ;
  if cfg.random_test then ignore @@ run_test cfg info decls ;
  if cfg.simulate then ignore @@ run_simulator cfg info decls
