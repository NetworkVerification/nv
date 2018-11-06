open Main_defs
  
let main =
  let cfg, info, decls = parse_input Sys.argv in
  if cfg.smt then ignore @@ run_smt cfg info decls ;
  if cfg.random_test then ignore @@ run_test cfg info decls ;
  if cfg.simulate then ignore @@ run_simulator cfg info decls
