open Nv_lang
open Syntax
open Nv_solution
open Nv_datastructures
open Nv_interpreter
open Nv_utils.OCamlUtils
open Nv_lang.Collections

(* We track an environment of bound variables, and two lists of symbolic/solution
   variables for later reporting. We also track if an assertion has been failed,
   and if so, which one. We only store the first assertion failure since we terminate
   simulation when we see it. *)
type sym_state =
  { env : value Env.t
  ; syms : (var * value) list
  ; sols : (var * Solution.sol) list
  ; assertions : bool list
  }

let empty_state = { env = Env.empty; syms = []; sols = []; assertions = [] }

let simulate_declaration
    ~(throw_requires : bool)
    (graph : AdjGraph.t)
    (state : sym_state)
    (d : declaration)
    : sym_state
  =
  match state.assertions with
  | false :: _ -> state (* Stop simulating once an assertion fails *)
  | _ ->
    let env = state.env in
    let evaluate = Interp.interp_exp { ty = Env.empty; value = env } in
    (match d with
    | DLet (x, _, e) -> { state with env = Env.update env x (evaluate e) }
    | DSymbolic (x, toe) ->
      let e =
        match toe with
        | Exp e -> e
        | Ty ty -> e_val (Generators.default_value ty)
      in
      let v = evaluate e in
      { state with env = Env.update env x v; syms = (x, v) :: state.syms }
    | DRequire e ->
      begin
        match evaluate e with
        | { v = VBool true } -> state
        | _ ->
          if throw_requires
          then raise Srp.Require_false
          else (
            Console.warning
            @@ "Requires condition not satisified during simulation : "
            ^ Printing.exp_to_string e;
            state)
      end
    | DAssert e ->
      let result =
        match evaluate e with
        | { v = VBool b } -> b
        | _ -> failwith "Bad assert"
      in
      { state with assertions = result :: state.assertions }
    | DSolve solve ->
      let results = Srp.simulate_solve graph { ty = Env.empty; value = env } solve in
      begin
        match solve.var_names.e with
        | EVar x ->
          let xty = TMap (TNode, oget solve.aty) in
          let bdd_base =
            BddMap.create ~key_ty:TNode (Generators.default_value (oget solve.aty))
          in
          let bdd_full =
            AdjGraph.VertexMap.fold
              (fun n v acc -> BddMap.update acc (vnode n) v)
              results
              bdd_base
          in
          let mapval = avalue (vmap bdd_full, Some xty, solve.var_names.espan) in
          { state with
            env = Env.update env x mapval
          ; sols =
              (x, { sol_val = mapval; mask = None; attr_ty = oget solve.aty })
              :: state.sols
          }
        | _ -> failwith "Not implemented" (* Only happens if we did map unrolling *)
      end
    | DUserTy _ | DPartition _ | DNodes _ | DEdges _ -> state)
;;

let simulate_declarations ~(throw_requires : bool) (decls : declarations) : Solution.t =
  let n = get_nodes decls |> oget in
  let es = get_edges decls |> oget in
  let graph = List.fold_left AdjGraph.add_edge_e (AdjGraph.create n) es in
  let final_state =
    List.fold_left (simulate_declaration ~throw_requires graph) empty_state decls
  in
  let symbolics = List.rev final_state.syms in
  let solves = List.rev final_state.sols in
  let assertions =
    let num_asserts = List.length @@ get_asserts decls in
    let rec pad count lst =
      if count = 0 then lst else pad (count - 1) (true :: lst)
      (*TODO: what is this code doing?*)
    in
    pad (num_asserts - List.length final_state.assertions) final_state.assertions
    |> List.rev
  in
  let sol : Solution.t = { symbolics; solves; assertions; guarantees = []; nodes = n } in
  sol
;;
