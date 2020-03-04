open Srp
open Nv_lang
open Syntax
open Nv_solution
open Nv_datastructures
open Nv_interpreter
open Nv_utils.OCamlUtils

(* We track an environment of bound variables, and two lists of symbolic/solution
   variables for later reporting. We also track if an assertion has been failed,
   and if so, which one. We only store the first assertion failure since we terminate
   simulation when we see it. *)
type sym_state = {env : value Env.t; syms : var list; sols : var list; failed : exp option}
let empty_state = {env = Env.empty; syms = []; sols = []; failed = None}

let simulate_declaration ~(throw_requires: bool) (graph : AdjGraph.t) (state : sym_state) (d : declaration) : sym_state =
  match state.failed with
  | Some _ -> state (* Stop simulating once an assertion fails *)
  | None ->
    let env = state.env in
    let evaluate = Interp.interp_exp {ty = Env.empty; value = env} in
    match d with
    | DLet (x, _ , e) ->
      {state with env = Env.update env x (evaluate e)}
    | DSymbolic (x, toe) ->
      let e = match toe with
        | Exp e -> e
        | Ty ty -> e_val (Generators.default_value ty)
      in
      {state with env = Env.update env x (evaluate e); syms = x :: state.syms}
    | DRequire e ->
      begin
        match evaluate e with
        | {v = VBool true} -> state
        | _ ->
          if throw_requires
          then raise Srp.Require_false
          else (Console.warning @@
                "Requires condition not satisified during simulation : " ^
                Printing.exp_to_string e;
                state)
      end
    | DAssert e ->
      begin
        match evaluate e with
        | {v = VBool true} -> state
        | _ ->
          {state with failed = Some e}
      end
    | DSolve solve -> failwith ""
    | DATy _ | DUserTy _ | DPartition _ | DInterface _ | DNodes _ | DEdges _ -> state
    | DInit _ | DTrans _ | DMerge _ -> state (* Deprecated *)
;;


let simulate_declarations ~(throw_requires: bool) (decls : declarations) : Solution.t =
  let graph =
    let n = get_nodes decls |> oget in
    let es = get_edges decls |> oget in
    List.fold_left AdjGraph.add_edge_e (AdjGraph.create n) es
  in
  let final_state = List.fold_left (simulate_declaration ~throw_requires graph) empty_state decls in
  ignore final_state; (* Turn final_state into a solution somehow *)
  failwith ""
