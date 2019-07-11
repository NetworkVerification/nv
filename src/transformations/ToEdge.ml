open Syntax

(***
   Simple implementation of the toEdge primitive in NV.
   toEdge is a function of type node -> node -> edge option, such that
   toEdge n1 n2 returns Some (n1~n2) if that edge exists in the graph, and
   None otherwise. This is used to ensure users cannot create invalid edge values.

   To avoid adding another primitive to the language grammar, we implement toEdge
   by automatically generating a function definition and adding it to the program.
   In essence, it is as if the user defined the function toEdge themselves at the
   beginning of each program, but we do it ourselves to ensure it's correct.

   For example, if the graph contains 3 edges 0~1, 1~0, and 1~2, we generate the
   following declaration:

   let toEdge n1 n2 =
   match n1, n2 with
   | 0n, 1n -> Some (0~1)
   | 1n, 0n -> Some (1~0)
   | 1n, 2n -> Some (1~2)
   | _ -> None
 ***)

let toEdge_decl decls =
  let edges = get_edges decls |> oget in
  let default_branch =
    addBranch PWild (e_val (voption None)) emptyBranch
  in
  let branches =
    List.fold_left
      (fun bs (n1, n2) ->
         addBranch (PTuple [PNode n1; PNode n2]) (esome (e_val (vedge (n1, n2)))) bs
      )
      default_branch
      edges
  in
  let n1_var = Var.create "n1" in
  let n2_var = Var.create "n2" in
  DLet
    (
      Var.create "toEdge",
      None,
      efun
        {arg = n1_var; argty = None; resty = None;
         body =
           efun
             {arg = n2_var; argty = None; resty= None;
              body =
                ematch (etuple [evar n1_var; evar n2_var]) branches
             }
        }
    )
