# NV's SMT Encoding

This document presents a breakdown of NV's `SmtClassicEncoding` in an effort to better understand its complexity.

## Entry Point: `src/lib/Main_defs.ml`

We enter NV's SMT library from `run_smt`, which is called when the user passes NV the `-smt` flag.
`run_smt` sets the relevant SMT config options (finite arithmetic and parallelism) from the commandline flags,
and then calls the appropriate encoding.
In the past, this was either the _functional_ encoding or the _classic_ encoding:
functional encoding is no longer used, so we automatically move on to `run_smt_classic`.

### `run_smt_classic`

`run_smt_classic` begins by performing a few additional network transformations to prepare
the file for SMT that are not performed in other settings.
These include [unboxing edges](src/lib/transformations/UnboxEdges.ml) and
[options](src/lib/transformations/UnboxOptions.ml),
[flattening tuples](src/lib/transformations/TupleFlatten.ml),
[alpha-renaming](src/lib/transformations/Renaming.ml),
[optimizing match branches](src/lib/transformations/OptimizeBranches.ml),
[renaming SMT variables](src/lib/transformations/RenameForSMT.ml) and
[unboxing units](src/lib/transformations/UnboxUnits.ml).

We then may partition the file if the `-kirigami` flag is given, and otherwise
continue on to `run_smt_classic_aux` which will call the appropriate SMT solve function.
Parallelism was previously implemented here for _slicing_, which is currently disabled as it is not yet implemented
for this version of NV.

## The `solve_fun` SMT functions

We then solve the declarations of the network.
With `-kirigami`, we use the specialized [`SmtKirigami.solveKirigami`][smtkirigami] function;
with `-hiding`, we use [`SmtHiding.solve_hiding`][smthiding];
otherwise, we default to the standard [`Smt.solveClassic`][smt] solve function.
All three of these functions return either `Unsat`, `Unknown`, `Timeout` (if Z3 times out) or `Sat`.

The `solve_fun` functions have a standard form: they encode the declarations and
query Z3 with the resulting SMT query.

## The Classic SMT Encoding

We'll jump ahead to considering the classic encoding now.
The encoding consists of a function `encode_z3` which calls relevant
subfunctions to encode the entire list of declarations `decls` as an [`smt_env`][smtutils].

### `encode_z3`

`encode_z3` starts by requesting the five essential components of `decls` using the `get_decl`-based functions provided
by [`Syntax`][syntax]. Each of these operations searches `decls` for the relevant declarations in time `O(len(decls))`.

- the network graph `graph` (constructed from the `nodes` and `edges` declarations in time `O(|V| + |E|)`);
- the symbolic declarations `symbolics`;
- the solution declarations `solves`;
- the assert declarations `asserts`, which are each [partially interpreted][interppartial]; and
- the require declarations `requires`.

It then initializes the [`smt_env`][smtutils] environment, which will store all the declarations
in the encoding. The `smt_env` has four mutable fields, which are updated imperatively as the encoding proceeds:

- `symbolics : Syntax.ty_or_exp VarMap.t`: a map from variable names to their associated syntactic type or expression
  (essentially just storing the symbolic declarations): these are used when reporting a counterexample, as we need to report
  the value given to each symbolic variable.
- `const_decls : ConstantSet.t`: an ordered set (implemented as a bBST) of SMT constants, declared using `(declare-const)` at
  the top of the environment.
- `type_decls : datatype_decl StringMap.t`: an ordered map (implemented as a bBST) which declares SMT datatypes: not used by
  the [`SmtUnboxed`][smtunboxed] encoding (which just uses bools and integers).
- `ctx : command list`: commands are SMT commands like `echo s`, `assert t`, `checksat` and `getmodel`; these are passed
  to the solver last, after all declarations and SMT constants. `assert t` commands (where `t` is an `smt_term`)
  collect the essential constraints of our encoding.

We then proceed to the four stages of encoding:

1. Encode `symbolic`s: add each symbolic to `smt_env.symbolics` and declare an SMT constant;
2. Encode `solution`s: declare constants representing each function of the `solution`'s inputs and outputs,
   e.g., the input to a `trans` function and its result, or the result of `merge` on two values,
   and finally the label representing each node's solution;
3. Encode `assert`s: for each `assert` statement, declare an `assert-i` constant and add an `assert` constraint; and
4. Encode `require`s: add a constraint for the encoding of each `require` statement.

Additionally, all constants of sort [`IntSort`][smtutils] must be constrained to be non-negative.
All of these stages involve making calls to [`encode_exp_z3`][smtunboxed] to handle
the relevant `Syntax.exp` expressions, and adding relevant constants and symbolics to the environment.
`encode_exp_z3` (and `encode_exp_z3_single`, one of its helpers) traverse the AST of an expression
to encode it to SMT, creating variables and terms as needed and adding constraints
using the [`SmtUtils`][smtutils] API.

We now expand on the encoding of solutions, which is the largest stage.

### `encode_solve`

Encoding solutions also proceeds in multiple stages:

1. `encode_label_vars`: for each node, extract the variables that make up its solution from `var_names`, based on the
   solution's `aty` (attribute type) field. Proportional to `|V|`.
2. Create two data structures, each proportional to `|E|`,
   to keep track of `trans` behavior along edges with `encode_edge_transfers`:

- `trans_map`, a map from each edge `uv` to the encoded variable `y` where `y = (trans uv x)`
- `trans_input_map`, a map from each edge `uv` to the encoded variable `x` where `y = (trans uv x)`

The variables `x` and `y` are newly-declared constants, and we declare a constraint for each edge `uv` asserting
`y = (trans uv x)`.
We invert the arguments of `trans` before constructing the maps, but don't [partially interpret][interppartial]
until each edge is supplied. (not totally clear why to me)

3. For each node `v` (`O(|V|)`), collect all predecessor edges `uv` (`O(max(|V|,|E|)*ln|V|)`),
   and then encode the merge of `(init v)` with each of the transferred `y` variables.
   [Partially interpret][interppartial] `(init v)` and `(merge v)` before encoding.
   Successive merges are folded together one-by-one.
   The final declared label `l` is then stored in `labelling`: a `VertexMap.t` that maps nodes to their `smt_term`(s).
4. For each label `l` in `labelling` (`O(|V|)`), add a constraint equating it to the `x` defined in `trans_input_map`.

Once this is done, `encode_solve` returns.

#### `encode_kirigami_solve`

Kirigami's encoding of solutions is similar to the encoding for `encode_solve`, except for a few extra steps:

- We construct an `input_map` using the decomposed `rtrans` (input trans) akin to `trans_map`. This encodes a predicate
  `input-pred` for the interface of each incoming edge, and performs the usual `trans` behavior encoding for the input trans.
- We use both `trans_map` and `input_map` when computing the final label `l`.
- As `label_vars` is encoded and sized using the map of all nodes in the monolithic network,
  we need to assign dummy constants to the variables of the cut nodes so that SMT doesn't throw an error.
- We construct a list of guarantees to assert encoded `output-pred` predicates for each outgoing edge, and (if given)
  perform the `trans` behavior encoding for the output trans.

### `encode_exp_z3`

Encoding [`Syntax.exp`][syntax] expressions to Z3 is done by `encode_exp_z3`.
This function descends the AST of an `exp` to encode it to SMT.
As transformations have been run on the AST, we expect these expressions to be only those of the following forms:

- values: either integers, bools, nodes or tuples thereof
- variables
- equality operators: `e1 = e2`
- boolean operators: `e1 && e2`, `e1 || e2`, `!e1`
- integer operators: `e1 + e2`, `e1 - e2`, `e1 & e2`, `e1 < e2`, `e1 <= e2`, `e1 > e2`, `e1 >= e2`
- tuple read: `tget size lo hi t` (return the elements of the tuple `t` from `lo` to `hi`)
- tuple write: `tset size lo hi t1 t2` (set the elements of `t1` from `lo` to `hi` using `t2`)
- if statements: `if e1 then e2 else e3`
- let statements: `let x = e1 in e2`
- match statements: `match e1 with bs`, where `bs` is a non-zero sequence of match arms (matching on valid value types or variables)
- type annotations: `e : ty`

This also means that any functions in the code must at this point have been inlined and applied to all of their arguments:
this is handled by interpreting.

[smtkirigami]: src/lib/smt/SmtKirigami.ml
[smthiding]: src/lib/smt/SmtHiding.ml
[smt]: src/lib/smt/Smt.ml
[smtutils]: src/lib/smt/SmtUtils.ml
[syntax]: src/lib/lang/Syntax.ml
[interppartial]: src/lib/interpreter/InterpPartial.ml
[smtunboxed]: src/lib/smt/SmtUnboxed.ml
