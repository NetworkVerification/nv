# Educational materials on network verification

## Building nv

Execute the following to install required packages:

```
opam install -y integers batteries ounit ansiterminal menhir mlcuddidl ppx_deriving ppx_deriving_argparse lru-cache zarith ocamlgraph z3
```

Then clone the repo and run `make`.

## Running nv
  
In order to use the SMT solver, you must have the z3 executable on your PATH. It should have the name "z3".
