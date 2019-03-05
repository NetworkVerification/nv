# Educational materials on network verification

## Building nv

To start with, make sure you have all of these dependencies: `gcc, make, m4` for `ocaml`, `g++` for `mlcuddidl` and `z3` (which needs `python2.7` and `libgmp`).
Use `opam` to install the `ocaml` dependencies.

If you don't have `opam` yet, see the [OPAM install instructions](https://opam.ocaml.org/doc/Install.html).
This is the best way to set up `ocaml`.

Execute the following to install required packages once `opam` is up:

```
opam install -y \
  integers \
  batteries \
  ounit \
  ansiterminal \
  menhir \
  mlcuddidl \
  ppx_deriving \
  ppx_deriving_argparse \
  lru-cache \
  zarith \
  ocamlgraph \
  z3
```

Then clone the repo and run `make`.

### Ubuntu (16.04+)

```
sudo apt install gcc g++ make m4 libgmp-dev python2.7 libz3-dev z3
```

## Running nv
  
In order to use the SMT solver, you must have the z3 executable on your PATH. It should have the name "z3".

## Troubleshooting

### "symbol lookup error: Z3_get_full_version"

Add the ocaml z3 lib to your `LD_LIBRARY_PATH`:

```
eval $(opam env)
export LD_LIBRARY_PATH="$OPAM_SWITCH_PREFIX/lib/z3"
```
