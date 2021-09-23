.PHONY: test clean

default:
	dune build src/exe/main.exe
	cp _build/default/src/exe/main.exe nv

release:
	dune build --profile release src/exe/main.exe
	cp _build/default/src/exe/main.exe nv.opt

debug:
	dune build --profile debug src/exe/main.exe
	cp _build/default/src/exe/main.exe nv.debug

#install: default
#	cp _build/default/src/exe/main.exe nv

nvgen: default $(wildcard src/nvgen/*.ml)
	dune build src/nvgen/nvgen.exe
	cp _build/default/src/nvgen/nvgen.exe nvgen

test: default
	dune runtest -f --no-buffer

doc:
	dune build @doc

format:
	find src -type f -regex ".*\.mli*" -exec ocamlformat --inplace {} \;
	find test -type f -regex ".*\.mli*" -exec ocamlformat --inplace {} \;

clean:
	dune clean
	rm -f nv
	rm -f nvgen
