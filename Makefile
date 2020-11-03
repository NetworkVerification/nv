.PHONY: test clean

default:
	dune build src/exe/main.exe
	cp _build/default/src/exe/main.exe nv

#install: default
#	cp _build/default/src/exe/main.exe nv

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
