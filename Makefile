PKGS = -package integers -package ounit -package z3
BUILD = ocamlbuild -use-ocamlfind -use-menhir -r $(PKGS)
MLFILES= src/*.ml src/*.mli test/*.ml \

default:  src/Main

build: $(MLFILES)
	$(BUILD) src/Main.native

%: %.ml
	$(BUILD) $@.native

simple: $(MLFILES)
	./Main.native -f "examples/simple.nv" -v -s

diamond: $(MLFILES)
	./Main.native -f "examples/diamond.nv" -v -s

run_tests: tests
	./Interp_test.native

clean:
	ocamlbuild -clean
	rm -Rf *~ src/*~ test/*~ examples/*~

format:
	ocamlformat -i $(MLFILES)
