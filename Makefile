PKGS = -package integers -package ounit -package z3
BUILD = ocamlbuild -use-ocamlfind -use-menhir -r $(PKGS)
MLFILES= src/*.ml src/*.mli test/*.ml \

default:  src/Main

all:
	ocamlformat -i $(MLFILES)
	$(BUILD) src/Main.native
	mv Main.native /usr/local/bin/srp

install:
	mv Main.native /usr/local/bin/srp

build: $(MLFILES)
	$(BUILD) src/Main.native

%: %.ml
	$(BUILD) $@.native

simple: $(MLFILES)
	./Main.native -f "examples/simple.nv" -v -s

diamond: $(MLFILES)
	./Main.native -f "examples/diamond.nv" -v -s

diamond-ospf: $(MLFILES)
	./Main.native -f "examples/diamond-ospf.nv" -v -s

run_tests: tests
	./Interp_test.native

clean:
	ocamlbuild -clean
	rm -Rf *~ src/*~ test/*~ examples/*~

format:
	ocamlformat -i $(MLFILES)
