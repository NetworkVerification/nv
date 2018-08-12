PKGS = -package integers -package ounit -package z3
BUILD = ocamlbuild -use-ocamlfind -use-menhir -r $(PKGS)
MLFILES= src/*.ml src/*.mli test/*.ml
FORMATFILES=$(shell find src/ -name "*.ml" | grep -v Cmdline.ml)
FORMATFILES+=$(shell find src/ -name "*.mli")

default:  src/Main

all:
	ocamlformat -i $(FORMATFILES)
	$(BUILD) src/Main.native
	mv Main.native /usr/local/bin/nv

install:
	mv Main.native /usr/local/bin/nv

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
	ocamlformat -i $(FORMATFILES)
