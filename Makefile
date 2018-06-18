PKGS = -package integers -package ounit -package z3
BUILD = ocamlbuild -use-ocamlfind -r $(PKGS)
MLFILES= src/*.ml src/*.mli test/*.ml \

default:  src/Main

build: $(MLFILES)
	ocamlbuild -use-ocamlfind -r src/Main.native

%: %.ml
	$(BUILD) $@.native

run_tests: tests
	./Interp_test.native

clean:
	ocamlbuild -clean
	rm -Rf *.d.byte _build *~
