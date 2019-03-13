PKGS = -package integers -package oUnit
DIRS = src,test
# BUILD = ocamlbuild -use-ocamlfind -use-menhir -r -Is $(DIRS) $(PKGS)
BUILD = ocamlbuild -tag thread -use-ocamlfind -use-menhir -r -Is $(DIRS) $(PKGS)
MLFILES= src/*.ml src/*.mli test/*.ml
FORMATFILES=$(shell find src/ -name "*.ml" | grep -v Cmdline.ml)
FORMATFILES+=$(shell find src/ -name "*.mli")

.PHONY: test clean

default:  src/Main

all:
	ocamlformat -i --margin=70 $(FORMATFILES)
	$(BUILD) src/Main.native
	mv Main.native /usr/local/bin/nv

install:
	mv Main.native /usr/local/bin/nv

build: $(MLFILES)
	$(BUILD) src/Main.native

debug: $(MLFILES)
	$(BUILD) -tag debug src/Main.native

profile: $(MLFILES)
	$(BUILD) -tag profile -tag 'cc(gcc)' src/Main.native

opt: $(MLFILES)
	$(BUILD) -tag 'optimize(2)' src/Main.native

byte: $(MLFILES)
	$(BUILD) -tag byte -tag debug src/Main.byte

%: %.ml
	$(BUILD) $@.native

test: $(MLFILES)
	$(BUILD) src/Main.native test/Test.native
	./Test.native

run_tests: tests
	./Interp_test.native

clean:
	ocamlbuild -clean
	rm -Rf *~ src/*~ test/*~ examples/*~

format:
	ocamlformat -i --margin=70 $(FORMATFILES)
