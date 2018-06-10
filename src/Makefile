PKGS = -package integers -package ounit
BUILD = ocamlbuild -use-ocamlfind $(PKGS)
TESTS = test/Interp_test

default:  Main

%: %.ml
	$(BUILD) $@.d.byte

tests: $(TESTS)

run_tests: tests
	./Interp_test.d.byte

clean:
	rm -Rf *.d.byte _build *~
