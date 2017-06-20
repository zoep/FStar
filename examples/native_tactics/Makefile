FSTAR_HOME=../..
OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

.PRECIOUS: %.ml

%.ml: %.fst
	$(FSTAR) $(OTHERFLAGS) --codegen OCaml $< --extract_module $(patsubst %.fst,%,$<)
	cat $(patsubst %.fst,%,$<).fixup >> $@

%.cmxs: %.ml
	ocamlfind ocamlopt -shared $(INCLUDES) -linkpkg -package zarith -o $@ $<

.PHONY: test

%.test: %.cmxs %.Test.fst 
	$(FSTAR) --load $^

clean:
	rm -f *.ml *.cm*