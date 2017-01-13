HAS_MENHIR := $(shell command -v menhir 2> /dev/null)
ifdef HAS_MENHIR
HAS_VALID_MENHIR := $(shell expr `menhir --version | sed -e 's/.*version \([0-9]*\)/\1/'` \>= 20161115)
else
HAS_VALID_MENHIR := 0
endif

MENHIR=menhir #--explain --infer -la 1 --table
OCAMLLEX=ocamllex

ml/interactiveParser.mly: interactiveParser.mly
ifeq ($(HAS_VALID_MENHIR), 1)
	# TODO : call menhir directly when positions are fixed instead of
	# letting OCamlbuild go through ocamlyacc
	# Save a copy of the dumb interactiveParser.mly for whoever doesn't have menhir.
	$(MENHIR) --only-preprocess-for-ocamlyacc $< > $@
endif

interactiveParser.fsy: ml/interactiveParser.mly
	echo "%{" >> $@
	echo "#ligth \"off\"" >> $@
	echo "open Prims" >> $@
	echo "open FStar.String" >> $@
	echo "open FStar.Util" >> $@
	sed $< -e '/%{/d' \
	       -e '/^open /d' \
	       -e '/%token/s/[a-zA-Z0-9_]*\.//g' \
	       -e '/%type/s/[a-zA-Z0-9_]*\.//g' \
	       -e '/%token.*->.*/d' \
	       -e '/%type.*->.*/d' \
	       >> $@

interactiveLex.fsl: ml/interactiveLex.mll
	echo "{" >> $@
	echo "  #light \"off\"" >> $@
	echo "  open FStar.InteractiveParser" >> $@
	sed $< -e 's/lexeme/ulexeme/g' \
	       -e '1,3d' \
	       >> $@
