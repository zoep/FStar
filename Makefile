.PHONY: all opt boot reopt clean

CORES ?= $(shell getconf _NPROCESSORS_ONLN)

all:
	$(MAKE) -j${CORES} -C src

opt:
	$(MAKE) -j${CORES} -C src/ocaml-output

boot:
	$(MAKE) -j${CORES} -C src fstar-ocaml

reopt: opt boot opt

install:
	./scripts/install.sh

clean:
	$(MAKE) -C src clean
