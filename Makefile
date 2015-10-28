#
# Trivial Makefile for a trival project.
#

.PHONY: html clean all
.DEFAULT_GOAL := all

COQLIBS?= -I .

COQC?= coqc
COQFLAGS?= $(COQLIBS)
COQDOC?= coqdoc
COQDOCFLAGS?= --parse-comments 
COQDEP?=coqdep -c

VFILES:= Elementary.v Cardinality.v Scales.v
VOFILES:= $(VFILES:.v=.vo)
VdFILES:= $(VFILTES:.v=.v.d)

-include $(VdFILES)
.SECONDARY: $(VdFILES)

html: $(GLOBFILES) $(VFILES) 
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -d html $(VFILES)

all: $(VOFILES)

clean:
	rm -f $(VOFILES) $(GLOBFILES) $(VdFILES)
	- rm -rf html

%.vo %.glob: %.v
	$(COQC) $(COQFLAGS) $*

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

