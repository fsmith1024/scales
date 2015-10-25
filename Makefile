#
# Trivial Makefile for a trival project.
#

.PHONY: html clean all
.DEFAULT_GOAL := all

COQC?= coqc
COQFLAGS?= 
COQDOC?= coqdoc
COQDOCFLAGS?= --parse-comments 

VFILES:= Elementary.v Scales.v
VOFILES:= $(VFILES:.v=.vo)

html: $(GLOBFILES) $(VFILES) 
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -d html $(VFILES)

all: $(VOFILES)

clean:
	rm -f $(VOFILES) $(GLOBFILES)
	- rm -rf html

%.vo %.glob: %.v
	$(COQC) $(COQFLAGS) $*

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

