#
# Trivial Makefile for a trival project.
#

.PHONY: doc

doc:
	coqdoc -d ./doc --parse-comments Scales.v
	coqdoc -d ./doc --parse-comments Elementary.v

all:
	coqc Elementary.v
	coqc Scales.v
