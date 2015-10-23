#
# Trivial Makefile for a trival project.
#

.PHONY: doc

doc:
	coqdoc -d ./doc --parse-comments Scales.v
