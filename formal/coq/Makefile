# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
#
# Makefile for the Eclexia Coq formal-verification project.
#
# The CI workflow (.github/workflows/verify-coq-proofs.yml) invokes a
# bare `make` in this directory. Coq projects are built by generating a
# rule file from _CoqProject with `coq_makefile` and then running it;
# this Makefile wires that two-step process to the default target so a
# plain `make` builds every file listed in _CoqProject (Syntax.v,
# Typing.v) under the same loadpath the proofs were checked with.
#
# (The repo also ships a Justfile with the same recipe for local use;
# this Makefile is the make-native entry point CI expects.)

COQMAKEFILE := build.mk

.PHONY: all clean

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d
