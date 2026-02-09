# Makefile for Eclexia formal verification
# SPDX-License-Identifier: PMPL-1.0-or-later

.PHONY: all clean install

# Build all Coq files
all: Makefile.coq
	$(MAKE) -f Makefile.coq

# Generate Makefile from _CoqProject
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Clean build artifacts
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

# Install compiled theories
install: Makefile.coq
	$(MAKE) -f Makefile.coq install

# Quick check: compile without vo files
check:
	coqc -R src Eclexia src/*.v

# Help message
help:
	@echo "Eclexia Formal Verification - Coq Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all      - Build all Coq files (default)"
	@echo "  clean    - Remove build artifacts"
	@echo "  install  - Install compiled theories"
	@echo "  check    - Quick compile check"
	@echo "  help     - Show this help"
