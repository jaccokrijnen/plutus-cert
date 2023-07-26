# Makefile originally taken from coq-club

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq cleanall
	rm -f Makefile.coq
	# CLEANING ALL *.vo *.aux *.glob *.vok *.vos files (files not known in _CoqProject are not removed by cleanall)
	find src -type f -name "*.vo" -delete
	find src -type f -name "*.vos" -delete
	find src -type f -name "*.vok" -delete
	find src -type f -name "*.aux" -delete
	find src -type f -name "*.glob" -delete
	rm -f Makefile.coq


Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony

