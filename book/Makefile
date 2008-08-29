MODULES    := Tactics StackMachine
VS         := $(MODULES:%=%.v)
GLOBALS    := .coq_globals

.PHONY: coq clean

coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -impredicative-set -dump-glob $(GLOBALS)" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend
