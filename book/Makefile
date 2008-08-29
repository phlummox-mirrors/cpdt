MODULES_NODOC := Tactics
MODULES_DOC   := StackMachine
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES_DOC:%=%.v)
GLOBALS       := .coq_globals

.PHONY: coq clean doc

coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -I src -impredicative-set \
			-dump-glob $(GLOBALS)" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend $(GLOBALS) \
		latex/*.sty latex/cpdt.*

doc: latex/cpdt.dvi

latex/cpdt.tex: $(VS)
	cd src ; coqdoc --latex $(VS_DOC) \
		-o ../latex/cpdt.tex

latex/cpdt.dvi: latex/cpdt.tex
	cd latex ; latex cpdt
