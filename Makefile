MODULES_NODOC := Tactics
MODULES_PROSE := Intro
MODULES_CODE  := StackMachine InductiveTypes
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE)
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES_DOC:%=%.v)
GLOBALS       := .coq_globals
TEMPLATES     := $(MODULES_CODE:%=templates/%.v)

.PHONY: coq clean doc dvi html templates install

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
		latex/*.sty latex/cpdt.* templates/*.v

doc: latex/cpdt.dvi latex/cpdt.pdf html

latex/cpdt.tex: Makefile $(VS)
	cd src ; coqdoc --latex -s $(VS_DOC) \
		-p "\usepackage{url}" \
		-p "\title{Certified Programming with Dependent Types}" \
		-p "\author{Adam Chlipala}" \
		-p "\iffalse" \
		-o ../latex/cpdt.tex

latex/cpdt.dvi: latex/cpdt.tex
	cd latex ; latex cpdt ; latex cpdt

latex/cpdt.pdf: latex/cpdt.dvi
	cd latex ; pdflatex cpdt

html: Makefile $(VS) src/toc.html
	cd src ; coqdoc $(VS_DOC) \
		--glob-from ../$(GLOBALS) \
		-d ../html
	cp src/toc.html html/

dvi:
	xdvi latex/cpdt

templates: $(TEMPLATES)

templates/%.v: src/%.v tools/make_template.ml
	ocaml tools/make_template.ml <$< >$@

cpdt.tgz:
	hg archive -t tgz $@

install: cpdt.tgz latex/cpdt.pdf html
	cp cpdt.tgz staging/
	cp latex/cpdt.pdf staging/
	cp -R html staging/
	rsync -az --exclude '*~' staging/* ssh.hcoop.net:sites/chlipala/adam/cpdt/
