MODULES_NODOC := Tactics MoreSpecif DepList
MODULES_PROSE := Intro
MODULES_CODE  := StackMachine InductiveTypes Predicates Coinductive Subset \
	MoreDep DataStruct Equality Generic Universes Match Reflection \
	Large Firstorder DeBruijn Hoas Interps Extensional Intensional OpSem
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE)
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES_DOC:%=%.v)
TEMPLATES     := $(MODULES_CODE:%=templates/%.v)

.PHONY: coq clean doc html templates install cpdt.tgz pdf

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -I src" \
		COQDEP = "coqdep -I src" \
		-o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend cpdt.tgz \
		latex/*.sty latex/cpdt.* templates/*.v
	rm -f *.aux *.log

doc: latex/cpdt.pdf html

latex/cpdt.tex: Makefile $(VS) src/BackMatter.v latex/cpdt.bib
	cd src ; coqdoc --interpolate --latex -s $(VS_DOC) BackMatter.v \
		-p "\usepackage{url}" \
		-p "\iffalse" \
		-o ../latex/cpdt.tex

latex/%.tex: src/%.v src/%.glob
	cd src ; coqdoc --interpolate --latex \
		-p "\usepackage{url}" \
		$*.v -o ../latex/$*.tex

latex/%.pdf: latex/%.tex latex/cpdt.bib
	cd latex ; pdflatex $* ; pdflatex $* ; bibtex $* ; makeindex $* ; pdflatex $* ; pdflatex $*

html: Makefile $(VS) src/toc.html
	mkdir -p html
	cd src ; coqdoc --interpolate $(VS_DOC) \
		-d ../html
	cp src/toc.html html/

templates: $(TEMPLATES)

templates/%.v: src/%.v tools/make_template.ml
	ocaml tools/make_template.ml <$< >$@

cpdt.tgz:
	hg archive -t tgz $@

install: cpdt.tgz latex/cpdt.pdf html
	cp cpdt.tgz staging/
	cp latex/cpdt.pdf staging/
	cp -R html staging/
	rsync -az --exclude '*~' staging/* chlipala.net:sites/chlipala/adam/cpdt/

pdf:
	evince latex/cpdt.pdf&
