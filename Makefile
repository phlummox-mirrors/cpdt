MODULES_NODOC := CpdtTactics MoreSpecif DepList
MODULES_PROSE := Intro
MODULES_CODE  := StackMachine InductiveTypes Predicates Coinductive Subset \
	MoreDep DataStruct Equality Generic Universes Match Reflection \
	Large Firstorder DeBruijn Hoas Interps Extensional Intensional OpSem
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE)
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
VS            := $(MODULES:%=src/%.v)
TEX           := $(MODULES:%=latex/%.v.tex)
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
	rm -f Makefile.coq .depend cpdt.tgz templates/*.v
	cd latex; rm -f *.sty *.log *.aux *.dvi *.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out

doc: latex/cpdt.pdf html

latex/%.v.tex: Makefile src/%.v src/%.glob
	cd src ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/cpdt.pdf: latex/cpdt.tex $(TEX) latex/cpdt.bib
	cd latex ; pdflatex cpdt ; pdflatex cpdt ; bibtex cpdt ; makeindex cpdt ; pdflatex cpdt ; pdflatex cpdt

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
