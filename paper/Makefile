DEPENDS=\
  cc-by.pdf \
  oasics-logo-bw.pdf \
  oasics-v2021.cls \
  orcid.pdf \
  deBruijn.tex \
  efficientdeceq.tex \
  positivelynegative.tex \
  compactconstant.tex \
  notations.tex \
  introduction.tex \
  velo-intro.tex \
  paper.bib


all: paper.pdf


%.pdf : %.tex $(DEPENDS)
	mkdir -p __build
	latexmk -pdf -bibtex -outdir="__build" $*.tex
	ln -sf __build/$*.pdf $*.pdf

clean:
	rm -rf __build/
	rm paper.pdf
