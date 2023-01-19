.PRECIOUS: build/ttc/*/%.ttm build/ttc/*/%.ttc Code/%.idr.tex

CODE:=\
  Code/MiniVelo.tex \
  Code/MiniDeBruijn.tex \
  Code/MiniCompact.tex \
  Code/MiniExecute.tex

DEPENDS:=\
  cc-by.pdf \
  oasics-logo-bw.pdf \
  oasics-v2021.cls \
  orcid.pdf \
  preamble.tex \
  notations.tex \
  ./content/*.tex \
  ./figure/*.tex \
  $(patsubst %.tex,%.idr.tex,$(CODE)) \
  paper.bib

all: paper.pdf

build/ttc/*/%.ttm build/ttc/*/%.ttc: Code/%.idr
	idris2 -c $^

Code/%.idr.tex: Code/%.tex build/ttc/*/%.ttm build/ttc/*/%.ttc
	katla literate Code/$*.tex build/ttc/*/Code/$*.ttm > $@

%.pdf : %.tex $(DEPENDS)
	mkdir -p __build
	echo $(DEPENDS)
	latexmk -pdf -bibtex -outdir="__build" $*.tex
	ln -sf __build/$*.pdf $*.pdf

clean:
	rm -rf __build/
	rm paper.pdf
