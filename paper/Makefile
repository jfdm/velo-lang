DEPENDS=\
  cc-by.pdf \
  oasics-logo-bw.pdf \
  oasics-v2021.cls \
  orcid.pdf \
  paper.bib


all: paper.pdf


%.pdf : %.tex $(DEPENDS)
	mkdir -p __build
	latexmk -pdf -bibtex -outdir="__build" $*.tex

clean:
	rm -rf __build/
	rm paper.pdf
