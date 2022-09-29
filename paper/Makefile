DEPENDS=\
  cc-by.pdf \
  oasics-logo-bw.pdf \
  oasics-v2021.cls \
  orcid.pdf \
  paper.bib


all: paper.pdf


%.pdf : %.tex $(DEPENDS)
	mkdir -p __build
	cp $^ __build/
	cd __build/ && latexmk -pdf -bibtex $*.tex
	ln -s __build/$*.pdf .

clean:
	rm -rf __build/
