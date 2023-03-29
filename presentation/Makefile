slides: presentation.slides.pdf

%.pdf: %.tex
	mkdir -p __build
	latexmk -pdf -bibtex-cond -outdir="__build" $*.tex
	ln -sf __build/$*.pdf $*.pdf

clean:
	rm -rf __build/
	rm presentation.slides.pdf
