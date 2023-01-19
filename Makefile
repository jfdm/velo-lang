#
# Copyright : see COPRRIGHT
# License   : see LICENSE
#

PROJECT=velo
IDRIS2=idris2

BUILDDIR = ${CURDIR}/build
TARGETDIR = ${BUILDDIR}/exec
TARGET = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: ${PROJECT} doc ${PROJECT}-test-build ${PROJECT}-test-run ${PROJECT}-test-run-re ${PROJECT}-test-update \
       # ${PROJECT}-bench

velo:
	$(IDRIS2) --build ${PROJECT}.ipkg

doc:
	$(IDRIS2) --mkdoc ${PROJECT}.ipkg

# To be activated once frontend is completed.

${PROJECT}-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

${PROJECT}-test-run: ${PROJECT}-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

${PROJECT}-test-run-re: ${PROJECT}-test-build
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

${PROJECT}-test-update: ${PROJECT}-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 THREADS=1 \
			 ONLY=$(ONLY)

${PROJECT}-bench: ${PROJECT} ${PROJECT}-test-build
	${ECHO} "Todo"

#	$(HYPERFINE) --warmup 10 '${MAKE} ${PROJECT}-test-run'

# [ Archive & Artefact ]

.PHONY: archive

archive:
	git archive \
	  --prefix=velo/ \
	  --format=tar.gz \
	  HEAD \
	  src tests/ \
	  CONTRIBUTORS COPYRIGHT LICENSE README.md emacs > artefact/velo.tar.gz


artefact: ${PROJECT} archive doc
	bash annotate.sh # generate annotated sources
	tar -zcvf artefact/velo_html.tar.gz ${BUILDDIR}/html/ # annotated source
	tar -zcvf artefact/velo_doc.tar.gz ${BUILDDIR}/docs/ # include docs
	${MAKE} -C paper/2023-EVCS paper.pdf
	cp paper/2023-EVCS/__build/paper.pdf artefact/velo.pdf
	${MAKE} -C artefact artefact

# [ Housekeeping ]

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean
	rm -rf build/

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/
	${RM} artefact/*.tar.gz

# -- [ EOF ]
