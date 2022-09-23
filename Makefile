#
# Copyright : see COPRRIGHT
# License   : see LICENSE
#

PROJECT=velo
IDRIS2=idris2

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: ${PROJECT} ${PROJECT}-test-build ${PROJECT}-test-run ${PROJECT}-test-run-re ${PROJECT}-test-update \
       # ${PROJECT}-bench

velo:
	$(IDRIS2) --build ${PROJECT}.ipkg

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


# [ Housekeeping ]

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/

# -- [ EOF ]
