SRC=src
# BE AWARE that modifications to .agdai files in these folders are not detected
SRC_STDLIB=agda-stdlib/src

INCLUDES=${AGDA_INCLUDES} \
         ${SRC} \
         ${SRC_STDLIB}

MODULES=Proposal

SOURCEFILES=$(MODULES:%=$(SRC)/%)

INCLUDE_PARAMS=$(INCLUDES:%=-i%$)

default: code
all: code proposal
clean: cleancode cleanproposal

# Code --------------------
code: $(SOURCEFILES:%=%.agdai)

$(SRC)/%.agdai: $(SRC)/%.lagda
	agda $(INCLUDE_PARAMS) $<
$(SRC)/%.agdai: $(SRC)/%.agda
	agda $(INCLUDE_PARAMS) $<

cleancode:
	find $(SRC_STDLIB) -name '*.agdai' -delete
	find $(SRC) -name '*.agdai' -delete

# Proposal --------------------

proposal: AGDA_PARAMS = $(INCLUDE_PARAMS) --latex-dir=lagda-out --latex --allow-unsolved-metas
proposal: proposal/main.pdf

lagda-out/%.tex: $(SRC)/%.lagda
	agda $(AGDA_PARAMS) $<

proposal/main.pdf: $(MODULES:%=lagda-out/%.tex) proposal/agda.sty proposal/main.tex proposal/body.tex proposal/main.bib
	cd proposal; latexmk -xelatex -outdir=out main.tex
	mv proposal/out/main.pdf proposal/main.pdf

cleanproposal:
	rm -rf lagda-out
	rm -rf proposal/out


.PHONY: default all clean code cleancode proposal cleanproposal
