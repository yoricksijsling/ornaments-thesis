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
clean: cleancode cleanproposal cleanthesis

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

PROPOSAL_TEX=main introduction literature prototype overview plan

proposal: AGDA_PARAMS = $(INCLUDE_PARAMS) --latex-dir=src-tex --latex --allow-unsolved-metas
proposal: proposal/main.pdf

src-tex:
	mkdir -p src-tex
src-tex/%.tex: $(SRC)/%.lagda src-tex proposal.fmt
	lhs2TeX --agda -o $@ $<

proposal/%.tex: proposal/%.lagda proposal.fmt
	lhs2TeX --agda -o $@ $<

proposal/main.pdf: $(PROPOSAL_TEX:%=proposal/%.tex) $(MODULES:%=src-tex/%.tex) proposal/agda.sty proposal/main.bib
	cd proposal; latexmk -xelatex -outdir=out main.tex
	cp proposal/out/main.pdf proposal/main.pdf
	rm proposal/out/main.pdf

cleanproposal:
	rm -rf src-tex
	rm -rf proposal/out
	rm -rf $(PROPOSAL_TEX:%=proposal/%.tex)
	rm -rf proposal/literature.rel

# Thesis --------------------

THESIS_TEX=main abstract introduction usage sop simple extended \
           named implementation reflection discussion conclusion

thesis: AGDA_PARAMS = $(INCLUDE_PARAMS) --latex-dir=src-tex --latex --allow-unsolved-metas
thesis: thesis/main.pdf

src-tex:
	mkdir -p src-tex
src-tex/%.tex: $(SRC)/%.lagda src-tex thesis.fmt
	lhs2TeX --agda -o $@ $<

thesis/%.tex: thesis/%.lagda thesis.fmt
	lhs2TeX --agda -o $@ $<

thesis/main.pdf: $(THESIS_TEX:%=thesis/%.tex) $(MODULES:%=src-tex/%.tex) thesis/agda.sty thesis/main.bib thesis/main.sty
	cd thesis; latexmk -xelatex -outdir=out main.tex
	cp thesis/out/main.pdf thesis/main.pdf
	rm thesis/out/main.pdf

cleanthesis:
	rm -rf src-tex
	rm -rf thesis/out
	rm -rf $(THESIS_TEX:%=thesis/%.tex)
	rm -rf thesis/literature.rel


.PHONY: default all clean code cleancode proposal cleanproposal thesis cleanthesis
