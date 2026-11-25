.PHONY: all calculus check open-signatures clean
all: calculus.pdf open-signatures.pdf type-rules.pdf

calculus: calculus.pdf

calculus.pdf: calculus.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error calculus.tex

# Check calculus.tex against the Rocq sources (needs the proof library built).
check:
	$(MAKE) -C ../../progress check-docs

open-signatures: open-signatures.pdf

OPEN_SIGNATURE_TEX = open-signatures.tex open-signatures-core.tex \
	open-signatures-elaboration.tex open-signatures-examples.tex \
	open-signatures-theorems.tex open-signatures-references.tex

open-signatures.pdf: $(OPEN_SIGNATURE_TEX)
	latexmk -pdf -interaction=nonstopmode -halt-on-error open-signatures.tex

type-rules.pdf: type-rules.tex side-conditions.tex computation.tex theorems.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error type-rules.tex

clean:
	latexmk -c calculus.tex
	latexmk -c open-signatures.tex
	latexmk -c type-rules.tex
