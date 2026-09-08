.PHONY: all clean
all: type-rules.pdf

type-rules.pdf: type-rules.tex side-conditions.tex computation.tex theorems.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error type-rules.tex

clean:
	latexmk -c type-rules.tex
