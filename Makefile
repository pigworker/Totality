default : Totality.pdf

Totality.tex : Totality.lagda
	lhs2TeX --agda Totality.lagda > Totality.tex

Totality.aux : Totality.tex
	latex Totality

Totality.blg : Totality.aux Totality.bib
	bibtex Totality

Totality.dvi : Totality.tex Totality.blg
	latex Totality
	latex Totality

Totality.pdf : Totality.tex Totality.blg
	latex Totality
	pdflatex Totality
