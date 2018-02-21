all:
	pdflatex quals.tex
	bibtex quals
	pdflatex quals.tex
	bibtex quals
	pdflatex quals.tex
