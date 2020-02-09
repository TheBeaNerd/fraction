
all: clean paper.pdf

paper.pdf: paper.tex
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	$(RM) -rf *.pdf *.aux *.bbl *.blg *.dvi *.pag *.out *.log

