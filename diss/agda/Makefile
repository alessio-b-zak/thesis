AGDA=agda
AFLAGS=-i. --latex
SOURCE=Thesis
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	$(LATEX) ./latex/Thesis.tex
