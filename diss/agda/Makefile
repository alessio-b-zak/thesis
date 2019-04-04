AGDA=agda
AFLAGS=-i. --latex
SOURCE=Thesis
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -pdf -use-make -xelatex

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
