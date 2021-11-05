OUTDIR=build
BODY_PDF=main_body.pdf
# SUPPLEMENTARY_PDF=appendix.pdf

LATEXMK=latexmk -bibtex -dvi- -ps- -pdf -pdflatex="pdflatex -synctex=1 -halt-on-error -interaction=nonstopmode -file-line-error --shell-escape %O %S" -outdir=$(OUTDIR)

# LATEXMK=latexmk -bibtex -dvi- -ps- -pdf -pdflatex="pdflatex -halt-on-error --shell-escape %O %S" 
LATEXPAND=latexpand 

# LAST_PAGE=29
# SUPPLEMENTARY_START_PAGE=$(shell expr $(LAST_PAGE) + 1)

all: 
	$(LATEXMK) main

view: 
	$(LATEXMK) -pvc main

# # the page number is hard coded 
# appendix: all
# 	pdftk $(OUTDIR)/main.pdf cat 1-$(LAST_PAGE) output $(BODY_PDF)
# 	pdftk $(OUTDIR)/main.pdf cat $(SUPPLEMENTARY_START_PAGE)-end output $(SUPPLEMENTARY_PDF)
# #	gs -sDEVICE=pdfwrite -dNOPAUSE -dBATCH -dFirstPage=1 -dLastPage=$(LAST_PAGE) -sOutputFile=$(BODY_PDF) main.pdf 
# #	gs -sDEVICE=pdfwrite -dNOPAUSE -dBATCH -dFirstPage=$(SUPPLEMENTARY_START_PAGE) -sOutputFile=$(SUPPLEMENTARY_PDF) main.pdf 

# pack: 
# 	rm -rf ./camera_ready 
# 	mkdir ./camera_ready 
# 	$(LATEXMK) main
# 	$(LATEXPAND) -o ./camera_ready/main_bundle.tex --keep-comments main.tex
# 	cp acmart.cls ./camera_ready
# 	cp main.bib   ./camera_ready
# #	cp proof.sty  ./camera_ready
# #	cp Makefile_bundle ./camera_ready/Makefile
# #	cp main.pdf  ./camera_ready 
# 	zip -r camera_ready camera_ready

clean:
	rm -rf $(OUTDIR)
	latexmk -C main
	rm -rf $(BODY_PDF)
#	rm -rf $(SUPPLEMENTARY_PDF)
