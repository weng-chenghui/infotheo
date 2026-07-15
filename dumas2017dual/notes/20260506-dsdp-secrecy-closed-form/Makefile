LATEX := pdflatex
LATEXFLAGS := -interaction=nonstopmode

TEX := \
	20260506-dsdp-alice-secrecy-closed-form.tex \
	20260506-dsdp-nparty-secrecy-closed-form.tex

PDF := $(TEX:.tex=.pdf)

.PHONY: all clean distclean

all: $(PDF)

%.pdf: %.tex
	$(LATEX) $(LATEXFLAGS) "$<"
	$(LATEX) $(LATEXFLAGS) "$<"

clean:
	rm -f *.aux *.fdb_latexmk *.fls *.log *.out

distclean: clean
	rm -f $(PDF)
