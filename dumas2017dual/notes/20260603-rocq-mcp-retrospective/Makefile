TEX := rocq-mcp-retrospective.tex
PDF := $(TEX:.tex=.pdf)

.PHONY: all data clean distclean

all: $(PDF)

# regenerate metrics.tex (+ metrics.json, samples.txt) from the transcripts
data:
	python3 parse.py

# latexmk runs pdflatex as many times as needed; halt on the first real error
%.pdf: %.tex metrics.tex
	latexmk -pdf -halt-on-error -interaction=nonstopmode "$<"

clean:
	latexmk -c "$(TEX)" 2>/dev/null || true
	rm -f *.aux *.fdb_latexmk *.fls *.log *.out

distclean: clean
	rm -f $(PDF)
