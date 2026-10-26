# Build: make (pdflatex + bibtex + pdflatex until cross-references converge, at most 5 passes);
# make check (log hygiene and exact rational parameter checks); make clean
MAIN = main
TEX  = pdflatex -interaction=nonstopmode -halt-on-error -file-line-error
RERUN = Rerun to get|Label\(s\) may have changed|Rerun LaTeX
MAXPASSES = 5

SECTIONS := $(wildcard sections/*.tex)

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(SECTIONS) refs.bib alphakey.bst
	$(TEX) $(MAIN) > /dev/null || (tail -40 $(MAIN).log; exit 1)
	bibtex $(MAIN) > /dev/null || (cat $(MAIN).blg; exit 1)
	@i=1; while :; do \
	  echo "$(TEX) $(MAIN)   [pass $$i after bibtex]"; \
	  $(TEX) $(MAIN) > /dev/null || { tail -40 $(MAIN).log; exit 1; }; \
	  if ! grep -q -E "$(RERUN)" $(MAIN).log; then \
	    echo "converged after $$i pass(es)"; break; fi; \
	  if [ $$i -ge $(MAXPASSES) ]; then echo "WARNING: no convergence after $(MAXPASSES) passes"; break; fi; \
	  i=$$((i+1)); \
	done
	@$(MAKE) --no-print-directory check

check:
	@echo "--- undefined references / citations ---"
	@grep -E "Warning: (Reference|Citation).*undefined|There were undefined" $(MAIN).log || echo "none"
	@echo "--- rerun requests (build convergence) ---"
	@grep -E "$(RERUN)" $(MAIN).log || echo "none"
	@echo "--- multiply defined labels ---"
	@grep -E "multiply defined" $(MAIN).log || echo "none"
	@echo "--- overfull boxes > 10pt ---"
	@python3 tools/overfull.py $(MAIN).log 10 || true
	@echo "--- bibtex warnings ---"
	@grep -E "^Warning--" $(MAIN).blg || echo "none"
	@echo "--- style gate ---"
	@python3 tools/style_gate.py
	@echo "--- parameter row checks ---"
	@python3 tools/h5_rows_check.py > /dev/null && echo "ALL OK"
	@echo "--- pages ---"
	@grep -E "Output written" $(MAIN).log || true

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out $(MAIN).toc $(MAIN).pdf sections/*.aux

.PHONY: all check clean
