# Build: make (pdflatex until cross-references converge, at most 5 passes; the bibliography is inline);
# make check (log hygiene); make clean
MAIN = main
TEX  = pdflatex -interaction=nonstopmode -halt-on-error -file-line-error
RERUN = Rerun to get|Label\(s\) may have changed|Rerun LaTeX
MAXPASSES = 5

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	@i=1; while :; do \
	  echo "$(TEX) $(MAIN)   [pass $$i]"; \
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
	@echo "--- pages ---"
	@grep -E "Output written" $(MAIN).log || true

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc $(MAIN).pdf

.PHONY: all check clean
