# Build: make (pdflatex + bibtex + pdflatex until cross-references converge, at most 5 passes);
# make check (log hygiene, style gate, and parameter/number verification); make clean
MAIN = main
TEX  = pdflatex -interaction=nonstopmode -halt-on-error -file-line-error

SECTIONS := $(wildcard sections/*.tex)

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(SECTIONS) refs.bib alphakey.bst
	$(TEX) $(MAIN).tex > /dev/null
	bibtex $(MAIN) > /dev/null
	$(TEX) $(MAIN).tex > /dev/null
	$(TEX) $(MAIN).tex > /dev/null
	@python3 -B -c 'import pathlib, re, subprocess; p = pathlib.Path("$(MAIN).log"); \
	  subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "$(MAIN).tex"], stdout=subprocess.DEVNULL, check=True) \
	  if re.search(r"Rerun to get|Label\(s\) may have changed|Rerun LaTeX", p.read_text(errors="replace")) else None'
	@$(MAKE) --no-print-directory check

check:
	@python3 -B -c 'import pathlib, re, sys; \
	  log = pathlib.Path("$(MAIN).log").read_text(errors="replace"); \
	  blg = pathlib.Path("$(MAIN).blg").read_text(errors="replace") if pathlib.Path("$(MAIN).blg").exists() else ""; \
	  errs = []; \
	  [errs.append(m.group(0)) for pat in [r"LaTeX Warning: (?:Reference|Citation)[^\n]*undefined", r"LaTeX Warning: Label[^\n]*multiply defined", r"LaTeX Warning: There were (?:undefined|multiply-defined)[^\n]*", r"(?:Rerun to get|Label\(s\) may have changed|Rerun LaTeX)[^\n]*", r"Package hyperref Warning:[^\n]*"] for m in re.finditer(pat, log)]; \
	  [errs.append(m.group(0)) for m in re.finditer(r"^Warning--[^\n]*|---line \d+ of file[^\n]*", blg, re.M)]; \
	  print("Log & BibTeX hygiene:", "OK" if not errs else "FAIL\n" + "\n".join(errs)); \
	  m_out = re.search(r"Output written on [^\n]+", log); \
	  print(m_out.group(0) if m_out else ""); \
	  sys.exit(1 if errs else 0)'
	@python3 -B tools/overfull.py $(MAIN).log 3.0 --fail
	@python3 -B tools/style_gate.py .
	@python3 -B tools/verify_numbers.py .

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out $(MAIN).toc $(MAIN).pdf sections/*.aux
	rm -rf tools/__pycache__

.PHONY: all check clean
