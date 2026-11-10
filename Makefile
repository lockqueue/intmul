# Top-level Makefile for IntMul_release_2026-10-25 (short, full and companion papers, Lean 4 formalizations, Python reference, and C/GMP package).
# Default target prints usage (`make all` is intentionally NOT the implicit default).

.DEFAULT_GOAL := help

SHELL  := /bin/bash
PYTHON ?= python3
LAKE   ?= lake

# Python 3.13 reference implementation ([Code26]) configuration.
PYREF_DIR  ?= python
PYREF_PY   := .venv/bin/python
PYREF_JOBS ?= auto

# Cap Lean worker fan-out by default so 64+ core Linux hosts do not hit the
# system-wide `fs.file-max` (ENFILE) limit via mmap'ed .olean files.
# Callers may override either variable via environment or command line.
LEAN_NUM_THREADS    ?= 16
LEAN_IMPORT_WORKERS ?= 4
export LEAN_NUM_THREADS
export LEAN_IMPORT_WORKERS

# Prevent Python verification scripts from writing __pycache__/*.pyc into the tree.
export PYTHONDONTWRITEBYTECODE := 1

# Set UPDATE_ROOT_PDFS=1 to copy freshly compiled PDFs over top-level IntMul_short_paper.pdf,
# IntMul_main_paper.pdf and companion/IntMul_companion_paper.pdf (left 0 by default so `make pdf` + `make test`
# preserves the exact archive hashes recorded in MANIFEST.sha256 across TeX Live versions).
UPDATE_ROOT_PDFS ?= 0

.PHONY: help pdf impl pyref-venv pytest pytest-slow pyref-reports lean lean-cache manifests static-checks test all clean

help:
	@echo "Available targets (default: help):"
	@echo "  make test           Run all quick checks (~2-3 min): SHA-256 manifests,"
	@echo "                      semantic-freeze & escape-hatch scans (lean/ + companion/lean/),"
	@echo "                      parameter/number checks, C/GMP build + selftest, and all three PDF builds"
	@echo "  make pdf            Compile short_paper/ (short paper), latex/ (full paper) and companion/latex/ ([MS])"
	@echo "                      (pass UPDATE_ROOT_PDFS=1 to overwrite root IntMul_short_paper.pdf,"
	@echo "                       IntMul_main_paper.pdf and companion/IntMul_companion_paper.pdf)"
	@echo "  make impl           Build companion/impl/intmul_fastdft and run selftest"
	@echo "  make pyref-venv     Create Python 3.13 virtualenv in $(PYREF_DIR)/.venv and install"
	@echo "                      pinned dependencies (falls back to 'uv' if ensurepip is absent)"
	@echo "  make pytest         Run fast Python 3.13 reference suite (~1,833 tests; PYREF_JOBS=$(PYREF_JOBS))"
	@echo "  make pytest-slow    Run slow Python 3.13 reference suite (234 tests; PYREF_JOBS=$(PYREF_JOBS))"
	@echo "  make pyref-reports  Run exact h=100 network-certificate and 71-config error reports (~30 s)"
	@echo "  make lean-cache     Download prebuilt Mathlib .olean caches for lean/ and"
	@echo "                      companion/lean/ via 'lake exe cache get'"
	@echo "  make lean           Build lean/ (~30 min + standalone axiom gates) and"
	@echo "                      companion/lean/ (~10 min + 'lake env lean checks/EvalProven.lean' about 15 s;"
	@echo "                      defaults: LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) LEAN_IMPORT_WORKERS=$(LEAN_IMPORT_WORKERS))"
	@echo "  make manifests      Verify top-level and component SHA-256 manifests (lean/, companion/lean/, python/, companion/impl/)"
	@echo "  make static-checks  Run Lean semantic-freeze, escape-hatch, and parameter/number checks"
	@echo "  make all            Run pdf, impl, pyref-venv, pytest, lean, and test sequentially"
	@echo "  make clean          Remove LaTeX, C, and pytest intermediates (keeps .lake and $(PYREF_DIR)/.venv)"

pdf:
	@echo "=== [pdf] Building short paper in short_paper/ ==="
	$(MAKE) -C short_paper clean
	$(MAKE) -C short_paper
	@test -s short_paper/main.pdf
	@if [ "$(UPDATE_ROOT_PDFS)" = "1" ] || [ ! -s IntMul_short_paper.pdf ]; then \
		cp short_paper/main.pdf IntMul_short_paper.pdf; \
	fi
	@test -s IntMul_short_paper.pdf
	@echo "=== [pdf] Building full paper in latex/ ==="
	$(MAKE) -C latex clean
	$(MAKE) -C latex
	@test -s latex/main.pdf
	@if [ "$(UPDATE_ROOT_PDFS)" = "1" ] || [ ! -s IntMul_main_paper.pdf ]; then \
		cp latex/main.pdf IntMul_main_paper.pdf; \
	fi
	@test -s IntMul_main_paper.pdf
	@echo "=== [pdf] Building companion manuscript [MS] in companion/latex/ ==="
	$(MAKE) -C companion/latex clean
	$(MAKE) -C companion/latex
	@test -s companion/latex/main.pdf
	@if [ "$(UPDATE_ROOT_PDFS)" = "1" ] || [ ! -s companion/IntMul_companion_paper.pdf ]; then \
		cp companion/latex/main.pdf companion/IntMul_companion_paper.pdf; \
	fi
	@test -s companion/IntMul_companion_paper.pdf

impl:
	@echo "=== [impl] Building companion/impl C/GMP binary and running selftest ==="
	@set -e; \
	if [ -n "$${LDLIBS:-}" ]; then \
		export LDLIBS="$$LDLIBS"; \
	elif printf 'int main(void){return 0;}\n' | $${CC:-gcc} -x c - -o /dev/null -lmpfr -lgmp -lm >/dev/null 2>&1; then \
		export LDLIBS="-lmpfr -lgmp -lm"; \
	elif printf 'int main(void){return 0;}\n' | $${CC:-gcc} -x c - -o /dev/null -l:libmpfr.so.6 -l:libgmp.so.10 -lm >/dev/null 2>&1; then \
		export LDLIBS="-l:libmpfr.so.6 -l:libgmp.so.10 -lm"; \
	fi; \
	$(MAKE) -C companion/impl clean all; \
	$(MAKE) -C companion/impl selftest

pyref-venv:
	@echo "=== [pyref] Creating the Python 3.13 virtual environment in $(PYREF_DIR)/.venv ==="
	@set -e; cd "$(PYREF_DIR)"; \
	export PATH="$$PATH:$$HOME/.local/bin"; \
	if python3.13 -m venv .venv >/dev/null 2>&1 && "$(PYREF_PY)" -m pip install -q -r requirements-lock.txt; then \
		true; \
	elif command -v uv >/dev/null 2>&1; then \
		echo "  (python3.13 -m venv lacks ensurepip; falling back to 'uv venv --python python3.13 --seed')"; \
		rm -rf .venv; \
		uv venv --python python3.13 --seed .venv; \
		uv pip install -q --python "$(PYREF_PY)" -r requirements-lock.txt; \
	else \
		rm -rf .venv; \
		python3.13 -m venv .venv && "$(PYREF_PY)" -m pip install -q -r requirements-lock.txt; \
	fi

pytest:
	@echo "=== [pyref] Running fast pytest suite (~1,833 tests; PYREF_JOBS=$(PYREF_JOBS)) ==="
	cd $(PYREF_DIR) && PYTHONDONTWRITEBYTECODE=1 $(PYREF_PY) -m pytest -q -n $(PYREF_JOBS) -p no:cacheprovider

pytest-slow:
	@echo "=== [pyref] Running slow pytest suite (234 tests; PYREF_JOBS=$(PYREF_JOBS)) ==="
	cd $(PYREF_DIR) && PYTHONDONTWRITEBYTECODE=1 $(PYREF_PY) -m pytest -q -m slow -n $(PYREF_JOBS) -p no:cacheprovider

pyref-reports:
	@echo "=== [pyref] Running exact h=100 network-certificate and 71-configuration error reports ==="
	cd $(PYREF_DIR) && PYTHONDONTWRITEBYTECODE=1 $(PYREF_PY) scripts/certify_report.py && PYTHONDONTWRITEBYTECODE=1 $(PYREF_PY) scripts/error_report.py

lean-cache:
	@echo "=== [lean-cache] Fetching prebuilt Mathlib .olean cache for lean/ ==="
	cd lean && $(LAKE) exe cache get
	@echo "=== [lean-cache] Fetching prebuilt Mathlib .olean cache for companion/lean/ ==="
	cd companion/lean && $(LAKE) exe cache get

lean:
	@echo "=== [lean] Building main Lean 4 project in lean/ (LEAN_NUM_THREADS=$(LEAN_NUM_THREADS), LEAN_IMPORT_WORKERS=$(LEAN_IMPORT_WORKERS)) ==="
	cd lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) build
	cd lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) env lean SubNLogN/GateCheck.lean
	cd lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) env lean IntMulTM/Headline.lean
	cd lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) env lean AxiomCheck.lean
	@echo "=== [lean] Building companion [MS] Lean 4 project in companion/lean/ (LEAN_NUM_THREADS=$(LEAN_NUM_THREADS), LEAN_IMPORT_WORKERS=$(LEAN_IMPORT_WORKERS)) ==="
	cd companion/lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) build
	@echo "=== [lean] Running standalone machine-size and axiom check companion/lean/checks/EvalProven.lean ==="
	cd companion/lean && LEAN_NUM_THREADS="$(LEAN_NUM_THREADS)" LEAN_IMPORT_WORKERS="$(LEAN_IMPORT_WORKERS)" $(LAKE) env lean checks/EvalProven.lean

manifests:
	@echo "=== [test] Verifying top-level and component SHA-256 manifests ==="
	sha256sum -c --quiet MANIFEST.sha256
	cd lean && sha256sum -c --quiet MANIFEST.sha256
	cd lean && sha256sum -c --quiet SPEC_LOCK.sha256
	cd companion/lean && sha256sum -c --quiet MANIFEST.sha256
	cd python && sha256sum -c --quiet MANIFEST.sha256
	cd companion/impl && sha256sum -c --quiet MANIFEST.sha256
	@echo "All SHA-256 manifests OK."

static-checks:
	@echo "=== [test] Running Lean semantic-freeze, escape-hatch, and parameter/number checks ==="
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B lean/tools/check_semantic_freeze.py --work lean
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B lean/tools/escape_scan.py lean > /dev/null
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B companion/lean/tools/check_semantic_freeze.py --work companion/lean
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B companion/lean/tools/escape_scan.py companion/lean > /dev/null
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B latex/tools/h5_rows_check.py > /dev/null
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B companion/latex/tools/verify_numbers.py companion/latex > /dev/null
	@echo "All static & parameter checks OK."

test:
	$(MAKE) manifests
	$(MAKE) static-checks
	$(MAKE) impl
	$(MAKE) pdf
	$(MAKE) clean
	sha256sum -c --quiet MANIFEST.sha256
	@echo "=== [test] ALL QUICK CHECKS PASSED ==="

all:
	$(MAKE) pdf
	$(MAKE) impl
	$(MAKE) pyref-venv
	$(MAKE) pytest
	$(MAKE) lean
	$(MAKE) test

clean:
	@if [ -f short_paper/Makefile ]; then $(MAKE) -C short_paper clean; fi
	@if [ -f latex/Makefile ]; then $(MAKE) -C latex clean; fi
	@if [ -f companion/latex/Makefile ]; then $(MAKE) -C companion/latex clean; fi
	@if [ -f companion/impl/Makefile ]; then $(MAKE) -C companion/impl clean; fi
	@rm -rf latex/tools/__pycache__ lean/tools/__pycache__ lean/replay/__pycache__ companion/latex/tools/__pycache__ companion/lean/tools/__pycache__
	@rm -rf $(PYREF_DIR)/.pytest_cache $(PYREF_DIR)/.hypothesis \
		$(PYREF_DIR)/__pycache__ \
		$(PYREF_DIR)/subnlogn/__pycache__ $(PYREF_DIR)/subnlogn/*/__pycache__ $(PYREF_DIR)/subnlogn/*/*/__pycache__ \
		$(PYREF_DIR)/tests/__pycache__ $(PYREF_DIR)/tests/*/__pycache__ \
		$(PYREF_DIR)/scripts/__pycache__ $(PYREF_DIR)/scripts/*/__pycache__
