#!/usr/bin/env python3
"""Attribute Overfull hbox/vbox warnings in main.log to the most recently opened .tex file.

Usage:
    python3 tools/overfull.py [main.log] [threshold_pt] [--fail]
"""

from __future__ import annotations

import pathlib
import re
import sys


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--fail"]
    fail_on_hit = "--fail" in sys.argv[1:]
    log_path = pathlib.Path(args[0] if len(args) > 0 else "main.log")
    thr = float(args[1]) if len(args) > 1 else 3.0

    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    cur = "main.tex"
    hits: list[str] = []

    pat = re.compile(
        r"\((\./[^\s()]+\.tex)"
        r"|(Overfull \\hbox \(([\d.]+)pt too wide\)[^\n]*)"
        r"|(Overfull \\vbox \(([\d.]+)pt too high\)[^\n]*)"
    )
    for m in pat.finditer(log_text):
        if m.group(1):
            cur = m.group(1)
        elif m.group(2) and float(m.group(3)) > thr:
            line = f"{cur}: {m.group(2)}"
            hits.append(line)
            print(line)
        elif m.group(4) and float(m.group(5)) > thr:
            line = f"{cur}: {m.group(4)}"
            hits.append(line)
            print(line)

    if fail_on_hit and hits:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
