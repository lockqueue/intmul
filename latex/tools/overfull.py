#!/usr/bin/env python3
"""Attribute Overfull hbox warnings in main.log to the most recently opened section file.
Usage: tools/overfull.py [main.log] [threshold_pt]"""
import re, sys
log = open(sys.argv[1] if len(sys.argv) > 1 else "main.log", errors="replace").read()
thr = float(sys.argv[2]) if len(sys.argv) > 2 else 10.0
cur = "main.tex"
for m in re.finditer(r"\((\./[^\s()]+\.tex)|(Overfull \\hbox \(([\d.]+)pt too wide\)[^\n]*)", log):
    if m.group(1):
        cur = m.group(1)
    elif float(m.group(3)) > thr:
        print(f"{cur}: {m.group(2)}")
