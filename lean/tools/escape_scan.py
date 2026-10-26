#!/usr/bin/env python3
"""Escape-hatch scanner for the Lean 4 repository (`VERIFICATION_escape_scan.md`).

Scans all library `.lean` files (`replay/` excluded as non-library) with comments and string
literals stripped (preserving source line numbers across multi-line comments and multi-line
string literals) and checks 26 escape-hatch and metaprogramming patterns plus all `set_option`
declarations.
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import sys
from typing import Dict, List, Tuple

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if THIS_DIR not in sys.path:
    sys.path.insert(0, THIS_DIR)

from strip_comments import iter_lean_files, lex_lean  # noqa: E402

PATTERNS: List[Tuple[str, re.Pattern[str]]] = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom decl", re.compile(r"(?:^|\s)axiom\s+[A-Za-z_α-ωΑ-Ω]")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("decide +kernel", re.compile(r"\bdecide\s+\+kernel\b")),
    ("ofReduceBool/ofReduceNat", re.compile(r"\b(?:ofReduceBool|ofReduceNat)\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"@\[[^\]]*\bextern\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("opaque", re.compile(r"(?:^|\s)opaque\s+")),
    ("partial def", re.compile(r"\bpartial\s+def\b")),
    ("skipKernelTC/debug.*", re.compile(r"\b(?:skipKernelTC|debug\.[A-Za-z0-9_]+)\b")),
    ("#exit", re.compile(r"#exit\b")),
    ("macro_rules", re.compile(r"\bmacro_rules\b")),
    ("macro decl", re.compile(r"(?:^|\s)macro\s+")),
    ("syntax decl", re.compile(r"(?:^|\s)syntax\s+")),
    ("elab decl", re.compile(r"(?:^|\s)(?:elab|elab_rules)\b")),
    (
        "notation/infix/prefix/postfix",
        re.compile(r"(?:^|\s)(?:(?:local|scoped)\s+)?(?:notation|infix[lr]?|prefix|postfix)\b"),
    ),
    ("run_cmd/run_tac/run_elab", re.compile(r"\b(?:run_cmd|run_tac|run_elab)\b")),
    ("attribute [-...] (instance/simp removal)", re.compile(r"attribute\s*\[-\s*[A-Za-z_]")),
    (
        "local/scoped instance",
        re.compile(
            r"(?:attribute\s*\[(?:local|scoped)\s+instance\b|\b(?:local|scoped)\s+instance\b)"
        ),
    ),
    ("import Lean", re.compile(r"(?:^|\s)import\s+Lean\b")),
    ("Lean.Elab/Lean.Meta use", re.compile(r"\bLean\.(?:Elab|Meta)\b")),
    ("csimp", re.compile(r"@\[[^\]]*\bcsimp\b")),
    (
        "Decidable instance decl",
        re.compile(r"\binstance\b[^\n:]*:\s*(?:Decidable|DecidableEq|DecidablePred|DecidableRel)\b"),
    ),
    ("Classical.choice explicit", re.compile(r"\bClassical\.choice\b")),
]

RE_SET_OPTION = re.compile(r"\bset_option\s+([A-Za-z0-9_.]+)")


def strip_comments_and_strings_line_preserving(src: str, filename: str) -> str:
    spans = lex_lean(src, filename=filename)
    parts: List[str] = []
    for kind, a, b in spans:
        if kind == "line_comment":
            continue
        if kind in ("block_comment", "docstring", "moduledoc"):
            nl = src.count("\n", a, b)
            if nl:
                parts.append("\n" * nl)
            continue
        if kind == "string":
            nl = src.count("\n", a, b)
            parts.append('""' + ("\n" * nl))
            continue
        parts.append(src[a:b])
    return "".join(parts)


def run_scan(repo_root: str, header_line: str) -> Tuple[str, Dict[str, int]]:
    lean_files = iter_lean_files(repo_root)
    hits_by_pat: Dict[str, List[str]] = {name: [] for name, _ in PATTERNS}
    set_opts: collections.Counter[str] = collections.Counter()

    for rel in lean_files:
        full = os.path.join(repo_root, rel)
        with open(full, "r", encoding="utf-8") as fh:
            src = fh.read()
        stripped = strip_comments_and_strings_line_preserving(src, rel)
        lines = stripped.split("\n")
        for idx, ln in enumerate(lines, 1):
            for m in RE_SET_OPTION.finditer(ln):
                set_opts[m.group(1)] += 1
            for name, rx in PATTERNS:
                if rx.search(ln):
                    hits_by_pat[name].append(f"{rel}:{idx}: {ln.strip()}")

    out: List[str] = []
    out.append(header_line)
    out.append("")
    out.append(
        f"Files scanned: {len(lean_files)} library .lean files under AxiomCheck.lean, Contracts, IntMul, "
        "IntMul.lean, IntMulTM, LevelSync, WP, SubNLogN (the lakefile defaultTargets; standalone replay wrappers "
        "and negative-control .lean files in replay/ are not part of the lake build targets and are excluded)."
    )
    out.append("")
    out.append("| pattern | hits |")
    out.append("|---|---|")
    for name, _ in PATTERNS:
        out.append(f"| {name} | {len(hits_by_pat[name])} |")
    out.append("")
    opts_str = ", ".join(f"{k}×{set_opts[k]}" for k in sorted(set_opts))
    out.append(f"`set_option` names used (count): {opts_str}")
    out.append("")
    for name, _ in PATTERNS:
        hlist = hits_by_pat[name]
        if hlist:
            out.append("")
            out.append(f"## {name} ({len(hlist)} hits; first 40)")
            out.append("```")
            for item in hlist[:40]:
                out.append(item)
            out.append("```")

    counts = {name: len(hits_by_pat[name]) for name, _ in PATTERNS}
    return "\n".join(out) + "\n", counts


def main() -> int:
    ap = argparse.ArgumentParser(description="Run escape-hatch scan over Lean 4 sources.")
    ap.add_argument(
        "repo",
        nargs="?",
        default=os.path.dirname(THIS_DIR),
        help="Repository root directory (defaults to parent of tools/).",
    )
    ap.add_argument("--out", help="Write Markdown report to this path.")
    ap.add_argument(
        "--header",
        default="# Escape-hatch scan of the distributed tree (from git archive 3480d37), comments and strings stripped",
        help="Top-level Markdown heading.",
    )
    args = ap.parse_args()
    report, counts = run_scan(args.repo, args.header)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(report)
    else:
        sys.stdout.write(report)

    critical = ("sorry", "admit", "axiom decl", "native_decide")
    if any(counts[k] != 0 for k in critical):
        print(
            f"FAIL: critical escape-hatch counts nonzero: { {k: counts[k] for k in critical} }",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
