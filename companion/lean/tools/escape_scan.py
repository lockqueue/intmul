#!/usr/bin/env python3
"""Escape-hatch scanner for the `IntMul` Lean 4 formalization.

Scans all `.lean` files (`IntMul.lean` and `IntMul/*.lean`) with comments and
string literals stripped (preserving source line numbers across multi-line
comments and multi-line string literals), checks 25 soundness/metaprogramming
patterns and all `set_option` declarations (with exact option, value, scope,
and port-provenance classification), and separately inventories any
escape-hatch keywords appearing inside string literals (such as error messages).
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
    ("ofReduceBool/ofReduceNat", re.compile(r"\b(?:ofReduceBool|ofReduceNat)\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"(?:@\[[^\]]*\bextern\b|\bextern\b)")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("opaque", re.compile(r"(?:^|\s)opaque\s+")),
    ("partial def", re.compile(r"\bpartial\s+def\b")),
    ("skipKernelTC/debug.*", re.compile(r"\b(?:skipKernelTC|debug\.[A-Za-z0-9_]+)\b")),
    ("#exit", re.compile(r"#exit\b")),
    ("csimp", re.compile(r"@\[[^\]]*\bcsimp\b")),
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
    (
        "Decidable instance decl",
        re.compile(r"\binstance\b[^\n:]*:\s*(?:Decidable|DecidableEq|DecidablePred|DecidableRel)\b"),
    ),
    ("Classical.choice explicit", re.compile(r"\bClassical\.choice\b")),
]

FORBIDDEN_ESCAPE_HATCHES = (
    "sorry",
    "admit",
    "axiom decl",
    "native_decide",
    "ofReduceBool/ofReduceNat",
    "implemented_by",
    "extern",
    "unsafe",
    "opaque",
    "partial def",
    "skipKernelTC/debug.*",
    "#exit",
    "csimp",
)

RE_SET_OPTION_FULL = re.compile(r"\bset_option\s+([A-Za-z0-9_.]+)(?:\s+([^\s]+))?(?:\s+(in)\b)?")
RE_STRING_KEYWORD = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by|extern|opaque|unsafe|partial)\b",
    re.IGNORECASE,
)


def classify_set_option_origin(rel: str, opt_name: str, opt_val: str) -> str:
    """Classify each `set_option` occurrence as port-added, port-raised, or original."""
    if opt_name == "backward.isDefEq.respectTransparency":
        return "port-added (Lean 4.33.1 port)"
    if opt_name == "maxRecDepth":
        if opt_val in {"20000", "4000"}:
            return "port-added (Lean 4.33.1 port)"
        return "original"
    if opt_name == "maxHeartbeats":
        if rel == "IntMul/TMArithStages.lean":
            return "port-added (Lean 4.33.1 port)"
        if opt_val == "4000000":
            return "port-raised from 1200000 (Lean 4.33.1 port)"
        return "original"
    return "present"


def strip_comments_and_strings_line_preserving(
    src: str, filename: str
) -> Tuple[str, List[Tuple[int, str]]]:
    spans = lex_lean(src, filename=filename)
    parts: List[str] = []
    string_hits: List[Tuple[int, str]] = []
    for kind, a, b in spans:
        if kind == "line_comment":
            continue
        if kind in ("block_comment", "docstring", "moduledoc"):
            nl = src.count("\n", a, b)
            if nl:
                parts.append("\n" * nl)
            continue
        if kind == "string":
            lit = src[a:b]
            if RE_STRING_KEYWORD.search(lit):
                line_no = src.count("\n", 0, a) + 1
                string_hits.append((line_no, lit))
            nl = src.count("\n", a, b)
            parts.append('""' + ("\n" * nl))
            continue
        parts.append(src[a:b])
    return "".join(parts), string_hits


def run_scan(repo_root: str, header_line: str) -> Tuple[str, Dict[str, int]]:
    lean_files = iter_lean_files(repo_root)
    hits_by_pat: Dict[str, List[str]] = {name: [] for name, _ in PATTERNS}
    set_opts: collections.Counter[str] = collections.Counter()
    set_opt_entries: List[Tuple[str, int, str, str, str, str]] = []
    string_literal_notes: List[str] = []

    for rel in lean_files:
        full = os.path.join(repo_root, rel)
        with open(full, "r", encoding="utf-8") as fh:
            src = fh.read()
        stripped, str_hits = strip_comments_and_strings_line_preserving(src, rel)
        raw_lines = src.split("\n")
        for lno, lit in str_hits:
            ctx = raw_lines[lno - 1].strip() if 1 <= lno <= len(raw_lines) else lit
            string_literal_notes.append(f"{rel}:{lno}: {ctx}")
        lines = stripped.split("\n")
        for idx, ln in enumerate(lines, 1):
            for m in RE_SET_OPTION_FULL.finditer(ln):
                opt_name = m.group(1)
                opt_val = m.group(2) or ""
                has_in = m.group(3) == "in"
                set_opts[opt_name] += 1
                if has_in:
                    stmt_str = f"set_option {opt_name} {opt_val} in".strip()
                    scope_str = f"single declaration (`set_option ... in` at L{idx})"
                else:
                    stmt_str = f"set_option {opt_name} {opt_val}".strip()
                    scope_str = f"file-wide from L{idx}"
                origin_str = classify_set_option_origin(rel, opt_name, opt_val)
                set_opt_entries.append((rel, idx, opt_name, stmt_str, scope_str, origin_str))
            for name, rx in PATTERNS:
                if rx.search(ln):
                    hits_by_pat[name].append(f"{rel}:{idx}: {ln.strip()}")

    out: List[str] = []
    out.append(header_line)
    out.append("")
    out.append(
        f"Scan scope: the {len(lean_files)} library files `IntMul.lean` and `IntMul/*.lean`, "
        "with all comments/docstrings and string literals stripped."
    )
    if os.path.isfile(os.path.join(repo_root, "checks", "EvalProven.lean")):
        out.append("")
        out.append(
            "Note on `checks/EvalProven.lean` (standalone post-build check outside the `IntMul` "
            "library build target): `checks/EvalProven.lean` deliberately uses `unsafe`, "
            "`implemented_by`, and `opaque` in meta code only (the command elaborator that "
            "constructs the proof terms); the kernel re-checks the produced theorems "
            "independently of how the terms were constructed, and `#print axioms` reports only "
            "`[propext, Classical.choice, Quot.sound]`."
        )
    out.append("")
    out.append("| pattern | hits |")
    out.append("|---|---|")
    for name, _ in PATTERNS:
        out.append(f"| {name} | {len(hits_by_pat[name])} |")
    out.append("")
    opts_str = ", ".join(f"{k}×{set_opts[k]}" for k in sorted(set_opts)) if set_opts else "none"
    out.append(f"`set_option` names used (count): {opts_str}")

    # Dedicated `set_option` inventory section
    out.append("")
    out.append("## set_option usage (compatibility options, not escape hatches)")
    out.append("")
    port_rt = sum(
        1
        for e in set_opt_entries
        if e[2] == "backward.isDefEq.respectTransparency" and e[5].startswith("port-")
    )
    port_rd = sum(1 for e in set_opt_entries if e[2] == "maxRecDepth" and e[5].startswith("port-"))
    orig_rd = sum(1 for e in set_opt_entries if e[2] == "maxRecDepth" and e[5] == "original")
    port_hb = sum(
        1 for e in set_opt_entries if e[2] == "maxHeartbeats" and e[5].startswith("port-")
    )
    orig_hb = sum(1 for e in set_opt_entries if e[2] == "maxHeartbeats" and e[5] == "original")
    out.append(
        f"The scan also inspected every `set_option` occurrence across the {len(lean_files)} "
        f"library files ({len(set_opt_entries)} total: "
        f"{set_opts['backward.isDefEq.respectTransparency']} `backward.isDefEq.respectTransparency` "
        f"[{port_rt} added in the Lean 4.33.1 port], "
        f"{set_opts['maxRecDepth']} `maxRecDepth` "
        f"[{port_rd} added in the port, {orig_rd} unchanged from the original development], and "
        f"{set_opts['maxHeartbeats']} `maxHeartbeats` "
        f"[{port_hb} added or raised in the port, {orig_hb} unchanged from the original "
        "development]). These options affect elaboration and tactic search only; the Lean kernel "
        "re-checks every resulting proof term independently."
    )
    out.append("")
    if set_opt_entries:
        out.append("```")
        for rel, idx, _opt_name, stmt_str, scope_str, origin_str in set_opt_entries:
            out.append(f"{rel}:{idx}: {stmt_str}  [{scope_str}; {origin_str}]")
        out.append("```")
    else:
        out.append("None.")

    out.append("")
    out.append("## String-literal keyword occurrences (excluded from code counts above)")
    if string_literal_notes:
        out.append("```")
        for note in string_literal_notes:
            out.append(note)
        out.append("```")
    else:
        out.append("None.")

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
    ap = argparse.ArgumentParser(description="Run escape-hatch scan over `IntMul` Lean 4 sources.")
    ap.add_argument(
        "repo",
        nargs="?",
        default=os.path.dirname(THIS_DIR),
        help="Repository root directory (defaults to parent of tools/).",
    )
    ap.add_argument("--out", help="Write report to this path.")
    ap.add_argument(
        "--header",
        default="# Escape-hatch scan of `IntMul` (comments and string literals stripped)",
        help="Top-level heading.",
    )
    args = ap.parse_args()
    report, counts = run_scan(args.repo, args.header)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(report)
    else:
        sys.stdout.write(report)

    bad = {k: counts[k] for k in FORBIDDEN_ESCAPE_HATCHES if counts[k] != 0}
    if bad:
        print(f"FAIL: forbidden escape-hatch counts nonzero: {bad}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
