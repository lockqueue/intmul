#!/usr/bin/env python3
"""Lexer-accurate Lean 4 declaration signature extractor and comparator.

Extracts all `theorem`, `lemma`, `def`, `abbrev`, `instance`, `structure`,
`inductive`, `class`, `axiom`, and `opaque` signatures from a Lean 4 source tree,
ignoring comments and normalizing whitespace.

Modes:
1. Single-tree mode:
     python3 tools/extract_signatures.py [<repo_dir>] [--out SIGNATURES.txt]
   Outputs one normalized signature record per declaration.

2. Comparison mode:
     python3 tools/extract_signatures.py <orig_dir> <ported_dir> [--out SIGNATURES.diff] [--allow-private-shims]
   Produces a unified diff between the two signature lists and exits 0 if
   all original signatures are preserved (and no non-private declarations were
   added unless identical), or 1 on any signature modification/deletion.
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import sys
from typing import List, Optional, Tuple

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if THIS_DIR not in sys.path:
    sys.path.insert(0, THIS_DIR)

from strip_comments import COMMENT_KINDS, iter_lean_files, lex_lean  # noqa: E402

HEADER_DECL_KEYWORDS = frozenset(
    {"theorem", "lemma", "def", "abbrev", "instance", "axiom", "opaque"}
)
FULL_DECL_KEYWORDS = frozenset({"structure", "inductive", "class"})
ALL_DECL_KEYWORDS = HEADER_DECL_KEYWORDS | FULL_DECL_KEYWORDS

MODIFIER_KEYWORDS = frozenset(
    {"private", "protected", "noncomputable", "unsafe", "partial", "scoped", "local"}
)

TOP_STOP_KEYWORDS = frozenset(
    {
        "import",
        "namespace",
        "section",
        "end",
        "open",
        "variable",
        "universe",
        "set_option",
        "attribute",
        "elab",
        "elab_rules",
        "macro",
        "macro_rules",
        "syntax",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "termination_by",
        "decreasing_by",
    }
)

OPEN_BRACKETS = frozenset({"(", "[", "{", "⦃", "⟨", "⟪", "@["})
CLOSE_BRACKETS = frozenset({")", "]", "}", "⦄", "⟩", "⟫"})

# Multi-character operators/punctuators to keep intact during code tokenization
CODE_TOKEN_RE = re.compile(
    r"""
    @\[
    | :=
    | =>
    | \|\|
    | &&
    | -> | ← | → | ↔ | ≤ | ≥ | ≠ | ≈ | ≡
    | [()\[\]{}⦃⦄⟨⟩⟪⟫,:]
    | \|
    | ;
    | [^\s()\[\]{}⦃⦄⟨⟩⟪⟫,:|;]+
    """,
    re.VERBOSE,
)


class Token:
    __slots__ = ("kind", "text", "line", "col", "space_before", "space_after")

    def __init__(
        self,
        kind: str,
        text: str,
        line: int,
        col: int,
        space_before: bool,
        space_after: bool,
    ) -> None:
        self.kind = kind
        self.text = text
        self.line = line
        self.col = col
        self.space_before = space_before
        self.space_after = space_after


def tokenize_lean_code(src: str, filename: str) -> List[Token]:
    """Tokenize non-comment spans of `src` with 1-based line and 0-based column offsets."""
    spans = lex_lean(src, filename=filename)
    # Build line-start offsets for fast (line, col) lookup
    line_starts = [0]
    for idx, ch in enumerate(src):
        if ch == "\n":
            line_starts.append(idx + 1)

    import bisect

    def pos_to_line_col(pos: int) -> Tuple[int, int]:
        ln_idx = bisect.bisect_right(line_starts, pos) - 1
        return ln_idx + 1, pos - line_starts[ln_idx]

    n = len(src)
    tokens: List[Token] = []
    for skind, a, b in spans:
        if skind in COMMENT_KINDS:
            continue
        if skind in ("string", "char", "guillemet"):
            ln, col = pos_to_line_col(a)
            sb = a == 0 or src[a - 1].isspace()
            sa = b == n or src[b].isspace()
            tokens.append(Token(skind, src[a:b], ln, col, sb, sa))
            continue
        # skind == "code"
        chunk = src[a:b]
        for m in CODE_TOKEN_RE.finditer(chunk):
            gs, ge = a + m.start(), a + m.end()
            txt = m.group(0)
            ln, col = pos_to_line_col(gs)
            sb = gs == 0 or src[gs - 1].isspace()
            sa = ge == n or src[ge].isspace()
            tokens.append(Token("code", txt, ln, col, sb, sa))
    return tokens


def format_tokens_normalized(toks: List[Token]) -> str:
    """Format a token slice with canonical single-space whitespace normalization."""
    if not toks:
        return ""
    parts: List[str] = []
    no_space_after = {"(", "[", "{", "⦃", "⟨", "⟪", "@["}
    no_space_before = {")", "]", "}", "⦄", "⟩", "⟫", ",", ";"}
    for idx, t in enumerate(toks):
        if idx > 0:
            prev = toks[idx - 1]
            # Preserve tight absolute-value bars `|x|` vs spaced `| pat =>`
            if prev.text == "|" and not prev.space_after:
                need_space = False
            elif t.text == "|" and not t.space_before:
                need_space = False
            elif prev.text in no_space_after or t.text in no_space_before:
                need_space = False
            # Keep tight field projection / qualified names if originally adjacent
            elif (prev.text.endswith(".") or t.text.startswith(".")) and (
                not prev.space_after and not t.space_before
            ):
                need_space = False
            else:
                need_space = True
            if need_space:
                parts.append(" ")
        parts.append(t.text)
    return "".join(parts)


def _is_top_cmd_start(toks: List[Token], i: int) -> bool:
    """Return True if token `i` at column 0 begins a new top-level command or declaration."""
    t = toks[i]
    if t.col != 0:
        return False
    if t.text.startswith("#"):
        return True
    if t.text in ALL_DECL_KEYWORDS or t.text in MODIFIER_KEYWORDS or t.text in TOP_STOP_KEYWORDS:
        return True
    if t.text == "@[":
        return True
    return False


def _is_equation_arm_pipe(toks: List[Token], i: int, end_limit: int) -> bool:
    """Return True if `toks[i]` (`|`) at bracket depth 0 starts a pattern-matching arm `| ... =>`."""
    t = toks[i]
    if t.text != "|":
        return False
    # Pattern-matching arm `|` is separated by whitespace on both sides (never `|x|`)
    if not (t.space_before and t.space_after):
        return False
    # Look ahead up to the next column-0 command or `|`/`:=` at depth 0 for `=>`
    depth = 0
    j = i + 1
    while j < end_limit:
        tj = toks[j]
        if depth == 0 and j > i + 1 and _is_top_cmd_start(toks, j):
            return False
        if tj.text in OPEN_BRACKETS:
            depth += 1
        elif tj.text in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if tj.text == "=>":
                return True
            if tj.text == ":=":
                return False
        j += 1
    return False


def extract_file_signatures(src: str, rel_path: str) -> List[Tuple[str, bool, str]]:
    """Return list of `(formatted_record, is_private, decl_kind)` for `rel_path`."""
    toks = tokenize_lean_code(src, filename=rel_path)
    n = len(toks)
    records: List[Tuple[str, bool, str]] = []
    ns_stack: List[str] = []

    i = 0
    while i < n:
        t = toks[i]

        # Track `namespace Foo.Bar` and `end Foo.Bar` at column 0
        if t.col == 0 and t.text == "namespace" and i + 1 < n:
            ns_name = toks[i + 1].text
            for part in ns_name.split("."):
                if part:
                    ns_stack.append(part)
            i += 2
            continue
        if t.col == 0 and t.text == "section":
            if i + 1 < n and toks[i + 1].line == t.line and toks[i + 1].col > 0:
                ns_stack.append(f"<section:{toks[i + 1].text}>")
                i += 2
            else:
                ns_stack.append("<section>")
                i += 1
            continue
        if t.col == 0 and t.text == "end":
            if i + 1 < n and toks[i + 1].line == t.line and toks[i + 1].col > 0:
                end_name = toks[i + 1].text
                parts = [p for p in end_name.split(".") if p]
                for _ in parts:
                    if ns_stack:
                        ns_stack.pop()
                i += 2
            else:
                if ns_stack:
                    ns_stack.pop()
                i += 1
            continue

        # Handle `open ... in` prefix at column 0 before a declaration/command
        if t.col == 0 and t.text == "open":
            j = i + 1
            while j < n and not (toks[j].col == 0 and j > i):
                if toks[j].text == "in":
                    j += 1
                    break
                j += 1
            i = j
            continue

        # Check for declaration start (optional `@[...]` and modifier keywords)
        if t.col == 0 and (
            t.text == "@[" or t.text in MODIFIER_KEYWORDS or t.text in ALL_DECL_KEYWORDS
        ):
            start_i = i
            j = i
            is_private = False
            while j < n:
                tj = toks[j]
                if tj.text == "@[":
                    depth = 1
                    j += 1
                    while j < n and depth > 0:
                        if toks[j].text in OPEN_BRACKETS:
                            depth += 1
                        elif toks[j].text in CLOSE_BRACKETS:
                            depth -= 1
                        j += 1
                    continue
                if tj.text in MODIFIER_KEYWORDS:
                    if tj.text == "private":
                        is_private = True
                    j += 1
                    continue
                break

            if j < n and toks[j].text in ALL_DECL_KEYWORDS:
                decl_kw = toks[j].text
                ns_prefix = ".".join(p for p in ns_stack if not p.startswith("<section"))
                scope_tag = f"{rel_path} [{ns_prefix}]" if ns_prefix else rel_path

                if decl_kw in FULL_DECL_KEYWORDS:
                    # Capture full `structure` / `inductive` / `class` block including `deriving`
                    k = j + 1
                    while k < n:
                        if toks[k].col == 0 and k > j:
                            if toks[k].text == "deriving":
                                # Include `deriving ...` line(s)
                                k += 1
                                while k < n and toks[k].col > 0:
                                    k += 1
                                break
                            break
                        k += 1
                    sig_str = format_tokens_normalized(toks[start_i:k])
                    records.append((f"{scope_tag} :: {sig_str}", is_private, decl_kw))
                    i = k
                    continue

                # Header declaration (`theorem`, `lemma`, `def`, `abbrev`, `instance`, `axiom`, `opaque`)
                k = j + 1
                depth = 0
                pending_let_assigns = 0
                while k < n:
                    tk = toks[k]
                    if depth == 0 and k > j + 1 and _is_top_cmd_start(toks, k):
                        break
                    if tk.text in OPEN_BRACKETS:
                        depth += 1
                        k += 1
                        continue
                    if tk.text in CLOSE_BRACKETS:
                        depth = max(0, depth - 1)
                        k += 1
                        continue
                    if depth == 0:
                        if tk.text in ("let", "have"):
                            pending_let_assigns += 1
                            k += 1
                            continue
                        if tk.text == ":=":
                            if pending_let_assigns > 0:
                                pending_let_assigns -= 1
                                k += 1
                                continue
                            break
                        if tk.text == "where":
                            break
                        if tk.text == "|" and _is_equation_arm_pipe(toks, k, n):
                            break
                    k += 1

                sig_str = format_tokens_normalized(toks[start_i:k])
                records.append((f"{scope_tag} :: {sig_str}", is_private, decl_kw))
                # Advance `i` to the next column-0 token after `k`
                i = max(k, j + 1)
                while i < n and toks[i].col != 0:
                    i += 1
                continue

        i += 1

    return records


def extract_repo_signatures(repo_root: str) -> List[Tuple[str, bool, str]]:
    all_records: List[Tuple[str, bool, str]] = []
    for rel in iter_lean_files(repo_root):
        full = os.path.join(repo_root, rel)
        with open(full, "r", encoding="utf-8") as fh:
            src = fh.read()
        all_records.extend(extract_file_signatures(src, rel))
    return all_records


def format_signatures_text(records: List[Tuple[str, bool, str]]) -> str:
    return "".join(f"{rec}\n" for rec, _, _ in records)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Extract or diff Lean 4 declaration signatures across a source tree."
    )
    ap.add_argument(
        "dirs",
        nargs="*",
        help="Either [<repo_dir>] for single-tree extraction or <orig_dir> <ported_dir> for diff mode.",
    )
    ap.add_argument("--out", help="Write SIGNATURES.txt or SIGNATURES.diff to this path.")
    ap.add_argument(
        "--allow-private-shims",
        action="store_true",
        help="In diff mode, exit 0 if additions are solely `private` compatibility declarations and zero original signatures changed.",
    )
    args = ap.parse_args()

    if len(args.dirs) == 0:
        target_dir = os.path.dirname(THIS_DIR)
        records = extract_repo_signatures(target_dir)
        text = format_signatures_text(records)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as fh:
                fh.write(text)
        else:
            sys.stdout.write(text)
        return 0

    if len(args.dirs) == 1:
        records = extract_repo_signatures(args.dirs[0])
        text = format_signatures_text(records)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as fh:
                fh.write(text)
        else:
            sys.stdout.write(text)
        return 0

    if len(args.dirs) == 2:
        orig_dir, port_dir = args.dirs
        orig_recs = extract_repo_signatures(orig_dir)
        port_recs = extract_repo_signatures(port_dir)
        orig_lines = [f"{r}\n" for r, _, _ in orig_recs]
        port_lines = [f"{r}\n" for r, _, _ in port_recs]

        diff_lines = list(
            difflib.unified_diff(
                orig_lines,
                port_lines,
                fromfile="original/SIGNATURES.txt",
                tofile="ported/SIGNATURES.txt",
                n=3,
            )
        )
        diff_text = "".join(diff_lines)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as fh:
                fh.write(diff_text)
        else:
            sys.stdout.write(diff_text)

        if not diff_lines:
            return 0

        if args.allow_private_shims:
            # Verify orig_recs is an exact subsequence of port_recs and every new entry is `private`
            orig_idx = 0
            added_non_private: List[str] = []
            for rec, is_priv, _ in port_recs:
                if orig_idx < len(orig_recs) and rec == orig_recs[orig_idx][0]:
                    orig_idx += 1
                else:
                    if not is_priv:
                        added_non_private.append(rec)
            if orig_idx == len(orig_recs) and not added_non_private:
                return 0

        return 1

    ap.error("Provide 0, 1, or 2 directory arguments.")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
