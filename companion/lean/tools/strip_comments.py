#!/usr/bin/env python3
"""Lexer-accurate Lean 4 comment stripper for semantic-freeze verification.

Preserves string literals ("..." and raw r#"..."#), character literals ('...'),
and quoted identifiers («...») intact while stripping:
  - `-- ...` line comments (leaving the trailing newline intact), and
  - nested `/- ... -/` block comments (including `/-- ... -/` docstrings and
    `/-! ... -/` module docstrings).
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from typing import List, Tuple

COMMENT_KINDS = frozenset({"line_comment", "block_comment", "docstring", "moduledoc"})


def _is_ident_char_before_prime(ch: str) -> bool:
    """Return True if `ch` can precede a trailing identifier prime `'` in Lean 4."""
    if ch.isalnum() or ch in "_'!?":
        return True
    if ord(ch) > 127 and ch not in "«»⟨⟩⟪⟫⦃⦄（）":
        return True
    return False


def lex_lean(src: str, filename: str = "<input>") -> List[Tuple[str, int, int]]:
    """Partition `src` into contiguous `(kind, start, end)` spans.

    Raises ValueError on unclosed block comments, stray `-/`, or unclosed strings.
    """
    n = len(src)
    i = 0
    spans: List[Tuple[str, int, int]] = []
    code_start = 0

    def flush_code(pos: int) -> None:
        nonlocal code_start
        if pos > code_start:
            spans.append(("code", code_start, pos))
        code_start = pos

    while i < n:
        c = src[i]

        # 1. Line comment `-- ...` (up to but excluding `\n`)
        if c == "-" and i + 1 < n and src[i + 1] == "-":
            flush_code(i)
            start = i
            i += 2
            while i < n and src[i] != "\n":
                i += 1
            spans.append(("line_comment", start, i))
            code_start = i
            continue

        # 2. Block comment `/- ... -/` (with arbitrary nesting)
        if c == "/" and i + 1 < n and src[i + 1] == "-":
            flush_code(i)
            start = i
            if i + 2 < n and src[i + 2] == "-" and not (i + 3 < n and src[i + 3] == "/"):
                kind = "docstring"
            elif i + 2 < n and src[i + 2] == "!" and not (i + 3 < n and src[i + 3] == "/" and i + 2 == n):
                kind = "moduledoc"
            else:
                kind = "block_comment"
            i += 2
            depth = 1
            while i < n and depth > 0:
                if src[i] == "/" and i + 1 < n and src[i + 1] == "-":
                    depth += 1
                    i += 2
                elif src[i] == "-" and i + 1 < n and src[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth != 0:
                line_no = src.count("\n", 0, start) + 1
                raise ValueError(f"{filename}:{line_no}: unclosed block comment `/-`")
            spans.append((kind, start, i))
            code_start = i
            continue

        # Reject stray `-/` outside comments/strings
        if c == "-" and i + 1 < n and src[i + 1] == "/":
            line_no = src.count("\n", 0, i) + 1
            raise ValueError(f"{filename}:{line_no}: stray closing comment delimiter `-/`")

        # 3. Raw string literal `r#*"..."#*`
        if c == "r" and i + 1 < n and src[i + 1] == "#":
            j = i + 1
            while j < n and src[j] == "#":
                j += 1
            if j < n and src[j] == '"':
                hashes = j - (i + 1)
                flush_code(i)
                start = i
                close_seq = '"' + ("#" * hashes)
                idx = src.find(close_seq, j + 1)
                if idx == -1:
                    line_no = src.count("\n", 0, start) + 1
                    raise ValueError(f"{filename}:{line_no}: unclosed raw string literal")
                i = idx + len(close_seq)
                spans.append(("string", start, i))
                code_start = i
                continue

        # 4. Standard string literal `"..."`
        if c == '"':
            flush_code(i)
            start = i
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                elif src[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                line_no = src.count("\n", 0, start) + 1
                raise ValueError(f"{filename}:{line_no}: unclosed string literal")
            spans.append(("string", start, i))
            code_start = i
            continue

        # 5. Character literal `'...'` (not trailing prime on an identifier)
        if c == "'":
            prev_is_ident = i > 0 and _is_ident_char_before_prime(src[i - 1])
            if not prev_is_ident:
                j = i + 1
                end_c = -1
                if j < n and src[j] == "\\":
                    if j + 1 < n and src[j + 1] == "x" and j + 4 < n and src[j + 4] == "'":
                        end_c = j + 5
                    elif j + 1 < n and src[j + 1] == "u" and j + 6 < n and src[j + 6] == "'":
                        end_c = j + 7
                    elif j + 2 < n and src[j + 2] == "'":
                        end_c = j + 3
                elif j + 1 < n and src[j] not in ("\n", "'") and src[j + 1] == "'":
                    end_c = j + 2
                if end_c != -1:
                    flush_code(i)
                    spans.append(("char", i, end_c))
                    i = end_c
                    code_start = i
                    continue

        # 6. Quoted identifier `«...»`
        if c == "«":
            end_g = src.find("»", i + 1)
            if end_g != -1:
                flush_code(i)
                spans.append(("guillemet", i, end_g + 1))
                i = end_g + 1
                code_start = i
                continue

        i += 1

    flush_code(n)
    return spans


def strip_comments_from_spans(
    src: str,
    spans: List[Tuple[str, int, int]],
    *,
    preserve_newlines: bool = False,
    strip_strings: bool = False,
) -> str:
    """Return `src` with all Lean 4 comments and docstrings stripped using precomputed `spans`."""
    out: List[str] = []
    for kind, a, b in spans:
        if kind == "line_comment":
            continue
        if kind in ("block_comment", "docstring", "moduledoc"):
            if preserve_newlines:
                nl_count = src.count("\n", a, b)
                if nl_count:
                    out.append("\n" * nl_count)
            continue
        if kind == "string" and strip_strings:
            out.append('""')
            continue
        out.append(src[a:b])
    return "".join(out)


def strip_comments(
    src: str,
    *,
    filename: str = "<input>",
    preserve_newlines: bool = False,
    strip_strings: bool = False,
) -> str:
    """Return `src` with all Lean 4 comments and docstrings stripped."""
    spans = lex_lean(src, filename=filename)
    return strip_comments_from_spans(
        src,
        spans,
        preserve_newlines=preserve_newlines,
        strip_strings=strip_strings,
    )


def iter_lean_files(repo_root: str) -> List[str]:
    """Return sorted relative paths of all `IntMul` library `.lean` files (`IntMul.lean` and `IntMul/*.lean`)."""
    rel_paths: List[str] = []
    root_file = os.path.join(repo_root, "IntMul.lean")
    if os.path.isfile(root_file):
        rel_paths.append("IntMul.lean")
    lib_dir = os.path.join(repo_root, "IntMul")
    if os.path.isdir(lib_dir):
        for dp, dn, fn in os.walk(lib_dir):
            dn[:] = sorted(d for d in dn if not d.startswith("."))
            for f in sorted(fn):
                if f.endswith(".lean"):
                    full = os.path.join(dp, f)
                    rel_paths.append(os.path.relpath(full, repo_root))
    rel_paths.sort()
    return rel_paths


def compute_stripped_manifest(repo_root: str, *, preserve_newlines: bool = False) -> List[Tuple[str, str]]:
    """Return list of `(sha256_hex, rel_path)` for comment-stripped `.lean` files."""
    entries: List[Tuple[str, str]] = []
    for rel in iter_lean_files(repo_root):
        full = os.path.join(repo_root, rel)
        with open(full, "r", encoding="utf-8") as fh:
            src = fh.read()
        stripped = strip_comments(src, filename=rel, preserve_newlines=preserve_newlines)
        digest = hashlib.sha256(stripped.encode("utf-8")).hexdigest()
        entries.append((digest, rel))
    return entries


def main() -> int:
    ap = argparse.ArgumentParser(description="Strip comments and docstrings from Lean 4 files.")
    ap.add_argument("path", nargs="?", help="Path to a .lean file (or omit when using --manifest)")
    ap.add_argument(
        "--preserve-newlines",
        action="store_true",
        help="Preserve newline counts inside block comments so line numbers stay fixed.",
    )
    ap.add_argument(
        "--strip-strings",
        action="store_true",
        help='Also replace string literals with "" (escape-hatch scan mode).',
    )
    ap.add_argument("--manifest", help="Compute stripped SHA-256 manifest for a repo directory.")
    ap.add_argument("--out", help="Write output to file instead of stdout.")
    args = ap.parse_args()

    if args.manifest:
        entries = compute_stripped_manifest(args.manifest, preserve_newlines=args.preserve_newlines)
        text = "".join(f"{h}  {rel}\n" for h, rel in entries)
    elif args.path:
        with open(args.path, "r", encoding="utf-8") as fh:
            src = fh.read()
        text = strip_comments(
            src,
            filename=args.path,
            preserve_newlines=args.preserve_newlines,
            strip_strings=args.strip_strings,
        )
    else:
        ap.error("Provide either a .lean file path or --manifest <repo_root>.")
        return 2

    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
