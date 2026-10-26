#!/usr/bin/env python3
"""Semantic-freeze verifier for the distributed Lean 4 repository.

Modes:
1. Comparison mode (`--orig <orig_repo> --work <work_repo>`):
   Verifies across all 2,011 library `.lean` files (`replay/` excluded as non-library) that:
   - Exact library file list matches (`2,011` library `.lean` files).
   - `SubNLogN/Challenge.lean` is 100% byte-identical with SHA-256
     `7aa50930921c494e50803b037c4cc6ed9be880c3f795e4b171e16ab59cf61fb5`.
   - `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are byte-identical.
   - Every library `.lean` file has balanced `/- ... -/` delimiters and valid string/char literals.
   - Comment-stripped sources are byte-identical under BOTH standard stripping
     (`/- ... -/` -> `""`) AND line-preserving stripping (`/- ... -/` -> `"\\n"*k`).
   - Every non-comment token/whitespace span is byte-identical span-for-span.
   - No docstring (`/--`), module docstring (`/-!`), block comment (`/-`), or
     line comment (`--`) was added, deleted, or changed in kind.
   - Generates (if `--write-manifest` is given) or verifies `MANIFEST_stripped.sha256`.

2. Standalone archive mode (no `--orig`, run inside the archive root or `--work <repo>`):
   Verifies all 2,011 library `.lean` files (`replay/` excluded as non-library) against
   `MANIFEST_stripped.sha256`, checks balanced comment delimiters, checks
   `SubNLogN/Challenge.lean` SHA-256, and checks `SPEC_LOCK.sha256`.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from typing import Dict, List, Tuple

from strip_comments import (
    COMMENT_KINDS,
    iter_lean_files,
    lex_lean,
    strip_comments,
    strip_comments_from_spans,
)

CHALLENGE_REL = "SubNLogN/Challenge.lean"
CHALLENGE_SHA256 = "7aa50930921c494e50803b037c4cc6ed9be880c3f795e4b171e16ab59cf61fb5"
EXPECTED_LEAN_COUNT = 2011
FROZEN_CONFIGS = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as fh:
        return sha256_bytes(fh.read())


def verify_spec_lock(work_root: str, errors: List[str]) -> None:
    """Verify SPEC_LOCK.sha256 (both full-file hashes and `# <hash>  <path> (comment-stripped)` lines)."""
    lock_path = os.path.join(work_root, "SPEC_LOCK.sha256")
    if not os.path.exists(lock_path):
        errors.append(f"Missing {lock_path}")
        return
    full_seen: Dict[str, str] = {}
    strip_seen: Dict[str, str] = {}
    with open(lock_path, "r", encoding="utf-8") as fh:
        for raw_ln in fh:
            ln = raw_ln.strip()
            if not ln:
                continue
            if ln.startswith("#"):
                body = ln[1:].strip()
                if body.endswith("(comment-stripped)") and "  " in body:
                    hpart, rest = body.split("  ", 1)
                    rel = rest[: -len("(comment-stripped)")].strip()
                    if len(hpart) == 64:
                        strip_seen[rel] = hpart
                continue
            parts = ln.split("  ", 1)
            if len(parts) != 2 or len(parts[0]) != 64:
                errors.append(f"Malformed SPEC_LOCK.sha256 line: {ln!r}")
                continue
            full_seen[parts[1]] = parts[0]

    for req in ("SubNLogN/Spec.lean", CHALLENGE_REL):
        if req not in full_seen:
            errors.append(f"SPEC_LOCK.sha256 missing full-file SHA-256 for {req}")
        else:
            actual_full = sha256_file(os.path.join(work_root, req))
            if actual_full != full_seen[req]:
                errors.append(f"SPEC_LOCK.sha256 full-file mismatch for {req}: {actual_full} != {full_seen[req]}")
        if req not in strip_seen:
            errors.append(f"SPEC_LOCK.sha256 missing comment-stripped SHA-256 for {req}")
        else:
            with open(os.path.join(work_root, req), "r", encoding="utf-8") as rfh:
                st = strip_comments(rfh.read(), filename=req, preserve_newlines=False)
            actual_strip = sha256_bytes(st.encode("utf-8"))
            if actual_strip != strip_seen[req]:
                errors.append(
                    f"SPEC_LOCK.sha256 comment-stripped mismatch for {req}: {actual_strip} != {strip_seen[req]}"
                )


def check_comparison(orig_root: str, work_root: str, write_manifest: str | None) -> int:
    errors: List[str] = []

    orig_files = iter_lean_files(orig_root)
    work_files = iter_lean_files(work_root)

    if orig_files != work_files:
        only_orig = sorted(set(orig_files) - set(work_files))
        only_work = sorted(set(work_files) - set(orig_files))
        errors.append(
            f"File list mismatch: orig={len(orig_files)}, work={len(work_files)}, "
            f"only_orig={only_orig[:5]}, only_work={only_work[:5]}"
        )
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    if len(work_files) != EXPECTED_LEAN_COUNT:
        errors.append(f"Expected {EXPECTED_LEAN_COUNT} library .lean files, found {len(work_files)}")

    # 1. Challenge.lean byte-identical check
    for label, root in (("orig", orig_root), ("work", work_root)):
        cpath = os.path.join(root, CHALLENGE_REL)
        chash = sha256_file(cpath)
        if chash != CHALLENGE_SHA256:
            errors.append(f"{label}/{CHALLENGE_REL} SHA-256 {chash} != {CHALLENGE_SHA256}")

    # 2. Frozen build/toolchain configs byte-identical check + SPEC_LOCK.sha256 check
    for cfg in FROZEN_CONFIGS:
        oh = sha256_file(os.path.join(orig_root, cfg))
        wh = sha256_file(os.path.join(work_root, cfg))
        if oh != wh:
            errors.append(f"Frozen config {cfg} changed: orig={oh} work={wh}")
    verify_spec_lock(work_root, errors)

    # 3. Per-file semantic freeze check
    manifest_lines: List[str] = []
    changed_comment_files = 0

    for rel in work_files:
        opath = os.path.join(orig_root, rel)
        wpath = os.path.join(work_root, rel)
        with open(opath, "rb") as fh:
            obytes = fh.read()
        with open(wpath, "rb") as fh:
            wbytes = fh.read()

        if obytes != wbytes:
            changed_comment_files += 1

        try:
            osrc = obytes.decode("utf-8")
            wsrc = wbytes.decode("utf-8")
        except UnicodeDecodeError as exc:
            errors.append(f"{rel}: UTF-8 decode error: {exc}")
            continue

        try:
            ospans = lex_lean(osrc, filename=f"orig/{rel}")
        except ValueError as exc:
            errors.append(str(exc))
            continue

        ostrip = strip_comments_from_spans(osrc, ospans, preserve_newlines=False)

        if obytes == wbytes:
            wstrip = ostrip
        else:
            try:
                wspans = lex_lean(wsrc, filename=f"work/{rel}")
            except ValueError as exc:
                errors.append(str(exc))
                continue

            # Check A: standard stripped source (`/- ... -/` -> `""`)
            wstrip = strip_comments_from_spans(wsrc, wspans, preserve_newlines=False)
            if ostrip != wstrip:
                errors.append(f"{rel}: comment-stripped source (`\"\"` mode) differs!")

            # Check B: line-preserving stripped source (`/- ... -/` -> `"\n"*k`)
            ostrip_nl = strip_comments_from_spans(osrc, ospans, preserve_newlines=True)
            wstrip_nl = strip_comments_from_spans(wsrc, wspans, preserve_newlines=True)
            if ostrip_nl != wstrip_nl:
                errors.append(
                    f"{rel}: line-preserving comment-stripped source differs (newline count changed)!"
                )

            # Check C: exact non-comment span sequence equality
            ocode_spans = [(k, osrc[a:b]) for k, a, b in ospans if k not in COMMENT_KINDS]
            wcode_spans = [(k, wsrc[a:b]) for k, a, b in wspans if k not in COMMENT_KINDS]
            if ocode_spans != wcode_spans:
                errors.append(f"{rel}: non-comment token/whitespace spans differ!")

            # Check D: exact comment/docstring kind sequence equality (no comment added/removed)
            ocomment_kinds = [k for k, _, _ in ospans if k in COMMENT_KINDS]
            wcomment_kinds = [k for k, _, _ in wspans if k in COMMENT_KINDS]
            if ocomment_kinds != wcomment_kinds:
                errors.append(
                    f"{rel}: comment/docstring block count or kinds changed "
                    f"(orig={len(ocomment_kinds)}, work={len(wcomment_kinds)})!"
                )

        digest = sha256_bytes(wstrip.encode("utf-8"))
        manifest_lines.append(f"{digest}  {rel}\n")

    manifest_text = "".join(manifest_lines)
    if write_manifest:
        with open(write_manifest, "w", encoding="utf-8") as fh:
            fh.write(manifest_text)
    else:
        mpath = os.path.join(work_root, "MANIFEST_stripped.sha256")
        if os.path.exists(mpath):
            with open(mpath, "r", encoding="utf-8") as fh:
                existing = fh.read()
            if existing != manifest_text:
                errors.append("MANIFEST_stripped.sha256 does not match computed stripped hashes!")

    if errors:
        for e in errors[:50]:
            print(f"FAIL: {e}", file=sys.stderr)
        if len(errors) > 50:
            print(f"... and {len(errors) - 50} more errors.", file=sys.stderr)
        return 1

    print(
        f"PASS: {len(work_files)} / {len(work_files)} library .lean files (replay/ excluded as non-library) "
        f"passed semantic freeze (comment-modified files: {changed_comment_files}; "
        f"{CHALLENGE_REL} SHA-256 verified: {CHALLENGE_SHA256[:16]}...)."
    )
    return 0


def check_standalone(work_root: str) -> int:
    errors: List[str] = []
    work_files = iter_lean_files(work_root)
    if len(work_files) != EXPECTED_LEAN_COUNT:
        errors.append(f"Expected {EXPECTED_LEAN_COUNT} library .lean files, found {len(work_files)}")

    cpath = os.path.join(work_root, CHALLENGE_REL)
    chash = sha256_file(cpath)
    if chash != CHALLENGE_SHA256:
        errors.append(f"{CHALLENGE_REL} SHA-256 {chash} != {CHALLENGE_SHA256}")
    verify_spec_lock(work_root, errors)

    mpath = os.path.join(work_root, "MANIFEST_stripped.sha256")
    if not os.path.exists(mpath):
        errors.append(f"Missing {mpath}")
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    expected_map: Dict[str, str] = {}
    with open(mpath, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts = line.split("  ", 1)
            if len(parts) != 2:
                errors.append(f"Malformed manifest line: {line!r}")
                continue
            expected_map[parts[1]] = parts[0]

    if sorted(expected_map.keys()) != work_files:
        errors.append("File list in MANIFEST_stripped.sha256 does not match repository library .lean files!")

    for rel in work_files:
        wpath = os.path.join(work_root, rel)
        with open(wpath, "r", encoding="utf-8") as fh:
            wsrc = fh.read()
        try:
            wstrip = strip_comments(wsrc, filename=rel, preserve_newlines=False)
        except ValueError as exc:
            errors.append(str(exc))
            continue
        digest = sha256_bytes(wstrip.encode("utf-8"))
        exp = expected_map.get(rel)
        if exp is not None and digest != exp:
            errors.append(f"{rel}: stripped SHA-256 {digest} != manifest {exp}")

    if errors:
        for e in errors[:50]:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print(
        f"PASS (standalone): {len(work_files)} / {len(work_files)} library .lean files "
        f"(replay/ excluded as non-library) match MANIFEST_stripped.sha256 "
        f"and {CHALLENGE_REL} matches {CHALLENGE_SHA256[:16]}...."
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify semantic freeze of Lean 4 sources.")
    ap.add_argument("--orig", help="Path to original frozen repository root.")
    ap.add_argument(
        "--work",
        default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        help="Path to repository root (defaults to parent of tools/).",
    )
    ap.add_argument("--write-manifest", help="Path to write MANIFEST_stripped.sha256.")
    args = ap.parse_args()

    if args.orig:
        return check_comparison(args.orig, args.work, args.write_manifest)
    return check_standalone(args.work)


if __name__ == "__main__":
    raise SystemExit(main())
