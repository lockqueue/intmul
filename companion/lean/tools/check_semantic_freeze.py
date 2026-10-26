#!/usr/bin/env python3
"""Semantic-freeze verifier for the `IntMul` Lean 4 formalization.

Modes:
1. Comparison mode (`--orig <ported_dir> --work <reconciled_dir>`):
   Verifies across all 27 `.lean` files (`IntMul.lean` and `IntMul/*.lean`) that:
   - The `.lean` file lists match (`27` files).
   - `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are byte-identical
     (when present, unless `--skip-configs` is passed).
   - Every `.lean` file has balanced `/- ... -/` comment delimiters and valid
     string, raw-string, character, and quoted-identifier literals.
   - Comment-stripped sources (`preserve_newlines=False`) are byte-identical.
   - Every non-comment token/whitespace span is byte-identical span-for-span.
   - Comment/docstring span kinds are aligned 1-to-1 (unless
     `--allow-comment-span-count-diff` is passed).
   - Writes (if `--write-manifest` is given) or checks `MANIFEST_stripped.sha256`.

2. Standalone archive mode (no `--orig`, run inside the archive root or `--work <dir>`):
   Verifies all 27 `.lean` files against `MANIFEST_stripped.sha256`, verifies
   `MANIFEST.sha256` against all shipped archive files, and verifies
   `SIGNATURES.txt` against `extract_signatures.py`.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from typing import Dict, List

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if THIS_DIR not in sys.path:
    sys.path.insert(0, THIS_DIR)

from extract_signatures import extract_repo_signatures, format_signatures_text  # noqa: E402
from strip_comments import (  # noqa: E402
    COMMENT_KINDS,
    iter_lean_files,
    lex_lean,
    strip_comments,
    strip_comments_from_spans,
)

EXPECTED_LEAN_COUNT = 27
FROZEN_CONFIGS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as fh:
        return sha256_bytes(fh.read())


def iter_shipped_files(repo_root: str) -> List[str]:
    """Return sorted relative paths of all archive files except `MANIFEST.sha256`, `.lake/`, and `__pycache__/`."""
    rel_paths: List[str] = []
    for dp, dn, fn in os.walk(repo_root):
        dn[:] = sorted(d for d in dn if not d.startswith(".") and d != "__pycache__")
        for f in sorted(fn):
            if f.startswith(".") or f.endswith(".pyc"):
                continue
            full = os.path.join(dp, f)
            rel = os.path.relpath(full, repo_root)
            if rel == "MANIFEST.sha256":
                continue
            rel_paths.append(rel)
    rel_paths.sort()
    return rel_paths


def check_comparison(
    orig_root: str,
    work_root: str,
    write_manifest: str | None,
    skip_configs: bool,
    allow_comment_span_count_diff: bool,
) -> int:
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
        errors.append(f"Expected {EXPECTED_LEAN_COUNT} .lean files, found {len(work_files)}")

    if not skip_configs:
        for cfg in FROZEN_CONFIGS:
            op = os.path.join(orig_root, cfg)
            wp = os.path.join(work_root, cfg)
            if os.path.exists(op) or os.path.exists(wp):
                if not (os.path.exists(op) and os.path.exists(wp)):
                    errors.append(f"Config {cfg} missing in one tree (orig={os.path.exists(op)}, work={os.path.exists(wp)})")
                else:
                    oh = sha256_file(op)
                    wh = sha256_file(wp)
                    if oh != wh:
                        errors.append(f"Frozen config {cfg} changed: orig={oh} work={wh}")

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

        try:
            wspans = lex_lean(wsrc, filename=f"work/{rel}")
        except ValueError as exc:
            errors.append(str(exc))
            continue

        ostrip = strip_comments_from_spans(osrc, ospans, preserve_newlines=False)
        wstrip = strip_comments_from_spans(wsrc, wspans, preserve_newlines=False)
        if ostrip != wstrip:
            errors.append(f"{rel}: comment-stripped source differs!")

        ocode_spans = [(k, osrc[a:b]) for k, a, b in ospans if k not in COMMENT_KINDS]
        wcode_spans = [(k, wsrc[a:b]) for k, a, b in wspans if k not in COMMENT_KINDS]
        if ocode_spans != wcode_spans:
            errors.append(f"{rel}: non-comment token/whitespace spans differ!")

        if not allow_comment_span_count_diff:
            ocomment_kinds = [k for k, _, _ in ospans if k in COMMENT_KINDS]
            wcomment_kinds = [k for k, _, _ in wspans if k in COMMENT_KINDS]
            if ocomment_kinds != wcomment_kinds:
                errors.append(
                    f"{rel}: comment/docstring span kinds changed "
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
        f"PASS: {len(work_files)} / {len(work_files)} .lean files passed semantic freeze "
        f"(comment-modified files: {changed_comment_files})."
    )
    return 0


def _parse_manifest_file(path: str, label: str, errors: List[str]) -> Dict[str, str]:
    mapping: Dict[str, str] = {}
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts = line.split("  ", 1)
            if len(parts) != 2 or len(parts[0]) != 64:
                errors.append(f"Malformed {label} line: {line!r}")
                continue
            mapping[parts[1]] = parts[0]
    return mapping


def check_standalone(work_root: str) -> int:
    errors: List[str] = []
    work_files = iter_lean_files(work_root)
    if len(work_files) != EXPECTED_LEAN_COUNT:
        errors.append(f"Expected {EXPECTED_LEAN_COUNT} .lean files, found {len(work_files)}")

    # 1. Verify MANIFEST_stripped.sha256
    mstrip_path = os.path.join(work_root, "MANIFEST_stripped.sha256")
    if not os.path.exists(mstrip_path):
        errors.append(f"Missing {mstrip_path}")
    else:
        expected_strip = _parse_manifest_file(mstrip_path, "MANIFEST_stripped.sha256", errors)
        if sorted(expected_strip.keys()) != work_files:
            errors.append("File list in MANIFEST_stripped.sha256 does not match .lean files!")
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
            exp = expected_strip.get(rel)
            if exp is not None and digest != exp:
                errors.append(f"{rel}: stripped SHA-256 {digest} != manifest {exp}")

    # 2. Verify MANIFEST.sha256
    mfull_path = os.path.join(work_root, "MANIFEST.sha256")
    if not os.path.exists(mfull_path):
        errors.append(f"Missing {mfull_path}")
    else:
        expected_full = _parse_manifest_file(mfull_path, "MANIFEST.sha256", errors)
        shipped_files = iter_shipped_files(work_root)
        if sorted(expected_full.keys()) != shipped_files:
            only_man = sorted(set(expected_full.keys()) - set(shipped_files))
            only_fs = sorted(set(shipped_files) - set(expected_full.keys()))
            errors.append(
                f"File list in MANIFEST.sha256 does not match archive files "
                f"(only_in_manifest={only_man[:5]}, only_on_disk={only_fs[:5]})!"
            )
        for rel, exp_hash in expected_full.items():
            fpath = os.path.join(work_root, rel)
            if os.path.exists(fpath):
                actual_hash = sha256_file(fpath)
                if actual_hash != exp_hash:
                    errors.append(f"{rel}: file SHA-256 {actual_hash} != MANIFEST.sha256 {exp_hash}")

    # 3. Verify SIGNATURES.txt
    sig_path = os.path.join(work_root, "SIGNATURES.txt")
    if not os.path.exists(sig_path):
        errors.append(f"Missing {sig_path}")
    else:
        with open(sig_path, "r", encoding="utf-8") as fh:
            expected_sigs = fh.read()
        actual_sigs = format_signatures_text(extract_repo_signatures(work_root))
        if actual_sigs != expected_sigs:
            errors.append("SIGNATURES.txt does not match extracted declaration signatures!")

    if errors:
        for e in errors[:50]:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print(
        f"PASS (standalone): {len(work_files)} / {len(work_files)} .lean files match "
        "MANIFEST_stripped.sha256, MANIFEST.sha256, and SIGNATURES.txt."
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify semantic freeze of Lean 4 sources.")
    ap.add_argument("positional", nargs="*", help="Optional [<orig_dir> <work_dir>] positional paths.")
    ap.add_argument("--orig", help="Path to ported reference repository root.")
    ap.add_argument(
        "--work",
        help="Path to working/reconciled repository root (defaults to parent of tools/).",
    )
    ap.add_argument("--write-manifest", help="Path to write MANIFEST_stripped.sha256.")
    ap.add_argument(
        "--skip-configs",
        action="store_true",
        help="Skip comparing lean-toolchain / lakefile.toml / lake-manifest.json.",
    )
    ap.add_argument(
        "--allow-comment-span-count-diff",
        action="store_true",
        help="Allow adding or removing standalone comment spans if stripped code is byte-identical.",
    )
    args = ap.parse_args()

    orig_dir = args.orig
    work_dir = args.work
    if len(args.positional) == 2 and not orig_dir and not work_dir:
        orig_dir, work_dir = args.positional
    elif len(args.positional) == 1 and not work_dir:
        work_dir = args.positional[0]
    elif len(args.positional) > 2:
        ap.error("At most two positional directory paths may be given.")

    if not work_dir:
        work_dir = os.path.dirname(THIS_DIR)

    if orig_dir:
        return check_comparison(
            orig_dir,
            work_dir,
            args.write_manifest,
            args.skip_configs,
            args.allow_comment_span_count_diff,
        )
    return check_standalone(work_dir)


if __name__ == "__main__":
    raise SystemExit(main())
