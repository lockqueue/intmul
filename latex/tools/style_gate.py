#!/usr/bin/env python3
"""Check LaTeX sources against dash and sentence-readability thresholds.

Usage:
    python3 tools/style_gate.py [source_dir] [--verbose]
"""

from __future__ import annotations

import glob
import os
import re
import sys

SINC_ENDASH_PAT = re.compile(r"sinc" + "--" + r"gaussian", re.IGNORECASE)
INLINE_MATH_RE = re.compile(r"(?<!\\)((?:\\\\)*)\$([^$]+?(?<!\\)(?:\\\\)*)\$")
THEOREM_LIKE_ENVS = (
    "theorem",
    "maintheorem",
    "lemma",
    "proposition",
    "corollary",
    "definition",
    "fact",
    "remark",
)
DISPLAY_MATH_ENVS = (
    "equation",
    "equation\\*",
    "align",
    "align\\*",
    "gather",
    "gather\\*",
    "multline",
    "multline\\*",
    "flalign",
    "flalign\\*",
)
ABBREV_RE = re.compile(
    r"\b(e\.g|i\.e|cf|vs|resp|Thm|Thms|Prop|Props|Lem|Lems|Cor|Def|Rem|Sec|Secs|App|Eq|Eqs|Fig|Figs|Tab|No|St|Dr|Prof|al)\.\s*"
)


def strip_tex_comments(text: str) -> str:
    """Strip TeX % comments without introducing artificial blank lines."""
    out_lines: list[str] = []
    for raw in text.splitlines():
        if raw.strip() == "":
            out_lines.append("")
            continue
        if raw.lstrip().startswith("%"):
            continue
        m = re.search(r"(?<!\\)(?:\\\\)*%", raw)
        if m:
            out_lines.append(raw[: m.end() - 1])
        else:
            out_lines.append(raw)
    return "\n".join(out_lines)


def strip_verbatim_envs(text: str) -> str:
    text = re.sub(r"\\begin\{Verbatim\}[\s\S]*?\\end\{Verbatim\}", "", text)
    text = re.sub(r"\\begin\{verbatim\}[\s\S]*?\\end\{verbatim\}", "", text)
    return text


def extract_balanced_command_args(text: str, cmd: str) -> list[str]:
    """Extract balanced {...} arguments of \\cmd{...} or \\cmd[...]{...}."""
    results: list[str] = []
    pat = re.compile(rf"\\{cmd}\*?(?:\[[^\]]*\])?\s*\{{")
    pos = 0
    while True:
        m = pat.search(text, pos)
        if not m:
            break
        start = m.end()
        depth = 1
        i = start
        while i < len(text) and depth > 0:
            ch = text[i]
            if ch == "\\" and i + 1 < len(text):
                i += 2
                continue
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            i += 1
        if depth == 0:
            results.append(text[start : i - 1])
            pos = i
        else:
            pos = start
    return results


def strip_algorithm_fboxes(text: str) -> str:
    """Remove \\fbox{...Algorithm~1...} display boxes from prose checks."""
    out: list[str] = []
    pat = re.compile(r"\\fbox\s*\{")
    pos = 0
    while True:
        m = pat.search(text, pos)
        if not m:
            out.append(text[pos:])
            break
        start = m.end()
        depth = 1
        i = start
        while i < len(text) and depth > 0:
            ch = text[i]
            if ch == "\\" and i + 1 < len(text):
                i += 2
                continue
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            i += 1
        body = text[start : i - 1] if depth == 0 else ""
        if "Algorithm~1" in body or "Algorithm 1" in body:
            out.append(text[pos : m.start()])
            out.append("\n\n")
        else:
            out.append(text[pos:i])
        pos = i
    return "".join(out)


def check_forbidden_em_dashes(rel: str, clean_tex: str) -> list[str]:
    """Return descriptions of any forbidden em-dash occurrences in clean_tex."""
    issues: list[str] = []

    # 1. Theorem-like environments and remarks
    for env in THEOREM_LIKE_ENVS:
        for m in re.finditer(rf"\\begin\{{{env}\*?\}}([\s\S]*?)\\end\{{{env}\*?\}}", clean_tex):
            cnt = m.group(1).count("---")
            for _ in range(cnt):
                issues.append(f"{rel}: em dash inside \\begin{{{env}}}")

    # 2. Tabular environments
    for m in re.finditer(r"\\begin\{tabular\*?\}([\s\S]*?)\\end\{tabular\*?\}", clean_tex):
        cnt = m.group(1).count("---")
        for _ in range(cnt):
            issues.append(f"{rel}: em dash inside tabular")

    # 3. Captions
    for cap in extract_balanced_command_args(clean_tex, "caption"):
        cnt = cap.count("---")
        for _ in range(cnt):
            issues.append(f"{rel}: em dash inside \\caption")

    # 4. Math (display and inline)
    math_spans: list[str] = []
    math_spans.extend(m.group(1) for m in re.finditer(r"\\\[([\s\S]*?)\\\]", clean_tex))
    math_spans.extend(m.group(1) for m in re.finditer(r"\$\$([\s\S]*?)\$\$", clean_tex))
    for menv in DISPLAY_MATH_ENVS:
        math_spans.extend(
            m.group(1) for m in re.finditer(rf"\\begin\{{{menv}\}}([\s\S]*?)\\end\{{{menv}\}}", clean_tex)
        )
    no_disp = re.sub(r"\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$", " ", clean_tex)
    for menv in DISPLAY_MATH_ENVS:
        no_disp = re.sub(rf"\\begin\{{{menv}\}}[\s\S]*?\\end\{{{menv}\}}", " ", no_disp)
    math_spans.extend(m.group(2) for m in INLINE_MATH_RE.finditer(no_disp))
    math_spans.extend(m.group(1) for m in re.finditer(r"\\\(([\s\S]*?)\\\)", no_disp))
    for sp in math_spans:
        for _ in range(sp.count("---")):
            issues.append(f"{rel}: em dash inside math")

    # 5. Directly adjacent to \cite
    for _ in re.finditer(r"---\s*~?\s*\\cite\b|\\cite(?:\[[^\]]*\])?\{[^}]*\}\s*~?\s*---", clean_tex):
        issues.append(f"{rel}: em dash directly adjacent to \\cite")

    # 6. Spaces around --- or spaced en-dash used as em-dash in prose
    for _ in re.finditer(r"[ \t]---|---[ \t]", no_disp):
        issues.append(f"{rel}: whitespace adjacent to ---")
    no_tab_no_math = re.sub(
        r"\\begin\{(?:tabular\*?|tikzpicture)\}[\s\S]*?\\end\{(?:tabular\*?|tikzpicture)\}",
        " ",
        no_disp,
    )
    no_tab_no_math = INLINE_MATH_RE.sub(r"\1MATH", no_tab_no_math)
    for _ in re.finditer(r"[ \t]--[ \t]", no_tab_no_math):
        issues.append(f"{rel}: spaced en dash ' -- ' in prose")

    return issues


def extract_prose_sentences(clean_tex: str) -> list[str]:
    """Extract prose sentences with inline and display math each counted as 1 token."""
    t = clean_tex
    if "\\begin{document}" in t:
        t = t.split("\\begin{document}", 1)[1]
    if "\\end{document}" in t:
        t = t.split("\\end{document}", 1)[0]

    # Remove non-prose environments (tables, TikZ figures, algorithm display box)
    for env in ("tikzpicture", "tabular", "tabular\\*"):
        t = re.sub(rf"\\begin\{{{env}\}}[\s\S]*?\\end\{{{env}\}}", "\n\n", t)
    t = strip_algorithm_fboxes(t)

    # Replace display math with MATHTOKEN (preserving terminal . or ; inside display math)
    def repl_disp(m: re.Match[str]) -> str:
        body = m.group(1)
        body_clean = re.sub(r"\\(?:label|tag)\{[^}]*\}|\\(?:nonumber|qedhere|qed)\b", "", body).strip()
        if body_clean.endswith(".") and not body_clean.endswith("..."):
            return " MATHTOKEN. "
        if body_clean.endswith(";"):
            return " MATHTOKEN; "
        return " MATHTOKEN "

    t = re.sub(r"\\\[([\s\S]*?)\\\]", repl_disp, t)
    t = re.sub(r"\$\$([\s\S]*?)\$\$", repl_disp, t)
    for menv in DISPLAY_MATH_ENVS:
        t = re.sub(rf"\\begin\{{{menv}\}}([\s\S]*?)\\end\{{{menv}\}}", repl_disp, t)

    # Replace inline math with 1 token
    t = INLINE_MATH_RE.sub(r"\1 MATHTOKEN ", t)
    t = re.sub(r"\\\([\s\S]*?\\\)", " MATHTOKEN ", t)

    # Remove section/paragraph headings and structural declarations
    t = re.sub(
        r"\\(?:section|subsection|subsubsection)\*?(?:\[[^\]]*\])?\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}",
        "\n\n",
        t,
    )
    t = re.sub(r"\\paragraph\*?\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}", "\n\n", t)
    t = re.sub(r"\\(?:label|bibliographystyle|bibliography|input|pagestyle|thispagestyle)\{[^}]*\}", " ", t)
    t = re.sub(
        r"\\(?:maketitle|newpage|clearpage|appendix|centering|footnotesize|scriptsize|small|normalsize|medskip|bigskip|smallskip|noindent|qed)\b",
        " ",
        t,
    )

    # Collapse \cite / \ref / \eqref to single tokens so internal punctuation does not split
    t = re.sub(r"\\cite(?:\[[^\]]*\])?\{[^}]*\}", " CITETOKEN ", t)
    t = re.sub(r"\\(?:ref|eqref|autoref|Cref|cref)\{[^}]*\}", " REFTOKEN ", t)

    # Environment boundaries and list items
    t = re.sub(
        r"\\begin\{(?:enumerate|itemize|theorem|maintheorem|lemma|proposition|corollary|definition|fact|remark|proof|table|figure)\*?\}(?:\[[^\]]*\])?",
        "\n\n",
        t,
    )
    t = re.sub(
        r"\\end\{(?:enumerate|itemize|theorem|maintheorem|lemma|proposition|corollary|definition|fact|remark|proof|table|figure)\*?\}",
        "\n\n",
        t,
    )
    t = re.sub(r"\\item(?:\[[^\]]*\])?", "\n\n", t)

    # Extract caption prose into separate blocks
    t = re.sub(
        r"\\caption(?:\[[^\]]*\])?\{([^{}]*(?:\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}[^{}]*)*)\}",
        r"\n\n\1\n\n",
        t,
    )

    t = re.sub(r"(\d)\{,\}(\d)", r"\1,\2", t)
    for _ in range(3):
        t = re.sub(r"\\(?:emph|textbf|textit|texttt|textrm|textup)\{([^{}]*)\}", r" \1 ", t)

    t = re.sub(r"\\\s", " ", t)
    t = ABBREV_RE.sub(r"\1_DOT_ ", t)
    t = t.replace("~", " ")
    t = re.sub(r"\\[a-zA-Z]+\*?", " ", t)
    t = t.replace("{", " ").replace("}", " ")

    sentences: list[str] = []
    for block in re.split(r"\n\s*\n", t):
        block = " ".join(block.split())
        if not block:
            continue
        parts = re.split(r"(?<=[.?!])\s+(?=[A-Z0-9(\"'`]|MATHTOKEN|CITETOKEN|REFTOKEN)", block)
        for part in parts:
            part = part.strip()
            if part and count_words(part) >= 2:
                sentences.append(part)
    return sentences


def count_words(sentence: str) -> int:
    s = sentence.replace("---", " ").replace("--", " ")
    return len(re.findall(r"[A-Za-z0-9_]+(?:['-][A-Za-z0-9_]+)*", s))


def check_readme_prose(readme_text: str) -> tuple[int, int]:
    """Return (paren_em_pairs, sinc_endash_hits) in README.md."""
    sinc_hits = len(SINC_ENDASH_PAT.findall(readme_text))
    # Strip fenced code blocks and markdown table separator lines before checking ---
    no_code = re.sub(r"```[\s\S]*?```", "\n\n", readme_text)
    prose_lines = []
    for line in no_code.splitlines():
        if re.match(r"^\s*\|[\s|:-]+\|\s*$", line) or re.match(r"^\s*---+\s*$", line):
            prose_lines.append("")
        elif line.startswith("    "):
            prose_lines.append("")
        else:
            prose_lines.append(line)
    paras = re.split(r"\n\s*\n", "\n".join(prose_lines))
    paren_pairs = sum(p.count("---") // 2 for p in paras if p.count("---") >= 2)
    return paren_pairs, sinc_hits


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--verbose"]
    verbose = "--verbose" in sys.argv[1:]
    if args:
        src_dir = os.path.abspath(args[0])
    elif os.path.exists("main.tex"):
        src_dir = os.path.abspath(".")
    else:
        src_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    tex_paths = []
    main_tex = os.path.join(src_dir, "main.tex")
    if os.path.exists(main_tex):
        tex_paths.append(main_tex)
    tex_paths.extend(sorted(glob.glob(os.path.join(src_dir, "sections", "*.tex"))))
    if not tex_paths:
        print(f"ERROR: No .tex files found under {src_dir}")
        return 1

    em_total = 0
    em_abstract = 0
    em_front = 0
    paren_pairs = 0
    forbidden_issues: list[str] = []
    sinc_hits = 0

    front_sentences: list[tuple[str, str]] = []
    all_sentences: list[tuple[str, str]] = []
    per_file_em: list[tuple[str, int]] = []

    for fp in tex_paths:
        rel = os.path.relpath(fp, src_dir)
        base = os.path.basename(fp)
        raw = open(fp, encoding="utf-8").read()
        clean = strip_verbatim_envs(strip_tex_comments(raw))

        em = clean.count("---")
        em_total += em
        if em:
            per_file_em.append((rel, em))
        if base == "abstract.tex":
            em_abstract += em
        if base in ("abstract.tex", "intro.tex", "overview.tex"):
            em_front += em

        for para in re.split(r"\n\s*\n", clean):
            if para.count("---") >= 2:
                paren_pairs += para.count("---") // 2

        forbidden_issues.extend(check_forbidden_em_dashes(rel, clean))
        sinc_hits += len(SINC_ENDASH_PAT.findall(clean))

        if base != "main.tex":
            sents = extract_prose_sentences(clean)
            all_sentences.extend((rel, s) for s in sents)
            if base in ("intro.tex", "overview.tex"):
                front_sentences.extend((rel, s) for s in sents)

    bib_path = os.path.join(src_dir, "refs.bib")
    if os.path.exists(bib_path):
        sinc_hits += len(SINC_ENDASH_PAT.findall(open(bib_path, encoding="utf-8").read()))

    readme_path = os.path.join(src_dir, "README.md")
    if os.path.exists(readme_path):
        rd_pairs, rd_sinc = check_readme_prose(open(readme_path, encoding="utf-8").read())
        paren_pairs += rd_pairs
        sinc_hits += rd_sinc

    front_wc = [count_words(s) for _, s in front_sentences]
    front_gt60 = [(rel, s, count_words(s)) for rel, s in front_sentences if count_words(s) > 60]
    front_avg = (sum(front_wc) / len(front_wc)) if front_wc else 0.0
    front_max = max(front_wc) if front_wc else 0

    multi_semi = [(rel, s, s.count(";")) for rel, s in all_sentences if s.count(";") >= 2]

    checks = [
        ("em_dash_total (--- across .tex)", em_total, "<= 8", em_total <= 8),
        ("em_dash_front (abstract+intro+overview)", em_front, "<= 2", em_front <= 2),
        ("em_dash_abstract (abstract.tex)", em_abstract, "== 0", em_abstract == 0),
        ("parenthetical_em_pairs (---...---)", paren_pairs, "== 0", paren_pairs == 0),
        ("forbidden_em_dash_contexts", len(forbidden_issues), "== 0", len(forbidden_issues) == 0),
        ("sinc_endash_gaussian (.tex+bib+README)", sinc_hits, "== 0", sinc_hits == 0),
        ("front_sentences_gt_60_words (intro+overview)", len(front_gt60), "== 0", len(front_gt60) == 0),
        ("front_avg_sentence_words (intro+overview)", f"{front_avg:.2f}", "<= 30.0", front_avg <= 30.0),
        ("sentences_with_>=2_semicolons (all .tex)", len(multi_semi), "<= 5", len(multi_semi) <= 5),
    ]

    print(f"Style gate report for: {src_dir}")
    print(f"{'Metric':46s} | {'Value':>8s} | {'Limit':>8s} | Status")
    print("-" * 75)
    failed = False
    for name, val, lim, ok in checks:
        status = "OK" if ok else "FAIL"
        if not ok:
            failed = True
        print(f"{name:46s} | {str(val):>8s} | {lim:>8s} | {status}")
    print("-" * 75)
    print(f"Info: front_sentences={len(front_wc)}, front_max_words={front_max}, total_sentences={len(all_sentences)}")
    if per_file_em:
        print("Em dashes by file: " + ", ".join(f"{r}={c}" for r, c in per_file_em))

    if verbose or failed:
        if forbidden_issues:
            print("\nForbidden em-dash details:")
            for item in forbidden_issues[:25]:
                print(f"  - {item}")
        if front_gt60:
            print("\nFront-matter sentences > 60 words:")
            for rel, s, w in front_gt60:
                print(f"  - [{rel} | {w} words] {s[:140]}...")
        if len(multi_semi) > 5 or verbose:
            print(f"\nSentences with >= 2 semicolons ({len(multi_semi)}):")
            for rel, s, sc in multi_semi[:25]:
                print(f"  - [{rel} | {sc} semicolons] {s[:140]}...")

    if failed:
        print("STYLE GATE FAILED")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
