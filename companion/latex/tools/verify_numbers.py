#!/usr/bin/env python3
"""Deterministic verification of all schedule constants, inequalities, identities,
Lean declaration counts, and benchmark numbers in the manuscript sources.

Usage:
    python3 tools/verify_numbers.py [source_dir]
"""

from __future__ import annotations

import cmath
from decimal import Decimal, getcontext
import glob
import math
import os
import random
import re
import sys

getcontext().prec = 100


def compute_pi_dec() -> Decimal:
    def atan_inv(m: int) -> Decimal:
        m2 = Decimal(m * m)
        term = Decimal(1) / Decimal(m)
        total = term
        k = 1
        while True:
            term = -term / m2
            step = term / Decimal(2 * k + 1)
            if abs(step) < Decimal(10) ** (-95):
                break
            total += step
            k += 1
        return total

    return Decimal(4) * (Decimal(4) * atan_inv(5) - atan_inv(239))


PI = compute_pi_dec()
SQRT_PI = PI.sqrt()
LN2 = Decimal(2).ln()


def erf_dec(z: Decimal) -> Decimal:
    if z == 0:
        return Decimal(0)
    if z < 0:
        return -erf_dec(-z)
    if z > Decimal(18):
        return Decimal(1)
    z2 = z * z
    term = z
    total = z
    n = 1
    while True:
        term = term * (Decimal(2) * z2) / Decimal(2 * n + 1)
        total += term
        if abs(term) < Decimal(10) ** (-95):
            break
        n += 1
    return (Decimal(2) / SQRT_PI) * (-z2).exp() * total


def erfc_dec(z: Decimal) -> Decimal:
    return Decimal(1) - erf_dec(z)


def g_hat_dec(xi: Decimal, alpha: Decimal) -> Decimal:
    half = Decimal(1) / Decimal(2)
    return half * (
        erf_dec(SQRT_PI * alpha * (xi + half))
        - erf_dec(SQRT_PI * alpha * (xi - half))
    )


def strip_tex_comments(text: str) -> str:
    out: list[str] = []
    for raw in text.splitlines():
        if raw.lstrip().startswith("%"):
            continue
        m = re.search(r"(?<!\\)(?:\\\\)*%", raw)
        out.append(raw[: m.end() - 1] if m else raw)
    return "\n".join(out)


def check_mathematical_constants() -> None:
    print("[1/3] Verifying mathematical inequalities, schedule constants, and identities...")
    # Rounding and height bounds
    assert 1 / 8 == 0.125
    assert math.sqrt(2) / 8 < 0.177
    for K0 in range(10, 300):
        assert 2 * (K0 - 1).bit_length() + 1 <= K0

    # Elementary series constants
    assert math.exp(9) < 8104 < (1 << 13)
    assert (9 * math.e) / 66 < 0.371 < 2 ** (-1.43)
    assert 2.0 / math.sqrt(math.pi) < 1.13
    assert 1.13 * (2 ** (-24)) + (2 ** (-110)) + 0.5 * (2 ** (-34)) < 2 ** (-23)
    assert (20.0 / 131.0) * (5.0 ** (-131)) < 2.0 ** (-42 - 16)
    assert 4.0 / math.pi < 1.28
    assert (0.5 + 2 ** (-10)) * 0.25 < 0.25
    assert math.sqrt(2) * (0.5 + 2 ** (-10)) * 0.25 < math.sqrt(2) / 4 < 0.354

    # Explicit stack-machine constant C_tm_total (~5.03 * 10^92)
    c_nested_d1 = 1324224 * 277159328108409262726
    c_nested_base = 1119 * 32768 * c_nested_d1
    c_nested_total = 701974 + 336 * (118782569189317654368 * c_nested_base)
    c_tm_d1 = 15000000000000 * (1010141 * 2061)
    c_tm_d2 = 15000000000000 * c_tm_d1 * (2 * c_nested_total)
    c_tm_total = c_tm_d2 + 500
    assert 53 * (10 ** 55) < c_nested_total < 55 * (10 ** 55)
    assert 31 * (10 ** 21) < c_tm_d1 < 32 * (10 ** 21)
    assert 50 * (10 ** 91) < c_tm_total < 51 * (10 ** 91)
    assert len(str(c_tm_total)) == 93

    # Passband, stopband, conditioning, and Nyquist constants for p_work >= 8
    for p_work_int in [8, 12, 16, 24, 32, 64]:
        pw = Decimal(p_work_int)
        alpha = Decimal(2) * (pw * LN2 / PI).sqrt()
        g_half = Decimal(1) / Decimal(2) * erf_dec(SQRT_PI * alpha)
        assert Decimal(1) / Decimal(2) - Decimal("0.08") * (Decimal(2) ** (-4 * p_work_int)) <= g_half < Decimal(1)
        assert g_half > Decimal("0.499999999") > Decimal("0.49999999")
        psi_0 = (Decimal(1) / Decimal(2)) * erfc_dec((pw * LN2).sqrt()) + (
            Decimal(1) / Decimal(2)
        ) * erfc_dec(Decimal(3) * (pw * LN2).sqrt())
        if p_work_int == 8:
            assert Decimal("0.11105") < psi_0 * (Decimal(2) ** 8) < Decimal("0.11115")
        assert psi_0 < Decimal("0.120") * (Decimal(2) ** (-p_work_int))
        assert Decimal("0.120") < Decimal("0.15")
        wrap_ub = (-Decimal("0.99995") * alpha).exp()
        assert wrap_ub < Decimal("0.1400") < Decimal("0.15")
        gamma_min = g_half * (Decimal(1) - wrap_ub)
        assert gamma_min > Decimal("0.424")
        assert Decimal(1) / Decimal("0.424") < Decimal("2.36")
        assert Decimal(15) / (Decimal(2) * g_half) < Decimal("1.0000001") * Decimal(16)

    # Column solver constants
    for t1 in [2, 4, 8, 16, 64, 1024]:
        val_p = 1.0001 * (0.604 * t1 + 0.501 * t1 * (t1 - 1) / 2)
        assert val_p < 0.56 * t1 * t1
        val_z_last = 0.652 * t1 * t1 + 0.501 * t1 + 0.177
        assert val_z_last < 0.95 * t1 * t1
        val_z_all = 1.0001 * (val_z_last + (t1 - 1) * (0.604 + 0.590 * t1))
        assert val_z_all < 1.85 * t1 * t1 <= 80 * t1 * t1

    # Filter l1, spatial tail, and non-leaf r_ell >= 32
    assert (4.0 + 1.25 - 1.14472 + 0.42920) / math.pi < 1.444 < 1.62
    assert (2 / math.pi) * math.log(32) > 2.20 > 1.62  # ensures (2/pi)ln(alpha)+2.62 <= W_tilde+1 for r >= 32
    assert 1 / (6 * math.pi) + 1 / (20 * math.pi * math.log(2)) < 0.077 < 0.10

    # Forward error closure constants
    assert 2.36 * 0.15 < 0.5
    assert 3 * 9 + 80 * 2 == 187 <= 200
    assert 200 * (2 ** (-14)) == 25 / 2048 < 2 ** (-6)
    assert math.sqrt(2) / 8 + 2 ** (-7) + 25 / 2048 < 0.197 < 0.25
    assert 2.86 * 0.5 * (2 ** (-4)) + math.sqrt(2) / 8 < 0.267 < 1.0

    # Root recovery margin
    eps_max = 2.0 ** (-28)
    assert 2.0 + 2.0 * eps_max + math.sqrt(2) / 8 < 2.19
    assert 3.19 * (2.0 ** (-7)) == 3.19 / 128 < 0.5

    # Twisted polynomial-transform & Nyquist identity spot-check
    rng = random.Random(42)
    t1, r = 4, 8
    R = t1 * r
    x = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(R)]
    F_x = [
        sum(x[j] * cmath.exp(2j * math.pi * j * u / R) for j in range(R)) / R
        for u in range(R)
    ]
    lhs = sum(((-1) ** u1) * F_x[(r // 2) + r * u1] for u1 in range(t1))
    rhs = (1j / r) * sum(((-1) ** j2) * x[(t1 // 2) + t1 * j2] for j2 in range(r))
    assert abs(lhs - rhs) < 1e-14

    # Benchmark configuration arithmetic at 10^7, 10^8, 5*10^8, 10^9
    expected_cfgs = {
        10**7: (23, 20, 92, 144),
        10**8: (26, 23, 104, 162),
        5 * 10**8: (28, 26, 114, 178),
        10**9: (29, 27, 118, 184),
    }
    for n_val, (b_exp, K0_exp, p0_exp, p1_exp) in expected_cfgs.items():
        b_val = max(4, n_val.bit_length() - 1)
        N_val = (n_val + b_val - 1) // b_val
        K0_val = (2 * N_val - 1).bit_length()
        p0_val = 2 * b_val + 2 * K0_val + 6
        p1_val = p0_val + 2 * K0_val + 12
        assert (b_val, K0_val, p0_val, p1_val) == (b_exp, K0_exp, p0_exp, p1_exp)

    # Level-1 parameters at n = 10^9 under C leaf cutoff p_0^2 = 13,924
    assert 118 * 118 == 13924 < (1 << 14) == 16384 < 4 * 184 * 184 == 135424
    alpha_1_1e9 = 2.0 * math.sqrt((184 + 20) * math.log(2.0) / math.pi)
    m1_1_1e9 = math.ceil(alpha_1_1e9 * math.sqrt((184 + 28 + 12) * math.log(2.0) / math.pi))
    assert m1_1_1e9 == 95 and 2 * m1_1_1e9 + 1 == 191 > 128

    # Quoted single-thread and 64-thread ratios re-derived from quoted timings
    assert abs(9.92 / 0.0478 - 207.5) < 0.2
    assert round(92.51 / 0.6059) == 153
    assert round(805.37 / 3.4417) == 234
    assert round(2612.65 / 8.0969) == 323
    assert round(6.31 / 0.6056, 1) == 10.4
    assert round(18.52 / 9.92, 2) == 1.87
    assert round(163.46 / 92.51, 2) == 1.77
    assert round(2.0 / 0.56, 1) == 3.6
    assert round(10.4 / 4.4, 1) == 2.4
    print("  OK: All mathematical constants and ratios verified.")


def check_tex_constants_and_declarations(src_dir: str) -> list[str]:
    print("[2/3] Checking manuscript .tex files for required schedule, Lean, and benchmark tokens...")
    errors: list[str] = []
    tex_files = [os.path.join(src_dir, "main.tex")] + sorted(
        glob.glob(os.path.join(src_dir, "sections", "*.tex"))
    )
    existing = [p for p in tex_files if os.path.exists(p)]
    if not existing:
        return [f"No .tex files found in {src_dir}"]

    combined = "\n".join(
        strip_tex_comments(open(p, encoding="utf-8").read()) for p in existing
    )

    required_patterns = [
        (r"\+\s*6\b", "schedule constant +6"),
        (r"\+\s*12\b", "schedule constant +12"),
        (r"2\s*b\s*\+\s*2\s*K_0\s*\+\s*6", "root precision 2b + 2K_0 + 6"),
        (r"4\s*p(?:_\\ell|_0)?\^2", "leaf threshold 4p^2"),
        (r"0\.120\b", "stopband constant 0.120"),
        (r"0\.15\b", "stopband slack constant 0.15"),
        (r"2\.36\b", "conditioning constant 2.36"),
        (r"0\.424\b", "denominator lower bound 0.424"),
        (r"1\.0000001\b", "Nyquist norm constant 1.0000001"),
        (r"\b80\b", "solver error constant 80"),
        (r"\b200\b", "combined Step 3 constant 200"),
        (r"0\.197\b", "non-leaf inductive closure constant 0.197"),
        (r"3\.19\b", "root recovery constant 3.19"),
        (r"2\^\{-7\}|1/128", "root margin factor 2^{-7} / 1/128"),
        (r"tmIntMul_evalsToInTime_n_log_n", "Lean headline theorem tmIntMul_evalsToInTime_n_log_n"),
        (r"tmIntMul_elementary_stack_ops_n_log_n", "Lean elementary ops theorem tmIntMul_elementary_stack_ops_n_log_n"),
        (r"\b27\b", "Lean count: 27 files"),
        (r"82(?:,|\{,\})377\b", "Lean count: 82,377 lines"),
        (r"4\.27\.0", "Lean development toolchain 4.27.0"),
        (r"a3a10db0", "Mathlib revision a3a10db0"),
        (r"4\.33\.1", "Port target Lean 4.33.1"),
        (r"0df444a3", "Port target Mathlib 0df444a3"),
        (r"1041232178\b", "Lean numLabels: 1041232178"),
        (r"finTM2(?:\\allowbreak\s*)*MaxStmt(?:\\allowbreak\s*)*ElemOps(?:\\allowbreak\s*|\\\s+|\s+)+tmIntMul\s*=\s*16", "Lean finTM2MaxStmtElemOps = 16"),
        (r"\bf4ecb4f468c1\b", "Lean snapshot id f4ecb4f468c1"),
        (r"9\.92\b", "10^7-bit e2e time 9.92 s"),
        (r"92\.5(?:1)?\b", "10^8-bit e2e time 92.51 / 92.5 s"),
        (r"805\.(?:37|4)\b", "5*10^8-bit e2e time 805.37 / 805.4 s"),
        (r"2(?:,|\{,\})?612\.(?:65|7)\b", "10^9-bit e2e time 2612.65 / 2612.7 s"),
        (r"67\.3\b", "10^9-bit peak RSS 67.3 GiB"),
        (r"6\.31\b", "64-thread 10^8-bit e2e time 6.31 s"),
        (r"10\^\{92\}", "explicit stack-machine constant ~5*10^{92}"),
        (r"135(?:,|\{,\})424\b", "level-1 4p_1^2 = 135,424 at 10^9 bits"),
    ]

    for pat, desc in required_patterns:
        if not re.search(pat, combined):
            errors.append(f"Missing required constant/declaration ({desc}): regex `{pat}`")

    bib_path = os.path.join(src_dir, "refs.bib")
    if os.path.exists(bib_path):
        bib_clean = re.sub(r"\\allowbreak\s*", "", strip_tex_comments(open(bib_path, encoding="utf-8").read()))
        expected_cgmp_id = "e4852f57b537"
        found_ids = re.findall(r"content snapshot \\texttt\{([0-9a-f]{12})\}", bib_clean)
        if expected_cgmp_id not in found_ids:
            errors.append(f"Expected CGMP26 content snapshot id {expected_cgmp_id} in refs.bib, got {found_ids}")
        found_64hex = re.findall(r"\b[0-9a-f]{64}\b", bib_clean)
        if found_64hex:
            errors.append(f"Unexpected 64-hex archive hash in refs.bib (artifacts are cited by content snapshot ids): {found_64hex}")

    if not errors:
        print("  OK: All required schedule constants, Lean declarations, and measured numbers present.")
    return errors


def main() -> int:
    if len(sys.argv) > 1:
        src_dir = os.path.abspath(sys.argv[1])
    elif os.path.exists("main.tex"):
        src_dir = os.path.abspath(".")
    else:
        src_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    check_mathematical_constants()
    errors = check_tex_constants_and_declarations(src_dir)
    print("[3/3] Summary...")
    if errors:
        for e in errors:
            print(f"  FAIL: {e}")
        print("NUMBER VERIFICATION FAILED")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
