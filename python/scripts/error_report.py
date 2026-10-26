"""Measured error vs proved bound for the 2D FastDFT (M1) and the bridge (M2, M3, M6, M9); prints a Markdown
report (and writes it to a file with --out FILE).

Final error: ||out - F_R x||_inf vs the contract 2^-p max(1, ||x||) (MS eq. (inductive-bound))
and, for the bridge rows, vs BR2 Thm 2's total under the SPEC v1.2 refinement
p_fft = P + 2: total < (sqrt2/8 + 2^-12 + 2^-23) 2^-p X < 0.177021 2^-p X, X = max(1, ||x||_inf)
(SPEC §5.10; the paper's bridge precision contract).  Pre-rounding error (before the final quantization to
C~_{p+2}), measured with a high-precision oracle (Q = P + 2K + 64 bits), vs the certificates (MS
Lemma 6.5 + r2 §8 for M1; Lemma C + the middle's term for the bridge).  All bridge rows use the
precision schedule of the paper's bridge precision contract (profile "r2").  Values are printed
as log2(error / 2^-p).

Current code throughout: tape routing in the 2D FastDFT (schedule default), the closure gamma-hat by
br_r2 (4.21) powering, bridge overlap-add slots of 4P + 16 bits, bridge address movements by Lemma 12
(bridge_movement="lemma12", as in test_policy), and the Proposition 14 network engine for the M6
(Bluestein) and M9 (Walsh) rows (prop14_layer="network", as in test_policy).  M3 keeps the direct
layers (prop14_layer="base", SPEC §5.11); every M6 output is asserted bit-identical to the M3 output
for the same shape and input.
Usage: .venv/bin/python scripts/error_report.py [--quick] [--out FILE]
"""

from __future__ import annotations

import random
import sys
import time
from fractions import Fraction

sys.path.insert(0, ".")
sys.path.insert(0, "tests")

from oracle import OracleDFT, log2_frac, sqrt_upper  # noqa: E402
from subnlogn.context import Ctx  # noqa: E402
from subnlogn.fastdft2d import certificate_2d, fast_dft  # noqa: E402
from subnlogn.fixedpoint import FxVec  # noqa: E402
from subnlogn.schedule import faithful_schedule, test_schedule  # noqa: E402


def rnd_input(R, p, rng, unit=False):
    """Random complex input: ||x|| close to 2^p (default) or ||x|| <= 1 (unit=True)."""
    q = p + 2
    big = (1 << q) * 7 // 10 if unit else (1 << (q + p)) * 7 // 10
    return [rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)]


def m1_rows(cases, tables):
    rows = []
    for name, sched, R, p, unit in cases:
        rng = random.Random(R * 31 + p)
        re, im = rnd_input(R, p, rng, unit)
        ctx = Ctx(schedule=sched, tables=tables, capture={})
        t0 = time.time()
        z = fast_dft(ctx, FxVec(re, im, p + 2), R, p)
        dt = time.time() - t0
        lv = sched.level(R, p)
        A = max(Fraction(1), sqrt_upper(FxVec(re, im, p + 2).sup_norm_sq()))
        cert = certificate_2d(lv, A)
        orc = OracleDFT(re, im, p + 2, p)
        fin = sqrt_upper(orc.error_sq_vs(z.re, z.im, z.q))
        if lv.leaf:
            pre_m, pre_b = "leaf", log2_frac(cert.pre_rounding) + p
        else:
            orc2 = OracleDFT(re, im, p + 2, lv.p_child)
            zc = ctx.capture["Zcomp"]
            pre_m = log2_frac(sqrt_upper(orc2.error_sq_vs(zc.re, zc.im, zc.q))) + p
            pre_b = log2_frac(cert.pre_rounding) + p
        depth = len(sched.chain(R, p)) - 1
        rows.append((name + (" (unit x)" if unit else ""), R, p, depth, log2_frac(fin) + p,
                     log2_frac(cert.contract) + p, pre_m, pre_b, dt))
    return rows


#: BR2 Thm 2 (the paper's bridge precision contract): total < (sqrt2/8 + 2^-12 + 2^-23) 2^-p X < 0.177021 2^-p X.
THM2_TOTAL = Fraction(177021, 1000000)


def m2_rows(cases, tables, outputs=None):
    """Bridge rows; case = (d, K, p, unit, profile[, middle[, prop14_layer]]).  With ``outputs`` a dict,
    the computed output of each case is stored under ((d, K, p, unit, profile), (middle, layer))."""
    from subnlogn.bridge.bridge_dft import bridge_certificate, bridge_dft
    rows = []
    for case in cases:
        d, K, p, unit, profile = case[:5]
        middle = case[5] if len(case) > 5 else "direct"
        layer = case[6] if len(case) > 6 else "base"
        R = 1 << K
        rng = random.Random(1000 * d + K)
        re, im = rnd_input(R, p, rng, unit)
        sched = test_schedule(bridge_d=d).with_(bridge_constants=profile, bridge_middle=middle,
                                                bridge_movement="lemma12", prop14_layer=layer)
        ctx = Ctx(schedule=sched, tables=tables, capture={})
        t0 = time.time()
        z = bridge_dft(ctx, FxVec(re, im, p + 2), R, p, d)
        dt = time.time() - t0
        P, w, m, geom = ctx.capture["bridge_params"]
        e = ctx.capture["bridge_e"]
        A = max(Fraction(1), sqrt_upper(FxVec(re, im, p + 2).sup_norm_sq()))
        cert = bridge_certificate(geom, p, P, w, 1 << e, A, middle_backend=middle)
        orc = OracleDFT(re, im, p + 2, p)
        fin = sqrt_upper(orc.error_sq_vs(z.re, z.im, z.q))
        orc2 = OracleDFT(re, im, p + 2, P)
        Zn = ctx.capture["bridge_Znorm"]
        pre = sqrt_upper(orc2.error_sq_vs(Zn.re, Zn.im, Zn.q - e))
        thm2 = log2_frac(THM2_TOTAL * A) if profile == "r2" else None      # units of 2^-p
        if fin > THM2_TOTAL * A / (1 << p) and profile == "r2":
            raise AssertionError(f"final error above the bridge precision contract (BR2 Thm 2) for {case}")
        if outputs is not None:
            outputs[((d, K, p, unit, profile), (middle, layer))] = (z.re, z.im)
        c = ctx.inst.counts
        net = (c.get("m6.layer.network", 0), c.get("m6.gate", 0))
        rows.append((f"{d} {profile}{' ' + middle if middle != 'direct' else ''}{' (unit x)' if unit else ''}",
                     geom.t, R, p, (P, w), log2_frac(fin) + p,
                     log2_frac(cert.contract) + p, thm2, log2_frac(pre) + p,
                     log2_frac(cert.pre_rounding) + p, dt, net))
    return rows


def _bridge_table(rows, first: str, net: bool = False) -> list[str]:
    head = (f"| {first} | t | R | p | (P, w) | final err | contract | Thm 2 total | pre-rounding err | "
            f"certificate (pre) |" + (" Prop 14 network layers (gates) |" if net else "") + " time s |")
    out = [head, "|" + "---|" * (head.count("|") - 1)]
    for d, t, R, p, P, fin, con, thm2, pm, pb, dt, nl in rows:
        th = f"{thm2:.2f}" if thm2 is not None else "— (r3)"
        nc = f" {nl[0]} ({nl[1]}) |" if net else ""
        out.append(f"| {d} | {t} | {R} | {p} | {P} | {fin:.2f} | {con:.2f} | {th} | {pm:.2f} | {pb:.2f} |{nc} {dt:.2f} |")
    return out


def main():
    quick = "--quick" in sys.argv
    out_path = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    tables: dict = {}
    m1 = [("test bt=2", test_schedule(base_threshold=2), R, p, u)
          for R, p in [(4, 10), (16, 12), (32, 14), (64, 16), (256, 20)] + ([] if quick else [(512, 20)])
          for u in (False, True)]
    m1 += [("test bt=16", test_schedule(base_threshold=16), 256, 16, False),
           ("faithful", faithful_schedule(), 256, 10, False),
           ("faithful", faithful_schedule(), 512, 9, False),
           ("faithful", faithful_schedule(), 1024, 10, True),
           ("faithful", faithful_schedule(), 1024, 16, False)]
    m2 = [(d, K, max(8, K) + 4, u, "r2") for d in (2, 3, 4, 5) for K in (d, 6, 8) if K >= d
          for u in (False, True)]
    m3_shapes = ((2, 4), (2, 6), (3, 6), (4, 5), (4, 6), (4, 8))
    m6_shapes = ((4, 5), (4, 6), (4, 8)) + (() if quick else ((5, 10),))
    m3 = [(d, K, max(8, K) + 2, u, "r2", "bluestein") for d, K in m3_shapes + m6_shapes[3:]
          for u in (False, True)]
    m6 = [(d, K, max(8, K) + 2, u, "r2", "bluestein", "network") for d, K in m6_shapes
          for u in (False, True)]
    m9 = [(d, K, max(8, K) + 2, u, "r2", "walsh", "network") for d, K in ((2, 4), (2, 6), (3, 6), (4, 8))
          for u in (False, True)]
    if quick:
        m2 = m2[::3]
    outputs: dict = {}
    r1 = m1_rows(m1, tables)
    r2 = m2_rows(m2, tables)
    r3 = m2_rows(m3, tables, outputs)
    r6 = m2_rows(m6, tables, outputs)
    r9 = m2_rows(m9, tables)
    for case in m6:                     # M6 network engine == M3 direct layers, bit for bit (SPEC §4.7)
        key = tuple(case[:5])
        if outputs[(key, ("bluestein", "network"))] != outputs[(key, ("bluestein", "base"))]:
            raise AssertionError(f"M6 output differs from M3 for {case}")
    out = ["# Error report: measured vs proved bounds", "",
           "Generated by `scripts/error_report.py`. All numbers are log2(error / 2^-p), so the "
           "contract 2^-p max(1,||x||) shows as log2 max(1,||x||): about p for inputs with "
           "||x|| close to 2^p, and 0 for the '(unit x)' rows (||x|| <= 1). The final error is "
           "dominated by the last rounding to C~_{p+2} (sqrt(2)/8 2^-p = 2^-2.5 2^-p). "
           "Pre-rounding errors (before that last rounding) are measured with an exact oracle "
           "at P + 2K + 64 bits and compared with the analytic certificates of the error analysis. "
           "For the bridge rows, 'Thm 2 total' is log2(0.177021·X) with X = max(1, ||x||∞): "
           "BR2 Thm 2's total bound under the SPEC v1.2 refinement p_fft = P + 2, "
           "(√2/8 + 2^-12 + 2^-23)·2^-p·X < 0.177021·2^-p·X (asserted for every row).", "",
           "Current code throughout: tape routing in the 2D FastDFT (MS Lemma 2.4/2.5 passes; schedule "
           "default), the closure γ̂ by br_r2 (4.21) powering, bridge overlap-add slots of 4P + 16 bits, "
           "bridge address movements by Lemma 12 (`bridge_movement=\"lemma12\"`), and the Proposition 14 "
           "network engine (`prop14_layer=\"network\"`) in the M6 and M9 rows, as in `test_policy`. "
           "Bridge rows time one `bridge_dft` call (tables shared across rows).", "",
           "## M1: 2D FastDFT with the negative half-bin carrier drop-in", "",
           "| schedule | R | p | depth | final err | contract | pre-rounding err | certificate (pre) | time s |",
           "|---|---|---|---|---|---|---|---|---|"]
    for name, R, p, depth, fin, con, pm, pb, dt in r1:
        pm_s = pm if isinstance(pm, str) else f"{pm:.2f}"
        out.append(f"| {name} | {R} | {p} | {depth} | {fin:.2f} | {con:.2f} | {pm_s} | {pb:.2f} | {dt:.2f} |")
    out += ["", "## M2: d-dimensional bridge, direct middle DFT", "",
            "Precision schedule: w = p+K+⌈lg d⌉+20, P = 2p+12K+32⌈lg(p+K+2)⌉+256, m = P (the paper's bridge "
            "precision contract; profile `r2`). The certificate is dominated by the worst-case alias "
            "term Q·0.120(d−1)·2^-w·X (Ψ(0) is never sampled with the negative carrier), so the "
            "measured error sits well below it.", ""]
    out += _bridge_table(r2, "d, profile")
    out += ["", "## M3: bridge with the Bluestein middle (direct layers; SPEC §5.7-5.11)", "",
            "Middle term of the certificate: (E_ring + 22)·2^-p_fft, E_ring = √2·M(3ℓ+1), p_fft = P + 2. "
            "Chunk rounds by the Proposition 14 base case (`prop14_layer=\"base\"`).", ""]
    out += _bridge_table(r3, "d, profile, middle")
    out += ["", "## M6: bridge with the Bluestein middle and the Proposition 14 network engine (SPEC §4.5-4.8)", "",
            "`prop14_layer=\"network\"`: chunk rounds through the complex test network C1 with Lemma 13 basis "
            "changes and Lemma 12 swaps on B1 (SPEC §4.3), engine policy LAYER_TEST (compiled guard, forced "
            "batching). Every output is asserted bit-identical to the M3 row with the same shape and input, so "
            "the error columns equal M3's. The network column counts the Prop 14 layers that ran through the "
            "network engine (`m6.layer.network`) and, in parentheses, the network gates applied (`m6.gate`).", ""]
    out += _bridge_table(r6, "d, profile, middle", net=True)
    out += ["", "## M9: bridge with the Walsh middle (direct complex tensor FFT; SPEC_WALSH §5-6)", "",
            "Middle term of the certificate: 12ℓ·2^-p_fft, p_fft = P + 2 (no M factor; SPEC_WALSH §6.2). "
            "Chunk rounds and CNOT batches through the network engine (`prop14_layer=\"network\"`). "
            "The bridge-level error is dominated by the alias term (w << P), so these rows coincide with "
            "M3's; the middle's own error against 12ℓ·2^-p_fft is measured in tests/test_walsh_fft.py (W-T10).", ""]
    out += _bridge_table(r9, "d, profile, middle", net=True)
    out.append("")
    text = "\n".join(out)
    if out_path:
        with open(out_path, "w", encoding="utf-8") as fh:
            fh.write(text)
    print(text)


if __name__ == "__main__":
    main()
