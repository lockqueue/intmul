"""Print the exact triple-network certificates (SPEC §2.7) as markdown tables.

Usage: .venv/bin/python scripts/certify_report.py [h ...]   (default: 21 22 27 39 40 100)

Table 1: the certificate with the preprint's crude log bound L = max(20, bitlen m) [Pr L1340-1341].
Table 2: the tau test with the certified sharp bound ln m <= L (net.certify.ln_enclosure), at tau = 1 - 2^-40 and
1 - 2^-42 (SPEC_WALSH §1.3 rows).
"""

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from subnlogn.net.certify import _dec, certify_triple, first_saving_h, ln_enclosure, tau_test  # noqa: E402


def main(hs):
    print("| h | kind | W | s | W m - s | eta | tau=1-2^-50 | tau=1-2^-40 | nu, C1, C0 digits | time |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for h in hs:
        for kind in ("bit", "complex"):
            t0 = time.time()
            c = certify_triple(h, kind, dense_scalar=False)
            t40 = tau_test(c.params, 40)[0]
            g = f"{c.guard.nu}, {c.guard.C1}, {c.guard.C0_digits}" if c.guard else "-"
            print(f"| {h} | {kind} | {c.params.W} | {c.params.s} | {c.saving} | {c.eta} | {c.tau_ok} | {t40} | {g} "
                  f"| {time.time() - t0:.1f}s |")
    print(f"\nfirst saving h: bit {first_saving_h('bit')}, complex {first_saving_h('complex')}\n")
    print("| h | m | certified ln m in [lo, hi] (12 digits, outward) | kind | eta 2^40 - L | tau40 | "
          "eta 2^42 - L | tau42 |")
    print("|---|---|---|---|---|---|---|---|")
    for h in hs:
        m = h ** 3
        lo, hi = ln_enclosure(m)
        for kind in ("bit", "complex"):
            c = certify_triple(h, kind, dense_scalar=False, log_bound="sharp", tau_exp=40)
            ok42, mg42 = tau_test(c.params, 42, "sharp")
            lo_s = "-" + _dec(-lo, 12) if lo < 0 else _floor_dec(lo, 12)
            print(f"| {h} | {m} | [{lo_s}, {_dec(hi, 12)}] | {kind} | {_dec(c.tau_margin, 4)} | {c.tau_ok} "
                  f"| {_dec(mg42, 4)} | {ok42} |")
    c = certify_triple(100, "bit", dense_scalar=False)
    print(f"\nq_radix (bit network, h = 100) = {c.q_radix}: {c.q_radix_provenance}")


def _floor_dec(x, digits):
    q = (x.numerator * 10 ** digits) // x.denominator
    return f"{q // 10 ** digits}.{q % 10 ** digits:0{digits}d}"


if __name__ == "__main__":
    main([int(x) for x in sys.argv[1:]] or [21, 22, 27, 39, 40, 100])
