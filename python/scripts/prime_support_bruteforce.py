"""Brute-force confirmation of the prime support of the bit triple network (steps 1-6 of the certificate).

Usage: .venv/bin/python scripts/prime_support_bruteforce.py [--workers 4] [--quick] [--mixed]

1. Exhaustive ordered one-factor primitives at h = 7, 8, 10, 11, 12: L_T, I - L_T (all triples), I - L_S - L_T and
   the gadget (all ordered pairs with |S cap T| = 1), literal SPEC §3.1 Lemma 9 elimination, exact
   reconstruction / inverses / triangularity, identities re-checked mod 5 and mod 125; prime support collected.
2. Exhaustive two-coordinate tensor-line projections L_S (x) L_T and I - L_S (x) L_T at h = 7 (h^2 = 49).
3. Full h^3 x h^3 edge matrices (h = 7, 8) of random roles of every edge class and stage, factored literally;
   ranks compared with the symbolic certificate.
--mixed: a deterministic sample of 4410 (20%) of the 22050 two-factor mixed edges I (x) D0 - P0 (x) K at
h = 7 (49 x 49).
Prints a markdown report.
"""

import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from subnlogn.net.primes import PrimeReport, brute_force_primitives, full_edge_primes  # noqa: E402
from subnlogn.net.triple import TripleNetwork  # noqa: E402
from subnlogn.net.triple_dense import sample_roles  # noqa: E402


def _prims(args):
    h, tl, part, parts = args
    return brute_force_primitives(h, tensor_lines=tl, part=part, parts=parts)


def _role(args):
    h, rid = args
    tn = TripleNetwork(h, "bit")
    t0 = time.time()
    rows = full_edge_primes(tn, rid)
    return rid, tn.role_name(rid)[0], [(cls, s, r, sorted(p)) for cls, s, r, p in rows], time.time() - t0


def _mixed(args):
    h, part, parts, n = args
    return brute_force_primitives(h, part=part, parts=parts, mixed=n, seed=2026, primitives=False, mod_exps=())


def main_mixed(workers: int, h: int = 7, n: int = 4410):
    """A deterministic random sample (seed 2026) of n of the two-factor mixed edges I (x) D0 - P0 (x) K at h
    (prefix triple x ordered neighbor pair; 22050 at h = 7), literal elimination with exact checks."""
    with ProcessPoolExecutor(workers) as ex:
        reps = list(ex.map(_mixed, [(h, k, workers * 4, n) for k in range(workers * 4)]))
    tot = PrimeReport(h)
    for r in reps:
        tot.merge(r)
    assert tot.primes <= {2, 3}
    print(f"h = {h}: {tot.counts} two-factor mixed edges ({h * h} x {h * h}), prime support {sorted(tot.primes)}, "
          f"CPU {tot.seconds:.1f} s", flush=True)


def main(workers: int, quick: bool):
    hs = (7, 8) if quick else (7, 8, 10, 11, 12)
    print("## 1. Exhaustive one-factor primitives (literal SPEC §3.1 elimination)\n")
    print("Factor-level primitives (one tensor factor, dimension <= 2h), not network edges; the network-edge "
          "checks are section 3 (full h^3 x h^3 edge matrices) and section 4 (mixed two-factor edges).\n")
    print("| h | L_T | I-L_T | I-L_S-L_T | gadget | max dim | prime support | CPU s |")
    print("|---|---|---|---|---|---|---|---|")
    with ProcessPoolExecutor(workers) as ex:
        for h in hs:
            reps = list(ex.map(_prims, [(h, False, k, workers * 4) for k in range(workers * 4)]))
            tot = PrimeReport(h)
            for r in reps:
                tot.merge(r)
            c = tot.counts
            print(f"| {h} | {c['L_T']} | {c['I-L_T']} | {c['I-L_S-L_T']} | {c['gadget']} | {tot.max_dim} | "
                  f"{sorted(tot.primes)} | {tot.seconds:.1f} |", flush=True)
            assert tot.primes <= {2, 3}
        print("\n## 2. Two-coordinate tensor lines L_S (x) L_T and complements (h^2 x h^2)\n")
        for h in ((7,) if quick else (7,)):
            reps = list(ex.map(_prims, [(h, True, k, workers * 4) for k in range(workers * 4)]))
            tot = PrimeReport(h)
            for r in reps:
                tot.merge(r)
            print(f"h = {h}: {tot.counts}, max dim {tot.max_dim}, prime support {sorted(tot.primes)}, "
                  f"CPU {tot.seconds:.1f} s", flush=True)
            assert tot.primes <= {2, 3}
        print("\n## 3. Full h^3 x h^3 edge matrices of random roles (every edge class, every stage)\n")
        for h, per_stage in ((7, 1) if quick else (7, 4), (8, 1)):
            tn = TripleNetwork(h, "bit")
            roles = sample_roles(tn, per_stage, seed=h)
            classes, primes, edges, cpu = {}, set(), 0, 0.0
            for rid, kind, rows, sec in ex.map(_role, [(h, r) for r in roles]):
                cpu += sec
                for cls, s, r, p in rows:
                    assert s == r, (h, rid, cls, s, r)
                    classes[cls] = classes.get(cls, 0) + 1
                    primes |= set(p)
                    edges += 1
            assert primes <= {2, 3}
            print(f"h = {h} (m = {h ** 3}): {len(roles)} roles, {edges} edges, {len(classes)} (stage, class) "
                  f"combinations, symbolic rank = dense rank on every edge, prime support {sorted(primes)}, "
                  f"CPU {cpu:.1f} s", flush=True)


if __name__ == "__main__":
    w = int(sys.argv[sys.argv.index("--workers") + 1]) if "--workers" in sys.argv else 4
    if "--mixed" in sys.argv:
        main_mixed(w)
    else:
        main(w, "--quick" in sys.argv)
