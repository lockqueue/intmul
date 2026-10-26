"""Full-cascade demonstration: ONE bridge product end to end in
products="hierarchy" with NO stub anywhere -- every packed product (the bridge overlap-add; for Bluestein
also the Lemma 17 ring products) and every word-scale product with an operand above 64 bits goes to the
independent hierarchy (Multiply1, whose own products above 64 bits go to BasicMul; BasicMul is schoolbook,
MS Thm 7.1 part 3 Stage 0).  Logs the wall time, every counter, python.word_product_over_64 = 0,
python.big_product = 0 and the exact product check; a background thread prints counter snapshots
(read-only) so long runs show progress.

usage: python scripts/full_cascade_demo.py ROUTE [--n N] [--d D] [--K K] [--seed S] [--log FILE]
  ROUTE in {walsh, bluestein}; defaults: the smallest bridge shape d = 2, K_root = 5 (t = (4, 8)), n = 70
  (Walsh: the middle of the retuned kappa = 2^-47 route of SPEC_WALSH, here under the SPEC §6.3 test policy:
  forced batching, compiled guard, fixtures C1/B1 -- the theorem rows' published guard is not executable).
"""

import argparse
import json
import random
import sys
import threading
import time

sys.path.insert(0, ".")

from subnlogn.context import Ctx  # noqa: E402
from subnlogn.multiply import multiply, root_parameters  # noqa: E402
from subnlogn.schedule import test_policy  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("route", choices=["walsh", "bluestein"])
    ap.add_argument("--n", type=int, default=70)
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--K", type=int, default=5)
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--log", default=None)
    ap.add_argument("--every", type=int, default=300, help="seconds between progress snapshots")
    args = ap.parse_args()
    sched = test_policy(args.d, middle=args.route, min_root_exponent=args.K)
    rng = random.Random(args.seed)
    a = rng.getrandbits(args.n) | (1 << (args.n - 1))
    b = rng.getrandbits(args.n) | 1
    ctx = Ctx(schedule=sched, products="hierarchy")
    b_, N, K0, R0, p0 = root_parameters(args.n, sched.min_root_exponent)
    head = (f"full-cascade demo: route={args.route} d={args.d} K_root={K0} R0={R0} n={args.n} seed={args.seed} "
            f"products=hierarchy (no stub); bridge P = {sched.bridge_params(p0, K0, args.d)[0]}")
    print(head, flush=True)
    stop = threading.Event()
    t0 = time.time()

    def progress():
        while not stop.wait(args.every):
            c = ctx.inst.counts
            print(f"  [{time.time() - t0:8.0f} s] multiply1 {c.get('hierarchy.multiply1', 0)}  basic "
                  f"{c.get('hierarchy.basic', 0)}  word products routed {c.get('hierarchy.word_product', 0)}",
                  flush=True)
    th = threading.Thread(target=progress, daemon=True)
    th.start()
    out = multiply(a, b, ctx)
    wall = time.time() - t0
    stop.set()
    c = dict(ctx.inst.counts)
    ok = out == a * b
    res = {"route": args.route, "d": args.d, "K_root": K0, "R0": R0, "n": args.n, "seed": args.seed,
           "wall_s": round(wall, 1), "exact": ok,
           "python.word_product_over_64": c.get("python.word_product_over_64", 0),
           "python.big_product": c.get("python.big_product", 0),
           "hierarchy.multiply1": c.get("hierarchy.multiply1", 0), "hierarchy.basic": c.get("hierarchy.basic", 0),
           "hierarchy.word_product": c.get("hierarchy.word_product", 0), "counters": c}
    lines = [head, f"wall time {wall:.1f} s; product exact: {ok}",
             f"python.word_product_over_64 = {res['python.word_product_over_64']}, "
             f"python.big_product = {res['python.big_product']}",
             f"Multiply1 calls {res['hierarchy.multiply1']}, BasicMul calls {res['hierarchy.basic']}, "
             f"word-scale products routed {res['hierarchy.word_product']}",
             "counters: " + json.dumps(c, sort_keys=True)]
    print("\n".join(lines[1:]), flush=True)
    if args.log:
        with open(args.log, "w") as fh:
            fh.write("\n".join(lines) + "\n")
    good = ok and res["python.word_product_over_64"] == 0 and res["python.big_product"] == 0
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
