"""Hierarchy-mode coverage pass: one product per SPEC §6.3
shape family (smallest instance: n just above 64 bits, R0 forced to 2^K_root by Dev-9) and per
middle (Bluestein, Walsh), plus the 2D fallback with forced recursion, all with
products="hierarchy" -- every packed product goes through the independent multiplier hierarchy
(SPEC §6.5) and the run asserts that Python's * never handled one.  Prints the wall time per run,
the total, and the component coverage of the union.

Usage: python scripts/hierarchy_coverage.py [--quick] [--jobs N] [--full]
  --quick   skip the K_root = 11, 12 shapes
  --jobs N  run the shapes in N worker processes (wall time ~ the slowest shape); default 1
  --full    no stage isolation at all (hours per bridge shape in Python; see scripts/full_cascade_demo.py)

Stage isolation (for runtime reasons): since word-scale products are routed, every packed
product above ~1000 bits makes Multiply1 call BasicMul once per butterfly product, and a full cascade of a
bridge product takes hours.  By default the bridge runs therefore use the REAL Multiply1 for every packed
and word product with only the Multiply1 -> BasicMul calls replaced by an exact recording stub
(tests/hierarchy_isolation.py); after each run the real BasicMul is verified, exactly and with its internal
FFT counters, on every operand-size pair the stub absorbed (compositional verification).  The 2D fallback
run is a full cascade (no stub).
"""

import random
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, ".")
sys.path.insert(0, "tests")

from subnlogn.context import Ctx  # noqa: E402
from subnlogn.instrument import COMPONENTS, Instrument  # noqa: E402
from subnlogn.multiply import multiply  # noqa: E402
from subnlogn.schedule import test_policy, test_schedule  # noqa: E402

# SPEC §6.3 shapes, plus (8, 2, 1): t = (16, 16), where the bridge's Lemma 12 exchanges have width 4 and
# Proposition 11 runs on the bit network
SHAPES = [(5, 2, 1), (6, 3, 1), (5, 4, 1), (8, 4, 1), (8, 2, 1), (11, 10, 1), (12, 4, 2)]


def runs(quick: bool):
    out = [("2D fallback, forced recursion", None)]
    for K, d, cb in SHAPES:
        if quick and K > 8:
            continue
        for middle in ("bluestein", "walsh"):
            out.append((f"K={K} d={d} K_chunk={cb} {middle}", (K, d, cb, middle)))
    return out


def run_one(item, isolate: bool = True):
    label, spec = item
    stub = None
    if isolate and spec is not None:                     # bridge shape: isolate Multiply1 -> BasicMul
        import subnlogn.hierarchy as H
        from hierarchy_isolation import BasicMulStub
        stub = BasicMulStub(real=H.Hierarchy.basic_mul)
        H.Hierarchy.basic_mul = lambda self, a, b: stub(self, a, b)
    if spec is None:
        schedule, seed = test_schedule(base_threshold=2), 0
    else:
        K, d, cb, middle = spec
        schedule, seed = test_policy(d, chunk_bits=cb, middle=middle, min_root_exponent=K), K
    n = 70
    rng = random.Random(seed)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
    inst = Instrument()
    ctx = Ctx(schedule=schedule, inst=inst, products="hierarchy")
    t0 = time.time()
    assert multiply(a, b, ctx) == a * b
    dt = time.time() - t0
    assert inst.counts.get("python.big_product", 0) == 0
    assert inst.counts.get("python.word_product_over_64", 0) == 0
    info = "full cascade"
    if stub is not None:
        import subnlogn.hierarchy as H
        H.Hierarchy.basic_mul = stub.real
        t1 = time.time()
        npairs = stub.verify_real_basic_mul() if stub.calls else 0
        info = (f"isolated: {stub.calls} BasicMul calls stubbed, real BasicMul verified on {npairs} size "
                f"pairs ({time.time() - t1:.1f} s)")
    return label, dt, dict(inst.counts), info


def main():
    quick = "--quick" in sys.argv
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 1
    items = runs(quick)
    t_start = time.time()
    isolate = "--full" not in sys.argv
    if jobs > 1:
        with ProcessPoolExecutor(max_workers=jobs) as ex:
            results = list(ex.map(run_one, items, [isolate] * len(items)))
    else:
        results = [run_one(it, isolate) for it in items]
    total = Instrument()
    cpu = 0.0
    for label, dt, counts, info in results:
        cpu += dt
        for k, v in counts.items():
            total.hit(k, v)
        print(f"{label:<34} {dt:8.1f} s   multiply1 calls {counts.get('hierarchy.multiply1', 0):6d}   "
              f"network nodes {counts.get('m6.c_power.network', 0):5d}   "
              f"lemma13 {counts.get('lemma13.call', 0):6d}   "
              f"lemma12 net {counts.get('interchange.lemma12_network_call', 0):4d}   "
              f"prop11 nodes {counts.get('interchange.prop11_node', 0):4d}   {info}", flush=True)
    bitnet = [label for label, dt, counts, _ in results if counts.get("interchange.prop11_node", 0)]
    assert {"K=8 d=2 K_chunk=1 bluestein", "K=8 d=2 K_chunk=1 walsh"} <= set(bitnet), \
        "the bit network must run end to end in the t = (16, 16) shape, both middles"
    print(f"\nsum of run times {cpu:.1f} s; wall time {time.time() - t_start:.1f} s with {jobs} job(s); "
          f"python.big_product = {total.counts.get('python.big_product', 0)}, "
          f"python.word_product_over_64 = {total.counts.get('python.word_product_over_64', 0)}")
    missing = [k for k in COMPONENTS if total.counts.get(k, 0) == 0 and k != "python.big_product"]
    print("registered components not reached by these products (informational; BasicMul/Multiply2 need "
          "packed products inside Multiply1, exercised in tests/test_m7_dispatch.py):", missing or "none")


if __name__ == "__main__":
    main()
