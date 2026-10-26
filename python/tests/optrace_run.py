"""Run one route under the operation tracer (tests/optrace.py) and write the site table as JSON.
usage: python tests/optrace_run.py ROUTE OUT.json [PATCHES.json]   (from the repository root)"""

import json
import os
import random
import sys
import time

sys.path.insert(0, os.getcwd())
sys.path.insert(0, os.path.join(os.getcwd(), "tests"))
import optrace  # noqa: E402

route, out = sys.argv[1], sys.argv[2]
patches = {}
if len(sys.argv) > 3:
    with open(sys.argv[3]) as fh:
        patches = {k: [tuple(x) for x in v] for k, v in json.load(fh).items()}
optrace.install(patches)

import subnlogn.hierarchy as H  # noqa: E402  (traced copy)
from optrace_routes import ROUTES, STAGES  # noqa: E402  (the route table, shared with the guard test)
from subnlogn.context import Ctx  # noqa: E402
from subnlogn.multiply import multiply, root_parameters  # noqa: E402
parts = route.split(":")
name, products = parts[0], (parts[1] if len(parts) > 1 else "hierarchy")
STUB_CALLS = {"multiply1": 0, "basic": 0}
if "stub" in parts[2:]:
    # Stage isolation: the next hierarchy stage is replaced by an exact, UNTRACED counting product, so
    # only the stage under test is traced (each stage is checked separately: routes multiply1/multiply2/
    # basic below).  The guard then asks that every long product of the traced stage was handed to it.
    def _stub(stage):
        def f(self, x, y):
            STUB_CALLS[stage] += 1
            return x * y
        return f
    nxt = {"multiply2": ["multiply1"], "multiply1": ["basic"], "basic_mul": []}.get(
        STAGES[name][0] if name in STAGES else "", ["multiply1", "basic"])
    if "multiply1" in nxt:
        H.Hierarchy.multiply1 = _stub("multiply1")
    if "basic" in nxt:
        H.Hierarchy.basic_mul = _stub("basic")
t0 = time.time()
rng = random.Random(len(name) * 1000)
if name in STAGES:
    stage, n, kw = STAGES[name]
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
    h = H.Hierarchy(**kw())
    assert getattr(h, stage)(a, b) == a * b
    sched = h.stage_schedule if stage == "multiply2" else (h.multiply1_schedule if stage == "multiply1"
                                                            else H.basic_schedule())
    counts = dict(h.inst.counts)
else:
    factory, n = ROUTES[name]
    sched = factory()
    ctx = Ctx(schedule=sched, products=products)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
    assert multiply(a, b, ctx) == a * b
    counts = dict(ctx.inst.counts)
_, _, K0, R0, p0 = root_parameters(n, sched.min_root_exponent)
levels = [max(lv.q_child, lv.q_b) for lv in sched.chain(R0, p0)]
if sched.bridge_d is not None:
    P, _, _ = sched.bridge_params(p0, K0, sched.bridge_d)
    levels.append(P + 2)
res = {"route": route, "n": n, "secs": round(time.time() - t0, 2), "word_scale": 4 * max(levels),
       "counts": counts, "stub_calls": STUB_CALLS, "sites": optrace.report(), "a": a, "b": b}
with open(out, "w") as fh:
    json.dump(res, fh)
