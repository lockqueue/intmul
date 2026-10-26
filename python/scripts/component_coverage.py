"""Algorithm-component coverage (instrumentation report): run one small multiply under the deep
test schedule (2D FastDFT) and one per bridge dimension, and print which registered components
were exercised (subnlogn.instrument.COMPONENTS)."""

import sys

sys.path.insert(0, ".")

from subnlogn.context import Ctx  # noqa: E402
from subnlogn.instrument import Instrument  # noqa: E402
from subnlogn.multiply import multiply  # noqa: E402
from subnlogn.schedule import faithful_schedule, test_schedule  # noqa: E402

total = Instrument()
tables: dict = {}
for sched, n in [(test_schedule(base_threshold=2), 400), (faithful_schedule(), 50),
                 (faithful_schedule(), 300), (test_schedule(bridge_d=5), 20)] + [
                    (test_schedule(bridge_d=d), 60 if d == 5 else 300) for d in (2, 3, 4, 5)] + [
                    (test_schedule(bridge_d=2).with_(bridge_middle="bluestein"), 120),
                    (test_schedule(bridge_d=4).with_(bridge_middle="bluestein", prop14_layer="network",
                                                     bridge_movement="lemma12"), 120),
                    (test_schedule(bridge_d=4).with_(bridge_middle="walsh", prop14_layer="network",
                                                     bridge_movement="lemma12"), 120)]:
    ctx = Ctx(schedule=sched, tables=tables)
    a = (1 << n) - 12345
    b = (1 << (n - 3)) + 987654321
    assert multiply(a, b, ctx) == a * b
    total.merge(ctx.inst)
# no admissible bridge dimension (K0 = 2 for a Lemma 16 middle): the 2D FastDFT runs (bridge.fallback_2d)
ctx = Ctx(schedule=test_schedule(bridge_d=4).with_(bridge_middle="bluestein"), tables=tables)
assert multiply(200, 150, ctx) == 30000
total.merge(ctx.inst)
# independent multiplier hierarchy (SPEC §6.5): Multiply1 -> BasicMul and Multiply2 -> Multiply1
from subnlogn.hierarchy import Hierarchy  # noqa: E402
one_level = test_schedule(base_threshold=None, max_depth=1)
a, b = (1 << 70) - 999, (1 << 69) + 12345
assert Hierarchy(total, tables, one_level).multiply1(a, b) == a * b
assert Hierarchy(total, tables, one_level, faithful_schedule()).multiply2(a, b) == a * b
# Lemma 13 with L = f K = 4: chunk exchanges through Lemma 12 and the bit network B1 (SPEC §4.10)
from subnlogn.interchange import InterchangePolicy  # noqa: E402
from subnlogn.m6 import lemma13  # noqa: E402
from subnlogn.net import compile_network  # noqa: E402
from subnlogn.net.fixtures import fixture_B1  # noqa: E402
from subnlogn.stream import Field, Shape  # noqa: E402
sh = Shape((Field("N0", 1), Field("y", 16, 2), Field("N1", 1), Field("x", 16, 2), Field("N2", 1),
            Field("z", 16, 2), Field("N3", 1)), 1)
swap = lemma13.swap_via_lemma12(compile_network(fixture_B1()), InterchangePolicy())
recs = list(range(sh.volume))
got, _ = lemma13.packed_selected_add(recs, sh, {c: c for c in "xyz"}, 2, 2, 1, swap=swap, inst=total)
assert got == lemma13.packed_selected_add(recs, sh, {c: c for c in "xyz"}, 2, 2, 1)[0]
# the Dev-5 exceptional set: B neither empty nor total (lemma13.repair_partial)
assert got == lemma13.packed_selected_add(recs, sh, {c: c for c in "xyz"}, 2, 2, 1, bad_set="safe_segments",
                                          inst=total)[0]
# Walsh route on t = (4, 4, 8, 8) with chunk width h = 2 (SPEC_WALSH §4-§5): leftover positions (m0 = 7 is
# odd), both gadget parities, prefix and chunk rounds
import random  # noqa: E402
from subnlogn.walsh.fft import tensor_fft_walsh  # noqa: E402
from subnlogn.walsh.gadget import WalshCtx  # noqa: E402
rng = random.Random(1)
lim = (1 << 40) * 7 // 20
wrecs = [([rng.randint(-lim, lim) for _ in range(8)], [rng.randint(-lim, lim) for _ in range(8)]) for _ in range(128)]
tensor_fft_walsh(wrecs, (4, 4, 8, 8), 40, WalshCtx(d=4, h=2, engine=None, inst=total))
print(total.coverage_report())
missing = [k for k in __import__("subnlogn.instrument", fromlist=["COMPONENTS"]).COMPONENTS
           if total.counts.get(k, 0) == 0]
print("\nall components exercised" if not missing else f"\nNOT exercised: {missing}")
