"""Instrumentation (M0): counters, height monitor, merge and the component coverage report."""

from conftest import make_ctx
from subnlogn.instrument import COMPONENTS, Instrument
from subnlogn.multiply import multiply
from subnlogn.schedule import test_schedule


def test_counters_merge_and_report():
    a = Instrument(monitor_heights=True)
    a.hit("fastdft.node")
    a.height("k", [7, -9], [3])
    a.note("x", 1)
    b = Instrument()
    b.hit("fastdft.node", 2)
    b.hit("unregistered.thing")
    b.merge(a)
    assert b.counts["fastdft.node"] == 3
    assert b.heights["k"] == 4
    rep = b.coverage_report()
    assert "!multiply.call" in rep and "?unregistered.thing" in rep
    assert all(name in rep for name in COMPONENTS)


def test_multiply_hits_core_components():
    ctx = make_ctx(test_schedule(base_threshold=2))
    multiply((1 << 300) - 1, (1 << 299) + 12345, ctx)
    for name in ("fastdft.node", "fastdft.leaf", "spread.row", "kron.product", "twist.pre",
                 "synfft.butterfly", "twist.post", "route.oddstride", "solver.forward",
                 "solver.backward", "multiply.call"):
        assert ctx.inst.counts[name] > 0, name
