import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from hypothesis import settings, HealthCheck  # noqa: E402

settings.register_profile("default", deadline=None, max_examples=60,
                          suppress_health_check=[HealthCheck.too_slow])
settings.register_profile("slow", deadline=None, max_examples=400,
                          suppress_health_check=[HealthCheck.too_slow])
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "default"))

import pytest  # noqa: E402

#: One table cache per test worker process (tables are deterministic functions of their keys);
#: passed explicitly into each Ctx, so the library itself keeps no global state.
_TABLES: dict = {}


@pytest.fixture
def tables():
    return _TABLES


def make_ctx(schedule, tables_dict=None, monitor=False, capture=False):
    from subnlogn.context import Ctx
    from subnlogn.instrument import Instrument
    return Ctx(schedule=schedule, inst=Instrument(monitor_heights=monitor),
               tables=_TABLES if tables_dict is None else tables_dict,
               capture={} if capture else None)


@pytest.fixture(autouse=True)
def _no_certified_fallback():
    """Fail loudly if any certified table entry fell back to faithful (non-correct) rounding
    (subnlogn.certified.FALLBACK_EVENTS)."""
    from subnlogn import certified
    before = len(certified.FALLBACK_EVENTS)
    yield
    assert len(certified.FALLBACK_EVENTS) == before, \
        f"certified fallback happened: {certified.FALLBACK_EVENTS[before:]}"


@pytest.fixture
def basic_mul_stub(monkeypatch):
    """Replace Hierarchy.basic_mul by an exact counting stub for this test (stage isolation; see
    tests/hierarchy_isolation.py)."""
    from hierarchy_isolation import BasicMulStub
    from subnlogn.hierarchy import Hierarchy
    stub = BasicMulStub(real=Hierarchy.basic_mul)
    monkeypatch.setattr(Hierarchy, "basic_mul", lambda self, a, b: stub(self, a, b))
    return stub
