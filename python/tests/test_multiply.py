"""End-to-end products (M1 acceptance): bit-exact against Python's * on random and adversarial
inputs, under the faithful schedule and under forced-deep test schedules (depth >= 3)."""

import random

import pytest

from conftest import make_ctx
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import faithful_schedule, test_schedule


def adversarial(n: int, rng: random.Random):
    ones = (1 << n) - 1
    alt = int("10" * (n // 2) + "1" * (n % 2), 2) if n > 1 else 1
    sparse = sum(1 << rng.randrange(n) for _ in range(max(1, n // 200))) | (1 << (n - 1))
    b = max(4, n.bit_length() - 1)
    maxchunk_alt = 0
    for j in range(0, n, 2 * b):
        maxchunk_alt |= ((1 << b) - 1) << j
    maxchunk_alt &= ones
    rnd = rng.getrandbits(n) | (1 << (n - 1))
    small = rng.getrandbits(max(1, n // 7)) | 1
    return [
        (ones, ones), (alt, alt), (alt, ones), (sparse, ones), (maxchunk_alt, maxchunk_alt),
        (rnd, small), (small, rnd), (1 << (n - 1), 1 << (n - 1)), (ones, 1), (0, ones), (rnd, 0),
        (1, 1), (rnd, rnd),
    ]


@pytest.mark.parametrize("n", [65, 100, 257, 1000, 3000, 12000])
def test_multiply_faithful(n):
    rng = random.Random(n)
    ctx = make_ctx(faithful_schedule())
    for a, b in adversarial(n, rng):
        assert multiply(a, b, ctx) == a * b


@pytest.mark.parametrize("n", [1, 2, 5, 17, 40, 64, 200, 777, 1500])
def test_multiply_deep_test_schedule(n):
    rng = random.Random(1000 + n)
    sched = test_schedule(base_threshold=2)
    ctx = make_ctx(sched)
    for a, b in adversarial(n, rng):
        assert multiply(a, b, ctx) == a * b
    _, _, K0, R0, p0 = root_parameters(n)
    if R0 >= 32:
        assert len(sched.chain(R0, p0)) - 1 >= 3


def test_multiply_signs_and_small():
    ctx = make_ctx(test_schedule(base_threshold=2))
    for a, b in [(0, 0), (1, 0), (0, 1), (1, 1), (-3, 5), (7, -9), (-11, -13), (2**70 + 3, -(2**65))]:
        assert multiply(a, b, ctx) == a * b


@pytest.mark.parametrize("n", [100, 500])
def test_multiply_other_thresholds(n):
    rng = random.Random(7 * n)
    for bt in (4, 16, 64):
        ctx = make_ctx(test_schedule(base_threshold=bt))
        a, b = rng.getrandbits(n), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b


@pytest.mark.slow
@pytest.mark.parametrize("n", [30000, 100000])
def test_multiply_faithful_large(n):
    rng = random.Random(n)
    ctx = make_ctx(faithful_schedule())
    for a, b in adversarial(n, rng)[:6]:
        assert multiply(a, b, ctx) == a * b


@pytest.mark.slow
@pytest.mark.parametrize("n", [10000, 100000])
def test_multiply_deep_large(n):
    rng = random.Random(n + 1)
    sched = test_schedule(base_threshold=2)
    ctx = make_ctx(sched)
    for a, b in adversarial(n, rng)[:4]:
        assert multiply(a, b, ctx) == a * b
    _, _, K0, R0, p0 = root_parameters(n)
    assert len(sched.chain(R0, p0)) - 1 >= 3


from hypothesis import given, settings, strategies as st  # noqa: E402

_PROP_CTX = {}


@settings(max_examples=40)
@given(st.integers(min_value=0, max_value=(1 << 400) - 1), st.integers(min_value=0, max_value=(1 << 400) - 1))
def test_multiply_property_deep(a, b):
    """Property: multiply(a, b) == a * b under the forced-deep test schedule (bt = 2)."""
    ctx = _PROP_CTX.setdefault("deep", make_ctx(test_schedule(base_threshold=2)))
    assert multiply(a, b, ctx) == a * b


@settings(max_examples=25)
@given(st.integers(min_value=0, max_value=(1 << 3000) - 1), st.integers(min_value=0, max_value=(1 << 3000) - 1))
def test_multiply_property_faithful(a, b):
    ctx = _PROP_CTX.setdefault("faithful", make_ctx(faithful_schedule()))
    assert multiply(a, b, ctx) == a * b


@pytest.mark.slow
def test_multiply_faithful_recursive_1e6():
    """At n = 10^6 bits the faithful schedule recurses once by itself: R0 = 2^17 > 4 p0^2 with
    p0 = 78 (MS listing l.733), so the certified 2D algorithm runs with no forcing."""
    n = 10 ** 6
    _, _, K0, R0, p0 = root_parameters(n)
    sched = faithful_schedule()
    assert not sched.level(R0, p0).leaf
    rng = random.Random(6)
    ctx = make_ctx(sched)
    a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
    assert multiply(a, b, ctx) == a * b
    assert ctx.inst.counts["fastdft.node"] == 2   # one recursive node per top-level transform
