"""All-ones operands a = b = 2^n - 1 over
n = 1..300 raised under test_policy for d = 2 (n = 5..8), 4 (5..40), 5 (5..96), 6 (5..224, 256) and
7 (every n in 5..300) with the Bluestein and Walsh middles.  Now every configuration is exact (the
bridge dimension is clamped to the middle's hypotheses, else the 2D FastDFT runs; see
multiply.bridge_dimension).  Fast: the first n of every root class K0 of n <= 300 plus the reported
range ends, for d = 2..7 and 10 and every middle; slow: every n = 1..300."""

import random

import pytest

import path_model as PM
from subnlogn.context import Ctx
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import test_policy

MIDDLES = ("direct", "bluestein", "walsh")
DIMS = (2, 3, 4, 5, 6, 7, 10)


def class_starts(limit: int = 300) -> list[int]:
    """The first n of every root class K0 among n = 1..limit (the bridge dimension depends on K0 only),
    plus the range ends reported by the original sweep."""
    first: dict[int, int] = {}
    for n in range(1, limit + 1):
        first.setdefault(root_parameters(n)[2], n)
    return sorted(set(first.values()) | {5, 8, 40, 96, 224, 256, 300})


def _check(ctx, n: int, seed: int, random_pair: bool = True) -> int:
    """Products at bit length n; returns the number of multiply calls made (each with max bit length n)."""
    a = (1 << n) - 1
    assert multiply(a, a, ctx) == a * a, n
    if random_pair:
        rng = random.Random(seed * 1009 + n)
        x, y = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
        assert multiply(x, y, ctx) == x * y, n
    return 2 if random_pair else 1


@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", DIMS)
def test_all_ones_class_starts(d, middle):
    sched = test_policy(d, middle=middle)
    ctx = Ctx(schedule=sched)
    ns = []
    for n in class_starts():
        ns += [n] * _check(ctx, n, d, random_pair=n in (40, 300))
    c = ctx.inst.counts
    assert c["safety.residue_check"] == c["multiply.call"]
    exp = PM.multiply_counts(sched, ns, PM.nets())          # exact dispatch counts (exact count; path_model)
    PM.assert_exact(c, exp, ["multiply.call", "bridge.dft", "bridge.middle", "bridge.fallback_2d", "bridge.d_clamped"])
    assert exp["bridge.dft"] > 0 and exp["bridge.fallback_2d"] > 0 and (exp["bridge.d_clamped"] > 0) == (d >= 3)


@pytest.mark.slow
@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", DIMS)
def test_all_ones_exhaustive(d, middle):
    """The all-ones probe: every n = 1..300 (plus a random pair per n)."""
    ctx = Ctx(schedule=test_policy(d, middle=middle))
    for n in range(1, 301):
        _check(ctx, n, d)


# ---------------------------------------------------------------- chunk_bits = 2 (Dev-2)


@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", DIMS)
def test_chunk_bits_2_class_starts(d, middle):
    """Dev-2 chunks (chunk_bits = 2) need ell >= 3 for Lemma 16 / the Walsh slices; the bridge dimension
    is clamped accordingly (else the 2D FastDFT runs) (the same ValueError appeared for ell <= 2)."""
    ctx = Ctx(schedule=test_policy(d, middle=middle, chunk_bits=2))
    for n in class_starts():
        _check(ctx, n, 100 + d, random_pair=n in (40, 300))
    c = ctx.inst.counts
    assert c["bridge.fallback_2d"] > 0
    assert c["bridge.dft"] > 0                     # K0 >= 5 admits d' = 2 with ell = 3 >= chunk_bits + 1


@pytest.mark.parametrize("middle", MIDDLES)
def test_random_9bit_operands_test_policy2(middle):
    """Random 9-bit operands under test_policy(2) (K0 = 3, t = (2, 4))."""
    import random as _r
    rng = _r.Random(9)
    for cb in (1, 2):
        ctx = Ctx(schedule=test_policy(2, middle=middle, chunk_bits=cb))
        for _ in range(60):
            a, b = rng.getrandbits(9), rng.getrandbits(9)
            assert multiply(a, b, ctx) == a * b, (a, b, cb)


@pytest.mark.slow
@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", DIMS)
def test_chunk_bits_2_exhaustive(d, middle):
    ctx = Ctx(schedule=test_policy(d, middle=middle, chunk_bits=2))
    for n in range(1, 301):
        _check(ctx, n, 100 + d)
