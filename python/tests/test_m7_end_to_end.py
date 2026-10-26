"""M7 end-to-end acceptance (SPEC §6.7): bit-exact products against a * b for the special operand
families of §6.7 and every SPEC §6.3 shape, through the faithful dispatcher (2D fallback) and the
test policies (bridge + Bluestein middle + network engine; direct middle; M3 direct layers).

Path claims are pinned by EXACT counts: every counter of ``path_model.PATH_KEYS`` (bridge calls,
middles, movements, Lemma 16 layouts, Prop 14 layers, network nodes, Lemma 13 calls, Lemma 12 network calls, the
paths that must not run) equals the independent closed form of ``tests/path_model.py`` for the operand lengths
used, so a partial silent fallback (one layer or middle call taking a shortcut) fails."""

import random

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.geometry import balanced_factors
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import faithful_schedule, test_policy, test_schedule


def n_range_for_K(K: int) -> tuple[int, int]:
    """Smallest and largest operand bit length n > 64 whose two-call root has K0 = K."""
    ns = [n for n in range(65, 40000) if root_parameters(n)[2] == K]
    return ns[0], ns[-1]


def special_operands(n: int, seed: int = 0):
    """SPEC §6.7 families at bit length n (b = digit width): zero, one, powers of two, all ones
    (maximal digits), alternating bits, sparse high/low digits, partial leading digit, unequal
    actual lengths under a common n, random."""
    rng = random.Random(seed * 1000 + n)
    b = root_parameters(n)[0]
    ones = (1 << n) - 1
    alt = int("10" * (n // 2) + "1" * (n % 2), 2)
    rnd = rng.getrandbits(n) | (1 << (n - 1))
    yield "zero", 0, rnd
    yield "one", 1, rnd
    yield "powers", 1 << (n - 1), 1 << (n // 2)
    yield "all_ones", ones, ones
    yield "alternating", alt, alt >> 1
    yield "sparse", 1 | (1 << (n - 1)), (1 << b) | (1 << (n - 1))
    yield "partial_lead", (1 << (n - 3)) | rng.getrandbits(n - 3), ones >> 2
    yield "unequal", rnd, rng.getrandbits(max(1, n // 4)) | 1
    yield "random", rng.getrandbits(n), rng.getrandbits(n)


SHAPES = [   # SPEC §6.3: (K_root, d, t, chunk_bits, layer D, network?, slow)
    (5, 2, (4, 8), 1, 1, False, False),
    (6, 3, (4, 4, 4), 1, 2, False, False),
    (5, 4, (2, 2, 2, 4), 1, 3, True, False),
    (8, 4, (4, 4, 4, 4), 1, 3, True, False),
    (11, 10, (2,) * 9 + (4,), 1, 9, True, True),
    (12, 4, (8, 8, 8, 8), 2, 3, True, True),
]


def test_shape_table_geometry():
    for K, d, t, cb, D, _, _ in SHAPES:
        assert balanced_factors(K, d) == t
        assert len(t) - 1 == D


@pytest.mark.parametrize("shape", [s for s in SHAPES if not s[6]], ids=lambda s: f"K{s[0]}d{s[1]}")
def test_spec_shapes_special_operands(shape):
    K, d, t, cb, D, network, _ = shape
    lo, hi = n_range_for_K(K)
    sched = test_policy(d, chunk_bits=cb)
    pairs = [(a, b) for n in sorted({lo, (lo + hi) // 2, hi}) for _, a, b in special_operands(n, seed=K)]
    exp = run_exact(sched, pairs)
    assert exp["bridge.dft"] == 2 * len(pairs) and exp["prop14.network_layer"] > 0
    assert (exp["m6.c_power.network"] > 0) == network          # the table's flag, against the closed form


@pytest.mark.slow
@pytest.mark.parametrize("shape", [s for s in SHAPES if s[6]], ids=lambda s: f"K{s[0]}d{s[1]}")
def test_spec_shapes_slow(shape):
    K, d, t, cb, D, network, _ = shape
    lo, hi = n_range_for_K(K)
    rng = random.Random(K)
    pairs = [(rng.getrandbits(hi), rng.getrandbits(hi)), ((1 << lo) - 1, (1 << lo) - 1)]
    assert run_exact(test_policy(d, chunk_bits=cb), pairs)["m6.c_power.network"] > 0


@pytest.mark.parametrize("middle,direct_layers", [("direct", False), ("bluestein", True)])
def test_other_middles_and_m3_mode(middle, direct_layers):
    """The same products with the direct middle (M2 reference) and with M3 direct layers."""
    lo, hi = n_range_for_K(5)
    exp = run_exact(test_policy(4, middle=middle, direct_layers=direct_layers),
                    [(a, b) for _, a, b in special_operands(hi, seed=3)])
    assert exp["prop14.network_layer"] == exp["m6.layer.network"] == 0


@pytest.mark.parametrize("n", [1, 2, 63, 64, 65, 96, 97, 127, 128, 129, 255, 256, 257, 1000, 4097])
def test_faithful_dispatcher_boundaries(n):
    """Faithful schedule: n <= 64 is the listing's direct product (MS line 706); above it the
    dispatcher finds no theorem shape and runs the 2D fallback (SPEC §6.2, §6.4)."""
    ctx = make_ctx(faithful_schedule())
    ns = []
    for name, a, b in special_operands(max(n, 8), seed=n):
        a &= (1 << n) - 1
        b &= (1 << n) - 1
        assert multiply(a, b, ctx) == a * b, name
        ns += PM.bit_lengths([(a, b)])
    big = sum(1 for m in ns if m > 64)                  # listing L706: n <= 64 -> A * B
    PM.assert_exact(ctx.inst.counts, {"multiply.direct": len(ns) - big, "multiply.call": big,
                                      "multiply.fallback_2d": 2 * big, "multiply.theorem_mode": 0, "bridge.dft": 0})


def test_root_boundaries_deep_2d():
    """Lengths around the root-size boundaries (2N - 1 crossing a power of two) with the forced
    deep 2D recursion."""
    ctx = make_ctx(test_schedule(base_threshold=2))
    for K in (5, 6, 7):
        lo, hi = n_range_for_K(K)
        for n in (lo - 1, lo, hi, hi + 1):
            rng = random.Random(n)
            a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n) | 1
            assert multiply(a, b, ctx) == a * b


def test_dev9_min_root_exponent():
    """Dev-9 (test only): R0 enlarged beyond the MS minimum (R0 >= 2N kept, p recomputed) lets a
    small product run a larger shape; still exact."""
    rng = random.Random(9)
    pairs = [(rng.getrandbits(100), rng.getrandbits(100)) for _ in range(3)]
    assert run_exact(test_policy(4, min_root_exponent=8), pairs)["m6.c_power.network"] > 0


@pytest.mark.parametrize("seed", range(6))
def test_random_seeds_network_shape(seed):
    """Random lengths through test_policy(4): bridge, Bluestein, network engine, Lemma 13, Lemma 12 movements."""
    rng = random.Random(100 + seed)
    n = rng.randint(70, 300)
    a, b = rng.getrandbits(n), rng.getrandbits(rng.randint(1, n))
    exp = run_exact(test_policy(4), [(a, b), (-a, b)])
    assert exp["m6.c_power.network"] > 0 and exp["lemma13.call"] > 0 and exp["layout.executed"] > 0


def run_exact(sched, pairs, ctx=None):
    """Multiply every pair exactly under ``sched`` and pin every counter of PM.PATH_KEYS to the independent
    closed form: bridge DFTs, middles, Lemma 16 layouts executed on the stream,
    the bridge's Lemma 12 exchanges, every Prop 14 layer through the network engine with its nodes and Lemma 13
    calls (none through the address-permutation oracle), Lemma 12 network calls.  Returns the expected counts."""
    ctx = make_ctx(sched) if ctx is None else ctx
    for i, (a, b) in enumerate(pairs):
        assert multiply(a, b, ctx) == a * b, (i, a.bit_length(), b.bit_length())
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    return exp


def test_lemma16_chunk_exchanges_end_to_end(monkeypatch):
    """No SPEC §6.3 shape has a Lemma 16 chunk exchange (q = floor((l-1)/K) <= 1 in every row), so the
    layout's Lemma 12 exchanges (SPEC §5.2) never ran end to end.  With d = 3 at K0 = 8 (t = (4, 8, 8), l = 3,
    K = 1: q = 2 chunks per record axis) each layout L and L^-1 makes one exchange, through swap_via_lemma12
    (Lemma 12 on record IDs, D12); every call is counted."""
    import subnlogn.m6.engine as eng
    from subnlogn.middle3.layout import layout_plan
    orig = eng.movement_from_schedule
    calls = []

    def counting(ctx):
        swap = orig(ctx)

        def wrapped(stream, shape, a, b, inst=None):
            calls.append((a, b))
            return swap(stream, shape, a, b, inst)
        return wrapped

    monkeypatch.setattr(eng, "movement_from_schedule", counting)
    assert balanced_factors(8, 3) == (4, 8, 8)
    lo, hi = n_range_for_K(8)
    rng = random.Random(8)
    a, b = rng.getrandbits(hi) | (1 << (hi - 1)), rng.getrandbits(lo)
    exp = run_exact(test_policy(3), [(a, b)])
    per_layout = PM.layout_exchanges(2, 3, 1)               # SPEC §5.2 scan: one exchange per L (and L^-1)
    assert per_layout == len([m for m in layout_plan((4, 8), 3, 1).moves if m[0] == "xchg"]) == 1
    assert len(calls) == exp["layout.executed"] * per_layout == 6     # 3 procedures x 2 middles x 1
