"""Regression tests: forced-dimension sweeps over every middle and product mode, the dimension clamp, the
bit network end to end, and the recovery check."""

import random
from fractions import Fraction

import pytest

import hierarchy_exact as HE
import path_model as PM
from subnlogn.context import Ctx
from subnlogn.multiply import bridge_dimension, multiply, root_parameters
from subnlogn.schedule import test_policy, test_schedule

MIDDLES = ("direct", "bluestein", "walsh")


def sweep_lengths(limit: int = 3200) -> list[int]:
    """For every root exponent K0 reached by n <= limit: the smallest and largest such n, plus the
    regression examples (n = 5..8, 20, 40, 1000, 3000)."""
    by: dict[int, list[int]] = {}
    for n in range(1, limit):
        by.setdefault(root_parameters(n)[2], []).append(n)
    ns = {v for k in by.values() for v in (k[0], k[-1])}
    return sorted(ns | {5, 6, 7, 8, 20, 40, 1000, 3000})


def _operands(n: int, seed: int):
    rng = random.Random(seed * 7919 + n)
    a = rng.getrandbits(n) | (1 << (n - 1))
    b = rng.getrandbits(n) | 1
    return [(a, b), ((1 << n) - 1, (1 << n) - 1)]


# ---------------------------------------------------------------------------- dimension clamp


@pytest.mark.parametrize("middle", MIDDLES)
def test_bridge_dimension_rules(middle):
    """Largest admissible d' <= d: direct needs K >= d'; Bluestein/Walsh need ell = ceil(K/d') >= 2
    and 1 <= chunk_bits <= ell - 1 (Lemma 16); None means the 2D FastDFT."""
    for d in (2, 3, 4, 10):
        for K in range(1, 16):
            for cb in (1, 2):
                sch = test_policy(d, middle=middle, chunk_bits=cb)
                dd = bridge_dimension(sch, K)
                ok = (lambda x: x <= K) if middle == "direct" else \
                    (lambda x: -(-K // x) >= 2 and cb <= -(-K // x) - 1)
                cands = [x for x in range(2, min(d, K) + 1) if ok(x)]
                assert dd == (max(cands) if cands else None), (middle, d, K, cb)


def _sweep(d, middle, kmax):
    """The sweep's products, with every dispatch and path counter exact (path_model): bridge DFTs,
    clamps, 2D fallbacks (and their FastDFT nodes/leaves), middles, movements, layouts, Prop 14 layers."""
    sched = test_policy(d, middle=middle)
    ctx = Ctx(schedule=sched)
    pairs = []
    for n in [v for v in sweep_lengths() if root_parameters(v)[2] <= kmax]:
        for a, b in _operands(n, d):
            assert multiply(a, b, ctx) == a * b, (n, d, middle)
            pairs.append((a, b))
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS + ("fastdft.node", "fastdft.leaf"))
    return exp


@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", [2, 3, 4, 10])
def test_small_n_sweep_python_mode(d, middle):
    """Exact products for every root size K0 = 1..8 (n up to 1280; K0 = 9, 10 in the slow suite),
    every forced dimension and middle: no configuration raises; clamping and the
    2D fallback are counted."""
    exp = _sweep(d, middle, 8)                              # exact counts: see _sweep
    assert exp["bridge.dft"] > 0 and (exp["bridge.d_clamped"] > 0) == (d >= 3)
    assert exp["bridge.fallback_2d"] > 0                    # K0 = 1 (and K0 <= 2 for Lemma 16)


@pytest.mark.slow
@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", [2, 3, 4, 5, 6, 7, 10])
def test_small_n_sweep_python_mode_large(d, middle):
    """K0 = 9, 10 (n up to ~3200) of the same sweep."""
    assert _sweep(d, middle, 10)["bridge.dft"] > 0          # exact counts: see _sweep


def _hierarchy_sweep(sched, pairs, stub, monkeypatch, replay):
    """Exact products in hierarchy mode with exact stage counts (exact counts; tests/hierarchy_exact.py): Multiply1
    calls = packed (closed form) + word products above 64 bits (python-mode oracle), every Multiply1 product's
    BasicMul calls by the closed form or the replay (all, or a sample of ``replay`` products), and every path
    counter of the sweep (tests/path_model.py, plus the Multiply1 products' own counters)."""
    rec = HE.Multiply1Recorder(monkeypatch, stub)
    ctx = Ctx(schedule=sched, products="hierarchy")
    for a, b in pairs:
        assert multiply(a, b, ctx) == a * b, (a.bit_length(), sched.bridge_middle)
    c = ctx.inst.counts
    HE.assert_stage_isolated(c, sched, pairs, rec, stub, replay)
    path = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets()) + HE.lower_stage_counts(rec)
    PM.assert_exact(c, path, PM.PATH_KEYS + ("fastdft.node", "fastdft.leaf"))
    if stub.calls:
        assert stub.verify_real_basic_mul() > 0


@pytest.mark.parametrize("middle", MIDDLES)
def test_small_n_sweep_hierarchy_mode_fast(middle, basic_mul_stub, monkeypatch):
    """The same in products="hierarchy" for K0 <= 4 (fast part; the rest is in the slow suite).  The
    Multiply1 -> BasicMul stage is isolated (a full cascade of a bridge product takes hours in Python) and the
    real BasicMul is verified on every operand-size pair it absorbed.  The replay class of the Multiply1 products
    is replayed on a sample of 8 here (all of it: ~4-7 s per middle)."""
    small = [v for v in sweep_lengths() if root_parameters(v)[2] <= 4]
    pairs = [_operands(n, 1)[0] for n in (small[0], small[len(small) // 2], small[-1])]   # the rest: slow sweep
    _hierarchy_sweep(test_policy(4, middle=middle), pairs, basic_mul_stub, monkeypatch, replay=8)


@pytest.mark.slow
@pytest.mark.parametrize("middle", MIDDLES)
@pytest.mark.parametrize("d", [2, 3, 4, 10])
def test_small_n_sweep_hierarchy_mode(d, middle, basic_mul_stub, monkeypatch):
    """Every root class K0 = 1..6 (its first n) in hierarchy mode, BasicMul stage isolated and verified per
    operand-size pair; exact stage counts, the replay class sampled (16 products per configuration: a full replay of
    the whole sweep costs about as much again as the sweep; the full replays are the slow route tests of
    tests/test_bigint_sites.py).  K0 <= 6 because Multiply1 itself runs on the packed products in Python: one
    stage-isolated product costs ~30 s at K0 = 5 and ~90 s at K0 = 6 and roughly triples per K0 beyond (measured);
    the bridge-dimension rules do not depend on the product mode and are swept to K0 <= 10 in python mode
    (test_small_n_sweep_python_mode_large) and over n = 1..300 by tests/test_regression_allones.py."""
    first: dict[int, int] = {}
    for n in range(1, 400):
        first.setdefault(root_parameters(n)[2], n)
    pairs = [_operands(first[K], d)[0] for K in sorted(first) if K <= 6]
    _hierarchy_sweep(test_policy(d, middle=middle), pairs, basic_mul_stub, monkeypatch, replay=16)


def test_regression_examples():
    """The reported raising configurations, now exact."""
    for d, n in ((4, 20), (4, 40), (10, 1000), (10, 3000), (2, 5), (2, 6), (2, 7), (2, 8)):
        for middle in ("bluestein", "walsh"):
            ctx = Ctx(schedule=test_policy(d, middle=middle))
            a, b = _operands(n, 3)[0]
            assert multiply(a, b, ctx) == a * b, (d, n, middle)


def test_r3_profile_with_lemma16_middles_rejected():
    """The Bluestein and Walsh middles need br_r2's input pre-scaling (SPEC §5.10); a schedule asking
    for them under the r3 profile is rejected up front instead of failing inside the middle."""
    with pytest.raises(ValueError):
        test_policy(4).with_(bridge_constants="r3")


# ---------------------------------------------------------------------------- bit network end to end


@pytest.mark.parametrize("middle", ["bluestein", "walsh"])
def test_bit_network_runs_end_to_end(middle):
    """t = (16, 16) (test_policy(2), K0 = 8): the bridge's Lemma 12 exchanges have width lg 16 = 4,
    so Proposition 11 runs on the bit network B1 inside a real product."""
    ctx = Ctx(schedule=test_policy(2, middle=middle))
    a, b = _operands(1000, 5)[0]
    assert multiply(a, b, ctx) == a * b
    # exact (path_model): 5 exchanges of two 4-bit axes per transform (2 spreading, 3 reversals),
    # each one Prop 11 call at level 1 (one node, s = 10 children)
    exp = PM.multiply_counts(test_policy(2, middle=middle), PM.bit_lengths([(a, b)]), PM.nets())
    keys = ["interchange.prop11_node", "interchange.lemma12_network_call", "interchange.child_call"]
    PM.assert_exact(ctx.inst.counts, exp, keys)
    assert [exp[k] for k in keys] == [2 * 5, 2 * 5, 2 * 5 * 10]


# ---------------------------------------------------------------------------- d_clamped counters


def _closure_421(a_hat: int, L: int, q: int, t: int) -> int:
    """Independent transcription of br_r2 §4.6 (4.21): truncated binary powering at
    Q = q + ceil(lg L) + 2 ceil(lg 4t) + 10, guarded division, one nearest (ties-even) rounding."""
    Q = q + (L - 1).bit_length() + 2 * (4 * t - 1).bit_length() + 10
    x, y, e = a_hat << (Q - q), 1 << Q, L
    while e:
        if e & 1:
            y = (y * x) >> Q
        x, e = (x * x) >> Q, e >> 1
    g = (1 << (2 * Q)) // ((1 << Q) - y)
    sh = Q - q
    hi, rem = g >> sh, g & ((1 << sh) - 1)
    half = 1 << (sh - 1)
    return hi + (rem > half or (rem == half and hi & 1))


def test_closure_default_is_the_421_powering(monkeypatch):
    """closure_gamma's default equals the independent (4.21) transcription, and it never forms the
    L q-bit power: the exact oracle's `pow(a_hat, L)` is shadowed by a guard in the module.  (The two
    methods round to the same value on every input we tried -- (4.21)'s guard leaves only
    vanishingly rare near-ties -- so the method is checked structurally and by the table counters
    below, not by values.)"""
    import subnlogn.tables as tables
    rng = random.Random(421)
    cases = [(rng.randrange(((2 * t - 1) << q) // (2 * t) + 1), L, q, t)
             for q in (20, 40, 62) for t in (4, 16, 64) for L in (2, 8, 512, 1 << 16) for _ in range(3)]
    for a_hat, L, q, t in cases:
        assert tables.closure_gamma(a_hat, L, q, t) == _closure_421(a_hat, L, q, t)

    def guard(base, exp, *mod):
        raise AssertionError("the default closure must not form a^L (br_r2 (4.21))")

    monkeypatch.setattr(tables, "pow", guard, raising=False)
    for a_hat, L, q, t in cases:
        tables.closure_gamma(a_hat, L, q, t)                       # powering: no pow call
    with pytest.raises(AssertionError, match="must not form"):
        tables.closure_gamma(*cases[0][:3], method="exact")      # the oracle does call it


@pytest.mark.parametrize("schedule", [test_schedule(base_threshold=2), test_policy(3)],
                         ids=["2d", "bridge"])
def test_faithful_tables_use_the_powering_closure(schedule):
    """Fresh tables (no shared cache): every closure is computed by (4.21) powering."""
    ctx = Ctx(schedule=schedule)
    a, b = _operands(300, 2)[0]
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    assert c["tables.closure_powering"] > 0 and c.get("tables.closure_exact", 0) == 0


# ---------------------------------------------------------------------------- bridge fallback


def test_kron_product_is_counted_per_product():
    """kron.product counts every packed product (4 per block); for one forced 2D node it equals
    4 t1 ceil(r / W~) per transform."""
    from subnlogn.fastdft2d import fast_dft
    from subnlogn.fixedpoint import FxVec
    sch = test_schedule(base_threshold=None, max_depth=1)
    ctx = Ctx(schedule=sch)
    R, p = 256, 20
    lv = sch.level(R, p)
    rng = random.Random(4)
    lim = (1 << (2 * p + 2)) * 7 // 10           # |x_j| <= 2^p (complex modulus, MS Thm 6.3; 0.7 < 1/sqrt 2)
    x = FxVec([rng.randint(-lim, lim) for _ in range(R)], [rng.randint(-lim, lim) for _ in range(R)], p + 2)
    fast_dft(ctx, x, R, p)
    assert ctx.inst.counts["kron.product"] == 4 * lv.t1 * (-(-lv.r // lv.W_tilde))


# ---------------------------------------------------------------------------- recovery check


def test_recovery_error_asserted_against_the_certified_bound():
    ctx = Ctx(schedule=test_policy(4))
    a, b = _operands(500, 9)[0]
    assert multiply(a, b, ctx) == a * b
    worst, eps = [v for k, v in ctx.inst.notes if k == "multiply.recovery_margin"][-1]
    assert eps == Fraction(319, 12800) and worst <= eps


def test_recovery_check_is_not_tautological(monkeypatch):
    """A transform error far above its contract but still rounding correctly (shift 0.1 < 1/2) must
    trip the certified-recovery assertion."""
    import subnlogn.multiply as mm
    real = mm._transform
    calls = []

    def perturbed(ctx, x, R, p):
        y = real(ctx, x, R, p)
        calls.append(1)
        if len(calls) == 2:                                   # the second transform: z
            im = list(y.im)
            im[0] += 51                                       # 51 / 2^9 ~ 0.1 in units of c_0
            y = type(y)(list(y.re), im, y.q)
        return y

    monkeypatch.setattr(mm, "_transform", perturbed)
    a, b = _operands(200, 1)[0]
    with pytest.raises(AssertionError, match="recovery error"):
        multiply(a, b, Ctx(schedule=test_schedule(base_threshold=2)))
