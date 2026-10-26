"""Packed-product mode: products="python" counts every packed
product computed by Python's * ("python.big_product"); products="hierarchy" routes them through the
independent multiplier hierarchy (SPEC §6.5) and asserts the counter stays 0."""

import random

import pytest

import hierarchy_exact as HE
import path_model as PM
from subnlogn.context import WORD_BITS, Ctx
from subnlogn.hierarchy import Hierarchy
from subnlogn.multiply import multiply
from subnlogn.schedule import faithful_schedule, test_policy, test_schedule


def test_python_mode_counts_packed_products_2d():
    ctx = Ctx(schedule=test_schedule(base_threshold=2))
    rng = random.Random(1)
    a, b = rng.getrandbits(300), rng.getrandbits(300)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    exp = PM.multiply_counts(ctx.schedule, PM.bit_lengths([(a, b)]))     # exact packed products (path_model)
    PM.assert_exact(c, exp, ["kron.product", "fastdft.node", "fastdft.leaf", "spread.row"])
    assert 0 < c["python.big_product"] <= exp["kron.product"]           # beyond word scale: data-dependent subset


def test_python_mode_counts_ring_and_spread_products_bridge():
    ctx = Ctx(schedule=test_policy(4))
    rng = random.Random(2)
    a, b = rng.getrandbits(100), rng.getrandbits(100)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    exp = PM.multiply_counts(ctx.schedule, PM.bit_lengths([(a, b)]), PM.nets())   # exact
    PM.assert_exact(c, exp, ["kron.product", "prop18.ring_product", "bridge.dft"])
    assert 0 < c["python.big_product"] <= exp["kron.product"] + 4 * exp["prop18.ring_product"]


def _deep2d_hierarchy_product(monkeypatch, stub=None, seed: int = 3):
    """The deep-2D hierarchy product with EXACT stage counts (exact counts; tests/hierarchy_exact.py):
    hierarchy.multiply1 = 96 packed products (closed form) + 899 word products above 64 bits (python-mode oracle);
    every Multiply1 product's BasicMul calls by the closed form (967 products: a leaf with q_b <= 63, none) or the
    python-mode replay (the 28 packed products of 577..1023 bits: q_b = 64, 1528 = 6 R0 - 8 each), 42,784 in all."""
    rec = HE.Multiply1Recorder(monkeypatch, stub)
    rng = random.Random(seed)
    a, b = rng.getrandbits(24) | (1 << 23), rng.getrandbits(24) | 1
    sched = test_schedule(base_threshold=2)
    ctx = Ctx(schedule=sched, products="hierarchy")
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    exp, res = HE.assert_stage_isolated(c, sched, [(a, b)], rec, stub)
    assert (exp["kron.product"], exp["oracle.word_over_64"], res["replayed"], res["total"]) == (96, 899, 28, 42784)
    return c, rec


def test_hierarchy_mode_2d_has_no_python_big_products(basic_mul_stub, monkeypatch):
    """2D with forced recursion in hierarchy mode: packed products and word-scale products with an operand
    above 64 bits go to Multiply1, counted exactly.  The Multiply1 -> BasicMul stage is isolated
    here (the full cascade, ~30 s, is the slow test below) and the real BasicMul is verified per size pair."""
    _deep2d_hierarchy_product(monkeypatch, basic_mul_stub)
    assert basic_mul_stub.calls == 42784 and basic_mul_stub.verify_real_basic_mul() > 0


def test_hierarchy_mode_faithful_full_cascade(monkeypatch):
    """Faithful 2D (a single leaf at 600 bits) in FULL hierarchy mode, no stub: the leaf butterfly and
    root products with an operand above 64 bits go to Multiply1 (MS Thm 7.1 part 3 (b))."""
    rec = HE.Multiply1Recorder(monkeypatch)
    rng = random.Random(8)
    a, b = rng.getrandbits(600) | (1 << 599), rng.getrandbits(600) | 1
    ctx = Ctx(schedule=faithful_schedule(), products="hierarchy")
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    # exact: 1528 Multiply1 calls (no packed product; the python-mode oracle, = 6 R0 - 8 for
    # R0 = 256, q_b = 64), each on <= 65-bit operands whose leaf has q_b = 49 <= 63: no BasicMul call at all
    exp, res = HE.assert_stage_isolated(c, faithful_schedule(), [(a, b)], rec)
    assert (exp["next"], res["closed"], res["replayed"], c.get("hierarchy.basic", 0)) == (1528, 1528, 0, 0)


@pytest.mark.slow
def test_hierarchy_mode_2d_full_cascade(monkeypatch):
    """The deep-2D product above in FULL hierarchy mode, no stub (~30 s): packed products to Multiply1,
    whose butterfly products above 64 bits go to the real BasicMul -- 42,784 calls, derived above by the closed
    form and the replay -- and every BasicMul call runs its own two base FFTs: the aggregate
    FFT counters of the three stages equal the 2D model + one leaf root per Multiply1 and per BasicMul call."""
    sizes = []
    inner = Hierarchy.basic_mul

    def sizing(h, x, y):
        sizes.append(max(abs(x).bit_length(), abs(y).bit_length(), 1))
        return inner(h, x, y)
    monkeypatch.setattr(Hierarchy, "basic_mul", sizing)
    c, rec = _deep2d_hierarchy_product(monkeypatch)
    assert c["hierarchy.basic"] == len(sizes) == 42784
    m1 = [max(abs(x).bit_length(), abs(y).bit_length(), 1) for x, y, _, _ in rec.calls]
    top = PM.multiply_counts(test_schedule(base_threshold=2), [24])
    leaves = [PM.root_K0(n) for n in m1 + sizes if n > 64]          # one leaf root per routed product
    # word products: the top 2D model + each Multiply1 product's + each BasicMul call's
    words = top["word.call"] + sum(PM.multiply_counts(s, [n])["word.call"] for (_, _, _, s), n in zip(rec.calls, m1))
    words += sum(PM.basic_mul_counts(1 << (n - 1), 1)["word.call"] for n in sizes)
    PM.assert_exact(c, {"multiply.call": 1 + len(leaves), "fastdft.node": top["fastdft.node"],
                        "fastdft.leaf": top["fastdft.leaf"] + 2 * len(leaves),
                        "basefft.butterfly": top["basefft.butterfly"] + sum(K << K for K in leaves),
                        "multiply.fallback_2d": 2 + 2 * len(leaves), "word.call": words})


def test_multiply_api_schedule_and_products():
    rng = random.Random(4)
    a, b = rng.getrandbits(300), rng.getrandbits(300)
    assert multiply(a, b, schedule=faithful_schedule(), products="hierarchy") == a * b
    a, b = rng.getrandbits(150), rng.getrandbits(150)
    assert multiply(a, b) == a * b                                  # faithful, python mode
    with pytest.raises(ValueError):
        multiply(a, b, Ctx(), schedule=faithful_schedule())
    with pytest.raises(ValueError):
        Ctx(products="gmp")


def test_word_scale_rule():
    ctx = Ctx()
    mul = ctx.product_mul(100)
    big, word = (1 << 1000) + 1, (1 << WORD_BITS) - 1
    assert mul(big, word) == big * word and ctx.inst.counts.get("python.big_product", 0) == 0
    assert mul(1 << 300, 1 << 300) == 1 << 600 and ctx.inst.counts.get("python.big_product", 0) == 0
    assert mul(big, big) == big * big and ctx.inst.counts["python.big_product"] == 1


def test_hierarchy_mode_assertion_catches_python_products(monkeypatch):
    """If a packed product bypassed the hierarchy, multiply() in hierarchy mode must fail."""
    ctx = Ctx(schedule=test_schedule(base_threshold=2), products="hierarchy")
    ctx.imul = None                                     # simulate a bypass: Python * again
    rng = random.Random(5)
    with pytest.raises(AssertionError, match="hierarchy mode"):
        multiply(rng.getrandbits(200), rng.getrandbits(200), ctx)


@pytest.mark.slow
def test_hierarchy_mode_bridge_bluestein(basic_mul_stub, monkeypatch):
    """Bridge + Bluestein in hierarchy mode with the Multiply1 -> BasicMul stage isolated (a full cascade
    takes hours in Python); the real BasicMul is verified on every operand-size pair the stub absorbed.  Exact
    stage counts: Multiply1 calls = packed + oracle word products, every Multiply1 product's
    BasicMul calls by the closed form or the replay, and the bridge's own path counters (path_model)."""
    rec = HE.Multiply1Recorder(monkeypatch, basic_mul_stub)
    sched = test_policy(4)
    ctx = Ctx(schedule=sched, products="hierarchy")
    rng = random.Random(6)
    a, b = rng.getrandbits(100), rng.getrandbits(100)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    HE.assert_stage_isolated(c, sched, [(a, b)], rec, basic_mul_stub)
    path = PM.multiply_counts(sched, PM.bit_lengths([(a, b)]), PM.nets()) + HE.lower_stage_counts(rec)
    PM.assert_exact(c, path, PM.PATH_KEYS)
    assert basic_mul_stub.verify_real_basic_mul() > 0
