"""M7: theorem shape and cutoff (SPEC §6.1-§6.2), the faithful dispatcher, the test policy and the
independent multiplier hierarchy with its recursion guard (SPEC §6.5)."""

import random
from collections import Counter
from fractions import Fraction

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import hierarchy_exact as HE
import path_model as PM
from conftest import make_ctx
from subnlogn.context import Ctx
from subnlogn.hierarchy import Hierarchy, basic_schedule, hierarchy_ctx
from subnlogn.m6.policy import LAYER_TEST, LayerPolicy
from subnlogn.multiply import multiply
from subnlogn.schedule import faithful_schedule, test_policy, test_schedule
from subnlogn.theorem import (THEOREM_CONSTANTS, cutoff_certificate, floor_rational_power, pow_le,
                              theorem_mode_shape, theorem_shape)


@given(st.integers(1, 40), st.integers(0, 40), st.integers(0, 10 ** 30))
@settings(max_examples=300, deadline=None)
def test_pow_le_matches_direct(base, exp, bound):
    assert pow_le(base, exp, bound) == (base ** exp <= bound)


@given(st.integers(1, 10 ** 12), st.integers(1, 7), st.integers(1, 7))
@settings(max_examples=200, deadline=None)
def test_floor_rational_power_brute(K, a, b):
    eps = Fraction(min(a, b), max(a, b))
    d = floor_rational_power(K, eps)
    A, B = eps.numerator, eps.denominator
    assert d ** B <= K ** A < (d + 1) ** B


def test_theorem_shape_never_at_feasible_sizes():
    """d >= 2 needs K_root >= 2^(2^75): None for every representable root (SPEC §6.1)."""
    assert THEOREM_CONSTANTS["eps"] == Fraction(1, 2 ** 75)
    for K in (5, 64, 10 ** 6, 2 ** 4096):
        assert theorem_shape(K) is None and theorem_mode_shape(K) is None
    assert cutoff_certificate() is None


def test_theorem_shape_formula_with_other_rows():
    s = theorem_shape(11, eps=Fraction(1, 2), c=Fraction(1, 2))
    assert (s.d, s.ell, s.r, s.t, s.chunk_bits) == (3, 4, 16, (8, 16, 16), 1)
    s = theorem_shape(2 ** 21, eps=Fraction(1, 21), c=Fraction(1, 2 ** 44))   # Walsh row 47: d = 2
    assert s.d == 2 and s.t == (1 << 2 ** 20,) * 2 and s.chunk_bits == 1


def test_faithful_dispatcher_theorem_branch_plumbing(monkeypatch):
    """Force the (unreachable) theorem branch at a tiny size to check its plumbing: bridge with the
    shape's d, Bluestein middle, network engine under the schedule's layer policy (a test-mode
    policy here, since the published guard is not executable) and the SPEC §2.5 test fixtures
    C1 / B1 in place of the faithful schedule's real h = 100 networks (never executable)."""
    import subnlogn.multiply as mm
    monkeypatch.setattr(mm, "theorem_mode_shape",
                        lambda K, row: theorem_shape(K, eps=Fraction(1, 2), c=Fraction(1, 2)))
    sched = faithful_schedule().with_(layer=LayerPolicy(mode="test", guard="compiled"),
                                      mul_direct_bits=0, net_cx="C1", net_bit="B1")
    ctx = make_ctx(sched)
    rng = random.Random(5)
    a, b = rng.getrandbits(96), rng.getrandbits(96)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    assert c["multiply.theorem_mode"] == 2 and c["bridge.dft"] == 2
    # exact counts (exact count; path_model): the shape's bridge with the Bluestein middle, every Prop 14 layer
    # through the network engine under the schedule's (theorem-batching) policy, Lemma 3/12 movements
    K0 = PM.root_K0(PM.bit_lengths([(a, b)])[0])
    shape = theorem_shape(K0, eps=Fraction(1, 2), c=Fraction(1, 2))
    nets = PM.nets()
    one = PM.bridge_transform(K0, shape.d, "bluestein", shape.chunk_bits, movement=True,
                              eng=PM.Eng(nets["C1"], shape.d, sched.layer, shape.chunk_bits, nets["B1"]),
                              bitnet=nets["B1"])
    root = Counter({"multiply.call": 1, "word.call": 3 << K0})          # the root's R0 pointwise squares (csquare)
    PM.assert_exact(c, Counter({k: 2 * v for k, v in one.items()}) + root, PM.PATH_KEYS)
    assert one["prop14.network_layer"] > 0 and one["layout.executed"] == 3      # theorem mode moves by Lemma 3/12


def test_test_policy_fields():
    s = test_policy(4)
    assert (s.bridge_d, s.bridge_middle, s.prop14_layer, s.layer, s.net_cx, s.net_bit) == \
        (4, "bluestein", "network", LAYER_TEST, "C1", "B1")
    assert (s.lemma12_min_e, s.lemma12_min_u, s.chunk_bits, s.mul_direct_bits) == (2, 1, 1, 0)
    assert test_policy(3, direct_layers=True, middle="direct").prop14_layer == "base"


def test_basic_mul_is_a_single_base_fft():
    h = Hierarchy()
    rng = random.Random(1)
    pairs = [(rng.getrandbits(n), rng.getrandbits(n)) for n in (65, 300, 2000)]
    for a, b in pairs:
        assert h.basic_mul(a, b) == a * b
    c = h.inst.counts
    assert c["hierarchy.basic"] == 3 and c.get("kron.product", 0) == 0 and c.get("fastdft.node", 0) == 0
    assert basic_schedule().max_depth == 0
    # BasicMul's internal FFT counters, exact (mutant A35 must fail): per call one two-call root, two base
    # radix-2 FFTs of K0 R0/2 butterflies each (path_model.basic_mul_counts; 160 + 896 + 4608 = 5664 here)
    exp = sum((PM.basic_mul_counts(a, b) for a, b in pairs), Counter())
    PM.assert_exact(c, exp, sorted(set(exp) | set(PM.BASIC_ZERO_KEYS)))
    assert exp["multiply.call"] == 3 and exp["fastdft.leaf"] == 6 and exp["basefft.butterfly"] == 5664


def test_multiply1_sends_packed_products_to_basic_mul(monkeypatch):
    """Multiply1 (one forced 2D node) in FULL cascade: its 32 packed products (closed form) and its 1236 word
    products above 64 bits (python-mode oracle) are exactly its 1268 BasicMul calls, and every BasicMul call runs
    one two-call root with two base FFTs: the aggregate counters are Multiply1's 2D model plus one leaf root per
    routed product."""
    sizes = []
    inner = Hierarchy.basic_mul

    def sizing(h, x, y):
        sizes.append(max(abs(x).bit_length(), abs(y).bit_length(), 1))
        return inner(h, x, y)
    monkeypatch.setattr(Hierarchy, "basic_mul", sizing)
    h = Hierarchy(stage_schedule=test_schedule(base_threshold=None, max_depth=1))
    rng = random.Random(2)
    a, b = rng.getrandbits(70), rng.getrandbits(70)
    assert h.multiply1(a, b) == a * b
    c = h.inst.counts
    exp = HE.stage_expected(h.multiply1_schedule, [(a, b)])
    assert (exp["kron.product"], exp["next"]) == (32, 1268)
    PM.assert_exact(c, {"hierarchy.basic": exp["next"], "kron.product": exp["kron.product"],
                        "hierarchy.word_product": exp["oracle.word_over_64"], "python.big_product": 0})
    m1 = PM.multiply_counts(h.multiply1_schedule, PM.bit_lengths([(a, b)]))
    leaves = [PM.root_K0(n) for n in sizes if n > 64]
    assert len(sizes) == exp["next"]
    words = m1["word.call"] + sum(PM.basic_mul_counts(1 << (n - 1), 1)["word.call"] for n in sizes)
    PM.assert_exact(c, {"multiply.call": 1 + len(leaves), "fastdft.node": m1["fastdft.node"],
                        "fastdft.leaf": m1["fastdft.leaf"] + 2 * len(leaves),
                        "basefft.butterfly": m1["basefft.butterfly"] + sum(K << K for K in leaves),
                        "multiply.fallback_2d": 2 + 2 * len(leaves), "word.call": words})


def test_recursion_guard():
    """No call from the hierarchy may reach the improved multiplier (SPEC §6.5)."""
    with pytest.raises(ValueError):
        Hierarchy(stage_schedule=test_schedule(bridge_d=3))
    ctx = Ctx(schedule=test_policy(4), hierarchy_level="multiply1")
    with pytest.raises(AssertionError, match="recursion guard"):
        multiply(3 ** 70, 5 ** 50, ctx)


def test_hierarchy_ctx_faithful_whole_call_fallback(monkeypatch):
    """hierarchy_ctx(): the faithful dispatcher's 2D fallback with packed products by Multiply1 is
    Multiply2 (SPEC §6.5); exact at small sizes (leaf transforms: no packed products).  Exact counts: 1528
    Multiply1 calls (the python-mode oracle; none at 100 bits), none of them reaching BasicMul (leaf
    with q_b <= 63), and the faithful dispatcher's 2D fallback twice per multiply at every stage."""
    rec = HE.Multiply1Recorder(monkeypatch)
    ctx = hierarchy_ctx()
    rng = random.Random(3)
    pairs = []
    for n in (100, 600):
        a, b = rng.getrandbits(n), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b
        pairs.append((a, b))
    c = ctx.inst.counts
    exp, res = HE.assert_stage_isolated(c, ctx.schedule, pairs, rec)
    routed = sum(1 for x, y, _, _ in rec.calls if PM.bit_lengths([(x, y)])[0] > 64)
    PM.assert_exact(c, {"multiply.fallback_2d": 2 * len(pairs) + 2 * routed, "hierarchy.basic": 0})
    assert (exp["next"], routed, res["closed"]) == (1528, 1528, 1528)


@pytest.mark.slow
def test_improved_multiplier_with_hierarchy(basic_mul_stub, monkeypatch):
    """Bridge + Bluestein + network engine with Lemma 17 products, the bridge's packed overlap-add and
    the word-scale products sent to Multiply1 (faithful 2D stage); Multiply1 -> BasicMul isolated and
    the real BasicMul verified per operand-size pair (runtime cost)."""
    rec = HE.Multiply1Recorder(monkeypatch, basic_mul_stub)
    ctx = hierarchy_ctx(test_policy(4))
    rng = random.Random(4)
    a, b = rng.getrandbits(100), rng.getrandbits(100)
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    # exact; the replay class is sampled (8 products): the same shape is replayed in full by
    # tests/test_products.py::test_hierarchy_mode_bridge_bluestein
    exp, _ = HE.assert_stage_isolated(c, test_policy(4), [(a, b)], rec, basic_mul_stub, replay=8)
    path = PM.multiply_counts(test_policy(4), PM.bit_lengths([(a, b)]), PM.nets()) + HE.lower_stage_counts(rec)
    PM.assert_exact(c, path, PM.PATH_KEYS)
    assert exp["prop18.ring_product"] > 0 and path["m6.c_power.network"] > 0
    assert basic_mul_stub.verify_real_basic_mul() > 0


def test_multiply2_sends_packed_products_to_multiply1(basic_mul_stub, monkeypatch):
    """Multiply2 (recursing once, forced stopping rule) sends its packed and word-scale products to
    Multiply1 (faithful 2D: a leaf at these sizes); the Multiply1 -> BasicMul link is tested above.  The
    BasicMul stage is isolated here (each Multiply1 call on the thousands-of-bits packed operands makes
    thousands of BasicMul calls) and verified per operand-size pair."""
    rec = HE.Multiply1Recorder(monkeypatch, basic_mul_stub)
    h = Hierarchy(stage_schedule=test_schedule(base_threshold=None, max_depth=1),
                  multiply1_schedule=faithful_schedule())
    rng = random.Random(6)
    a, b = rng.getrandbits(70), rng.getrandbits(70)
    assert h.multiply2(a, b) == a * b
    c = h.inst.counts
    assert c["hierarchy.multiply2"] == 1
    # exact: Multiply2's 32 packed + 1236 word products above 64 bits are its Multiply1 calls; the
    # faithful Multiply1 products make their BasicMul calls by the closed form or the replay (28 products: q_b = 64)
    exp, res = HE.assert_stage_isolated(c, h.stage_schedule, [(a, b)], rec, basic_mul_stub)
    assert (exp["next"], res["replayed"], basic_mul_stub.calls) == (1268, 28, 437568)
    assert basic_mul_stub.verify_real_basic_mul() > 0
