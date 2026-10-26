"""SPEC_WALSH §8 W-T11 (end-to-end exact products with every middle) and W-T12 (the retuned Prop 14 policy at
d = 13, exact equality with individual kernels + one Q_p); SPEC_WALSH §1, §6, §9."""

import random
from fractions import Fraction

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.m6.cnet import CCtx
from subnlogn.m6.policy import LayerPolicy, batch_plan
from subnlogn.m6.prop14 import hadamard_direct, simultaneous_H0
from subnlogn.multiply import multiply
from subnlogn.schedule import test_schedule
from walsh_helpers import NET_C1

MIDDLES = ("bluestein", "walsh", "direct")


@pytest.mark.parametrize("d", [3, 4])
@pytest.mark.parametrize("layer", ["base", "network"])
def test_end_to_end_products_all_middles(d, layer):
    """W-T11: identical exact products a*b with bridge_middle in {bluestein, walsh, direct}."""
    rng = random.Random(d * 7 + len(layer))
    pairs = [(rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)) for n in (90, 300)]
    pairs += [((1 << 200) - 1, (1 << 200) - 1), (1 << 150, 3)]
    for mid in MIDDLES:
        if mid == "direct" and layer == "network":
            continue
        exp = middle_products_exact(d, mid, layer, pairs)
        if mid == "walsh":
            assert exp["walsh.positional_map"] > 0 and exp["walsh.chunk_round"] > 0 and exp["walsh.slice_batch"] > 0
            assert (exp["m6.c_power.network"] > 0) == (layer == "network")   # slices of D = 3 chunks run C^{t3}


def middle_products_exact(d, mid, layer, pairs):
    """Exact products through test_schedule(bridge_d=d) with the middle ``mid`` and the Prop 14 engine ``layer``,
    and every counter of PM.PATH_KEYS equal to the independent closed form: positional maps, CNOT
    batches, chunk rounds, every Prop 14 layer of every middle call through the network engine with Lemma 13
    basis changes (none through the oracle).  Returns the expected counts."""
    sched = test_schedule(bridge_d=d).with_(bridge_middle=mid, prop14_layer=layer)
    ctx = make_ctx(sched)
    for a, b in pairs:
        assert multiply(a, b, ctx) == a * b
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    return exp


@pytest.mark.parametrize("d,K", [(4, 5), (4, 8), (3, 6)])
def test_bridge_walsh_network_equals_base(d, K):
    """The Walsh middle with the complex-network engine reproduces the base-case engine bit for bit."""
    R, p = 1 << K, max(8, K) + 2
    q = p + 2
    rng = random.Random(d * 11 + K)
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    base = test_schedule(bridge_d=d).with_(bridge_middle="walsh")
    za = bridge_dft(make_ctx(base), FxVec(re, im, q), R, p, d)
    ctx_b = make_ctx(base.with_(prop14_layer="network"))
    zb = bridge_dft(ctx_b, FxVec(re, im, q), R, p, d)
    assert za == zb
    eng = PM.Eng(PM.nets()["C1"], d, base.layer)                  # exact counts
    exp = PM.bridge_transform(K, d, "walsh", 1, movement=False, eng=eng)
    PM.assert_exact(ctx_b.inst.counts, exp, PM.PATH_KEYS)
    assert exp["m6.layer.network"] > 0 and exp["m6.c_power.network"] > 0     # CNOT-batch slices of D = 3 chunks


@pytest.mark.slow
def test_end_to_end_K11_d3():
    """SPEC_WALSH §9.2 shape K_root = 11, d = 3, h = 2 (leftover bit, both prefix kinds, two chunk rounds).
    The bridge orders the axes increasingly, t = (8, 16, 16); SPEC_WALSH lists the equivalent (16, 8, 16),
    which tests/test_walsh_fft.py runs directly."""
    sched = test_schedule(bridge_d=3).with_(bridge_middle="walsh", chunk_bits=2)
    ctx = make_ctx(sched)
    rng = random.Random(11)
    a, b = rng.getrandbits(10000) | (1 << 9999), rng.getrandbits(10000)
    assert multiply(a, b, ctx) == a * b
    exp = PM.multiply_counts(sched, PM.bit_lengths([(a, b)]), PM.nets())
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    assert exp["walsh.leftover_cnot"] > 0 and exp["walsh.prefix_round"] > 0 and exp["walsh.chunk_round"] == 2 * 2
    assert exp["walsh.slice_batch"] > 0 and exp["walsh.positional_map"] == 2 * 2


# ----------------------------------------------------------------------------------------------
# W-T12: retuned Prop 14 policy at d = 13
# ----------------------------------------------------------------------------------------------


def _run_layer(pol, d=13, D=13, p=10, seed=1):
    """One W-T12 layer with a bare CCtx (no row_add): the P_M basis changes use the SPEC §4.3 address-permutation
    oracle, not Lemma 13 (DEVIATIONS D11).  Through Lemma 13: beta = 1/8 in
    tests/test_regression_network.py::test_theorem_batching_beta_one_eighth_d13_through_lemma13, forced_q0 = 4 in
    tests/test_m6_acceptance.py::test_theorem_batching_forced_q0_through_lemma13."""
    rng = random.Random(seed)
    recs = [([rng.randint(-(1 << p) // 2, (1 << p) // 2)], [rng.randint(-(1 << p) // 2, (1 << p) // 2)])
            for _ in range(1 << D)]
    sel = list(range(D))
    eng = CCtx(net=NET_C1, d=d, policy=pol)
    out, sc = simultaneous_H0(recs, sel, p, p, eng, K=1, rho=0)
    ref, _ = hadamard_direct(recs, sel, p, p)
    assert sc == p and out == ref                       # exact equality with individual kernels + one Q_p
    return eng.counts


def test_retuned_policy_beta_one_eighth_d13():
    """beta = 1/8: theorem batching q0 = 6, pieces 3 + 3 + 1, network at e = 3 (13^(1/8) < 3)."""
    pol = LayerPolicy(beta=Fraction(1, 8), mode="test", guard="compiled")
    plan = batch_plan(13, 13, 1, NET_C1, pol)
    assert (plan.q0, plan.pieces) == (6, (3, 3, 1))
    c = _run_layer(pol)
    assert c["c_power.network"] == 2 and c["batch.preprocessed_chunks"] == 6


def test_retuned_policy_forced_q0_d13():
    """Dev-11 forced_q0 = 4 at D = d = 13: one 9-piece, two network levels (1 + s nodes)."""
    pol = LayerPolicy(mode="test", leaf="count", guard="compiled", forced_q0=4)
    assert batch_plan(13, 13, 1, NET_C1, pol).pieces == (9,)
    c = _run_layer(pol)
    assert c["c_power.network"] == 1 + NET_C1.s


def test_printed_beta_half_takes_the_leaf_path_d13():
    """beta = 1/2 at d = 13: every piece has e = 3 < 13^(1/2), so no network call is made."""
    pol = LayerPolicy(beta=Fraction(1, 2), mode="test", guard="compiled")
    c = _run_layer(pol)
    exp = PM.unprefixed(PM.prop14_layer(PM.Eng(NET_C1, 13, pol, row_add="direct"), 13, 13))
    PM.assert_exact(c, exp, ["c_power.network", "c_power.leaf", "c_single", "batch.preprocessed_chunks"])
    assert exp["c_power.network"] == 0 and exp["c_power.leaf"] == 3          # pieces 3 + 3 + 1, all leaves
