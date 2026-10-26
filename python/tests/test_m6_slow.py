"""M6 slow suite: faithful theorem batching at d = 20 (SPEC §4.10) and the bridge shapes of SPEC §6.3
that exercise two network levels (d = 10) and Dev-2 chunks (K = 2) through the network engine;
every result bit-identical to the base-case layer."""

import random

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.m6.cnet import CCtx, simultaneous_H0_network
from subnlogn.m6.policy import LayerPolicy
from subnlogn.m6.prop14 import simultaneous_H0_base
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_C1
from subnlogn.schedule import test_schedule

pytestmark = pytest.mark.slow


def test_faithful_batching_d20():
    """d = 20, D = 19, K = 1 with the printed beta = 1/2 and theorem batching (no Dev-4): q0 = 8
    preprocessed chunks joined into 256 rows padded to 270 (k0 = 3), pieces 9 + 1 + 1, the 9-piece an
    internal node with leaf children (9 >= sqrt(20) > 3).  r = 1, small p.

    The engine is a bare CCtx (no row_add): the P_M basis changes use the SPEC §4.3 address-permutation oracle,
    not Lemma 13.  The same layer through Lemma 13 (make_engine, swaps on B1) was measured once: bit-identical,
    381 s for the layer (60 Lemma 13 calls with f = 3, K = 1 on role arrays of 184,320 records, B total under
    (23)) plus 54 s for the base case, 773 MB, above the slow-suite budget; theorem batching through Lemma 13 runs
    at d = 13 instead (tests/test_regression_network.py, tests/test_m6_acceptance.py)."""
    net = compile_network(fixture_C1())
    D, p = 19, 10
    rng = random.Random(2019)
    lim = (1 << p) * 7 // 10
    recs = [([rng.randint(-lim, lim)], [rng.randint(-lim, lim)]) for _ in range(1 << D)]
    sel = list(range(D))
    ctx = CCtx(net=net, d=20, policy=LayerPolicy(mode="test", guard="compiled"))
    got = simultaneous_H0_network(recs, sel, p, p, ctx)
    ref = simultaneous_H0_base(recs, sel, p, p)
    assert got == ref
    c = ctx.counts
    assert c["batch.preprocessed_chunks"] == 8
    assert c["rows.padded"] == c["rows.removed"] == (270 - 256) * (1 << 11)
    assert c["c_power.network"] == 1                    # the 9-piece; its 13 children are leaves
    assert c["c_power.leaf"] == 13 + 2                  # 13 residual children + the two 1-pieces


def _bridge_pair(d, K, chunk_bits=1, seed=0):
    R = 1 << K
    p = max(8, K) + 2
    q = p + 2
    rng = random.Random(seed)
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    base = test_schedule(bridge_d=d).with_(bridge_middle="bluestein", chunk_bits=chunk_bits)
    ctx_a = make_ctx(base)
    ctx_b = make_ctx(base.with_(prop14_layer="network"))
    za = bridge_dft(ctx_a, FxVec(re, im, q), R, p, d)
    zb = bridge_dft(ctx_b, FxVec(re, im, q), R, p, d)
    return za, zb, ctx_b


def test_bridge_two_network_levels_d10():
    """SPEC §6.3 shape K_root = 11, d = 10, t = (2,...,2,4): layer D = 9, forced batching, one 9-piece
    through two network levels; network layer == base layer bit for bit."""
    za, zb, ctx = _bridge_pair(10, 11, seed=10)
    assert za == zb
    exp = _exact(ctx, 11, 10, 1)
    assert exp["m6.c_power.network"] == 3 * 1 * (1 + 13)       # 3 procedures x 1 chunk round x (top + 13 children)
    assert exp["lemma13.swap"] > 0                            # f = 3 slots at the top node: exchanges, rotations


def test_bridge_dev2_chunks_K2():
    """SPEC §6.3 shape K_root = 12, d = 4, t = (8, 8, 8, 8), chunk_bits = 2 (Dev-2): selected bits at
    offsets rho = 0, 1 of 2-bit chunks; network layer == base layer bit for bit."""
    za, zb, ctx = _bridge_pair(4, 12, chunk_bits=2, seed=12)
    assert za == zb
    exp = _exact(ctx, 12, 4, 2)
    assert exp["m6.c_power.network"] == 3 * 2 and exp["lemma13.call"] > 0    # q K = 2 chunk rounds per procedure


def _exact(ctx, K, d, chunk_bits):
    """Exact counts of the network bridge (exact count; path_model): every Prop 14 layer of the Bluestein middle
    through the network engine (C1, Lemma 13 with Lemma 12 exchanges on B1), none through the oracle."""
    nets = PM.nets()
    exp = PM.bridge_transform(K, d, "bluestein", chunk_bits, movement=False,
                              eng=PM.Eng(nets["C1"], d, ctx.schedule.layer, chunk_bits, nets["B1"]))
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    return exp
