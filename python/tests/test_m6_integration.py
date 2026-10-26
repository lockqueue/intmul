"""M6 integration (SPEC §5.11): the Bluestein middle with the complex-network Prop 14 layer must
reproduce the M3 (base-case layer) outputs BIT FOR BIT; products stay exact."""

import random

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.fixedpoint import FxVec
from subnlogn.multiply import multiply
from subnlogn.schedule import test_schedule


@pytest.mark.parametrize("d,K", [(4, 5), (4, 8), (3, 6)])
def test_network_layer_reproduces_m3_bit_for_bit(d, K):
    R = 1 << K
    p = max(8, K) + 2
    rng = random.Random(d * 11 + K)
    q = p + 2
    big = (1 << (q + p)) * 7 // 10
    re = [rng.randint(-big, big) for _ in range(R)]
    im = [rng.randint(-big, big) for _ in range(R)]
    base = test_schedule(bridge_d=d).with_(bridge_middle="bluestein", bridge_movement="lemma12")
    ctx_a = make_ctx(base)
    ctx_b = make_ctx(base.with_(prop14_layer="network"))
    za = bridge_dft(ctx_a, FxVec(re, im, q), R, p, d)
    zb = bridge_dft(ctx_b, FxVec(re, im, q), R, p, d)
    assert za == zb
    # exact counts: every Prop 14 layer of the middle through the network, each P_M row addition
    # one Lemma 13 call (none through the oracle), the three layouts L / L^-1 executed by Lemma 3 moves + Lemma 12
    nets = PM.nets()
    exp = PM.bridge_transform(K, d, "bluestein", 1, movement=True, eng=PM.Eng(nets["C1"], d, base.layer, 1, nets["B1"]),
                              bitnet=nets["B1"])
    PM.assert_exact(ctx_b.inst.counts, exp, PM.PATH_KEYS)
    assert exp["layout.executed"] == 3 and exp["prop14.network_layer"] > 0
    assert (exp["lemma13.call"] > 0) == (d - 1 >= 3)


def test_multiply_with_network_layer():
    sched = test_schedule(bridge_d=4).with_(bridge_middle="bluestein", prop14_layer="network")
    ctx = make_ctx(sched)
    rng = random.Random(4)
    pairs = []
    for n in (90, 300):
        a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b
        pairs.append((a, b))
    exp = PM.multiply_counts(sched, PM.bit_lengths(pairs), PM.nets())       # exact counts
    PM.assert_exact(ctx.inst.counts, exp, PM.PATH_KEYS)
    assert exp["m6.c_power.network"] > 0 and exp["lemma13.call"] > 0 and exp["m6.row_add.direct"] == 0
