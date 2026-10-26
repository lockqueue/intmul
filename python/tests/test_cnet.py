"""M6: C^{tensor e} through the complex network and the network Prop 14 layer, against individual
exact kernels and the base case (bit-exact), with fixture C1 (SPEC §4.5-§4.7, §4.11).

These are unit tests of the network logic: every engine here is a bare ``CCtx`` without ``row_add``, so the P_M
basis changes use the SPEC §4.3 address-permutation oracle, not Lemma 13 (DEVIATIONS D11).  The same layers through
Lemma 13 (``m6.engine.make_engine``): tests/test_m6_acceptance.py, tests/test_regression_network.py."""

import random

import pytest

import path_model as PM
from subnlogn.m6.cnet import CCtx, base_m_pieces, batched_c_layer, c_single, simultaneous_H0_network
from subnlogn.m6.policy import LAYER_TEST, LayerPolicy, compiled_delta
from subnlogn.m6.prop14 import simultaneous_H0_base
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_C1, fixture_C2


def _rand(rng, n, r, lim):
    return [([rng.randint(-lim, lim) for _ in range(r)], [rng.randint(-lim, lim) for _ in range(r)])
            for _ in range(n)]


def test_base_m_pieces():
    assert base_m_pieces(9, 3) == [9]
    assert base_m_pieces(4, 3) == [3, 1]
    assert base_m_pieces(19, 3) == [9, 9, 1]
    assert base_m_pieces(0, 3) == []


@pytest.mark.parametrize("fixture", [fixture_C1, fixture_C2])
@pytest.mark.parametrize("D,nb,K,rho,lo", [(3, 3, 1, 0, 0), (3, 5, 1, 0, 1), (4, 4, 1, 0, 0),
                                           (9, 9, 1, 0, 0), (3, 7, 2, 1, 1), (3, 6, 2, 0, 0)])
def test_batched_c_layer_equals_individual_kernels(fixture, D, nb, K, rho, lo):
    """C^{tD} through the network (forced batching, Dev-4) == D individual exact C kernels, on
    every row including the scratch roles' rows with arbitrary values; D consecutive K-bit chunks
    with offset rho above a suffix of lo bits and below a prefix."""
    net = compile_network(fixture())
    rng = random.Random(D * 100 + nb + 7 * K + rho)
    r = 2
    delta = compiled_delta(net, D, 2, K, LAYER_TEST)
    lim = 1 << 20
    recs = [([v << delta for v in re], [v << delta for v in im])
            for re, im in _rand(rng, 1 << nb, r, lim)]
    sel = [lo + rho + i * K for i in range(D)]
    ctx = CCtx(net=net, d=2, K=K, rho=rho)
    got = batched_c_layer(list(recs), sel, ctx)
    ref = list(recs)
    for b in sel:
        c_single(ref, b)
    assert got == ref
    # exact counts (exact count; path_model): network nodes, phase edges, row additions (the address-permutation
    # oracle of this unit test), padded/removed rows, leaves and kernels
    exp = PM.unprefixed(PM.prop14_layer(PM.Eng(net, 2, LAYER_TEST, K, row_add="direct"), D, nb))
    del exp["layer.network"]
    PM.assert_exact(ctx.counts, exp, sorted(set(exp) | {"c_power.network", "rows.padded", "rows.removed"}))
    assert (exp["c_power.network"] > 0) == (D >= net.m) and (exp["rows.padded"] > 0) == (D >= net.m)


def test_nonconsecutive_chunks_rejected():
    net = compile_network(fixture_C1())
    with pytest.raises(ValueError):
        batched_c_layer([([0], [0])] * 16, [0, 2, 3], CCtx(net=net, d=2))


@pytest.mark.parametrize("D,nb,lo", [(3, 3, 0), (3, 4, 1), (4, 5, 0), (9, 9, 0), (5, 6, 1)])
def test_network_prop14_equals_base_case(D, nb, lo):
    """Prop 14 via the network == base case, bit for bit (SPEC §4.11)."""
    net = compile_network(fixture_C1())
    rng = random.Random(7 * D + nb)
    p = 16
    recs = _rand(rng, 1 << nb, 2, (1 << p) * 7 // 10)
    sel = list(range(lo, lo + D))
    eng = CCtx(net=net, d=2)
    a = simultaneous_H0_network(recs, sel, p, p, eng)
    b = simultaneous_H0_base(recs, sel, p, p)
    assert a == b
    exp = PM.unprefixed(PM.prop14_layer(PM.Eng(net, 2, LAYER_TEST, 1, row_add="direct"), D, nb))   # exact
    PM.assert_exact(eng.counts, exp, sorted(set(exp) | {"c_power.network", "row_add.direct"}))
    assert exp["layer.network"] == 1 and exp["c_power.network"] == (14 if D == 9 else 1)    # 1 + s at D = 9


@pytest.mark.parametrize("d,D,pol", [
    (20, 19, None),                                    # SPEC §4.10 faithful batching (slow-sized: skip)
    (5, 4, LayerPolicy(mode="test", guard="compiled")),          # D <= q0: individual kernels
    (13, 13, LayerPolicy(mode="test", leaf="count", guard="compiled", forced_q0=4)),  # Dev-11: 9-piece
])
def test_theorem_batching_equals_base_case(d, D, pol):
    """Theorem batching (q0 preprocessing, joined row field padded to W^k0, base-m pieces) gives the
    base case bit for bit; the padded rows are asserted zero and removed.  P_M by the address-permutation oracle
    (module docstring); the d = 13, forced_q0 = 4 layer through Lemma 13 is
    tests/test_m6_acceptance.py::test_theorem_batching_forced_q0_through_lemma13."""
    if pol is None:
        pytest.skip("d = 20 runs in the slow suite (test_m6_slow.py)")
    net = compile_network(fixture_C1())
    rng = random.Random(d + D)
    p = 12
    nb = D
    recs = _rand(rng, 1 << nb, 1, (1 << p) * 7 // 10)
    sel = list(range(D))
    ctx = CCtx(net=net, d=d, policy=pol)
    a = simultaneous_H0_network(recs, sel, p, p, ctx)
    b = simultaneous_H0_base(recs, sel, p, p)
    assert a == b
    exp = PM.unprefixed(PM.prop14_layer(PM.Eng(net, d, pol, 1, row_add="direct"), D, nb))   # exact
    PM.assert_exact(ctx.counts, exp, sorted(set(exp) | {"c_power.network", "batch.individual", "rows.padded"}))
    if pol.forced_q0 is not None:
        assert exp["c_power.network"] == 1 + net.s and exp["rows.padded"] == (18 - 16) << (D - 4)
    else:
        assert exp["batch.individual"] == 1 and exp["c_power.network"] == 0
