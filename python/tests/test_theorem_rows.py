"""Theorem parameter rows (SPEC §6.1 printed row; SPEC_WALSH §1.3 Walsh rows), the Walsh policy presets (SPEC_WALSH
§1.4) and the faithful Walsh schedules (SPEC_WALSH §9.1): exact margins, theorem_shape thresholds, the dispatcher's
fallback, and the row-driven theorem branch."""

import random
from fractions import Fraction

import pytest

from conftest import make_ctx
from subnlogn.m6.policy import LAYER_THEOREM, LAYER_WALSH_46, LAYER_WALSH_47, LayerPolicy
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import Schedule, faithful_schedule
from subnlogn.theorem import (ROW_PRINTED, ROW_WALSH_46, ROW_WALSH_47, THEOREM_CONSTANTS, THEOREM_ROWS, XI,
                              theorem_mode_shape, theorem_shape)

ROWS = (ROW_PRINTED, ROW_WALSH_47, ROW_WALSH_46)


def test_rows_are_the_spec_tables():
    """SPEC §6.1 (printed) and the SPEC_WALSH §1.3 table, entry by entry (xi = 2^-42)."""
    assert XI == Fraction(1, 2 ** 42) and THEOREM_ROWS == {r.name: r for r in ROWS}
    p = ROW_PRINTED
    assert (p.middle, p.eps, p.c, p.beta, p.C1, p.delta) == \
        ("bluestein", Fraction(1, 2 ** 75), Fraction(1, 2 ** 56), Fraction(1, 2), 20, Fraction(1, 16))
    assert (p.tau, p.sigma, p.lam, p.lam_p, p.kappa) == (1 - Fraction(1, 2 ** 50), 1 - Fraction(1, 2 ** 50),
                                                         1 - Fraction(1, 2 ** 52), 1 - Fraction(1, 2 ** 54),
                                                         Fraction(1, 2 ** 182))
    assert {k: v for k, v in THEOREM_CONSTANTS.items()} == {
        "beta": p.beta, "delta": p.delta, "tau": p.tau, "sigma": p.sigma, "c": p.c, "lambda": p.lam,
        "lambda_p": p.lam_p, "eps": p.eps, "C1": p.C1, "kappa": p.kappa}
    w, v = ROW_WALSH_47, ROW_WALSH_46
    assert (w.middle, w.C1, w.eps, w.beta, w.c) == ("walsh", 20, Fraction(1, 21), Fraction(1, 8), Fraction(1, 2 ** 44))
    assert (v.middle, v.C1, v.eps, v.beta, v.c) == ("walsh", 14, Fraction(1, 15), Fraction(1, 64), Fraction(1, 2 ** 50))
    for r in (w, v):
        assert (r.tau, r.sigma) == (1 - Fraction(1, 2 ** 40), 1 - Fraction(1, 2 ** 42))
    assert (w.lam, w.lam_p, w.kappa) == (1 - 7 * XI / 8, 1 - 3 * XI / 4, Fraction(1, 2 ** 47))
    assert (v.lam, v.lam_p, v.kappa) == (1 - 63 * XI / 64, 1 - 31 * XI / 32, Fraction(1, 2 ** 46))


def test_walsh_policy_presets():
    """SPEC_WALSH §1.4: LAYER_WALSH_47 = LayerPolicy(beta=1/8, C1=20), LAYER_WALSH_46 = LayerPolicy(beta=1/64,
    C1=14), theorem mode with SPEC §4.0's theorem defaults; row = the §1.3 row.  LAYER_THEOREM is unchanged."""
    for pol, row in ((LAYER_WALSH_47, ROW_WALSH_47), (LAYER_WALSH_46, ROW_WALSH_46)):
        assert (pol.mode, pol.leaf, pol.guard, pol.batching, pol.bad_set) == \
            ("theorem", "beta", "published", "theorem", "eq23")
        assert (pol.beta, pol.C1, pol.row) == (row.beta, row.C1, row)
    assert LAYER_THEOREM == LayerPolicy() and LAYER_THEOREM.row is None


def test_spec_walsh_margins_exact():
    """SPEC_WALSH §1.3 margins, exactly: lambda - sigma, lambda - tau (1 + c/beta), lambda' - lambda, 1 - eps C1, the
    leaf exponent sigma + beta (1 - sigma) = lambda, and the dominant gap with its slack to kappa; the printed row's
    dominant gap eps c (1 - tau) = 2^-181 -> kappa = 2^-182 and positivity of its margins; the integer inequalities
    behind tau and sigma (with ln 10^6 < 14)."""
    w, v, p = ROW_WALSH_47, ROW_WALSH_46, ROW_PRINTED
    assert (w.lam - w.sigma, w.lam - w.tau * (1 + w.c / w.beta), w.lam_p - w.lam, 1 - w.eps * w.C1) == \
        (XI / 8, 9 * XI / 8 + 8 * XI ** 2, XI / 8, Fraction(1, 21))
    assert (v.lam - v.sigma, v.lam - v.tau * (1 + v.c / v.beta), v.lam_p - v.lam, 1 - v.eps * v.C1) == \
        (XI / 64, 177 * XI / 64 + XI ** 2, XI / 64, Fraction(1, 15))
    for r in (w, v):
        assert r.sigma + r.beta * (1 - r.sigma) == r.lam
    assert w.eps * (1 - w.lam_p) == XI / 28 and XI / 28 - w.kappa == XI / 224 and w.kappa == XI / 32
    assert v.eps * (1 - v.lam_p) == 31 * XI / 480 and 31 * XI / 480 - v.kappa == XI / 480 and v.kappa == XI / 16
    assert p.eps * p.c * (1 - p.tau) == Fraction(1, 2 ** 181) and p.kappa == Fraction(1, 2 ** 182)
    for r in ROWS:
        assert r.lam - r.sigma > 0 and r.lam - r.tau * (1 + r.c / r.beta) > 0 and r.lam_p - r.lam > 0
        assert 1 - r.eps * r.C1 > 0 and r.lam_p > r.sigma + r.beta * (1 - r.sigma)
    assert 339 * 2 ** 40 == 372734441816064 > 14 * 22587335000000
    assert 73 * 2 ** 42 == 321057395310592 > 14 * 19906842167500


@pytest.mark.parametrize("row,K_min", [(ROW_WALSH_47, 2 ** 21), (ROW_WALSH_46, 2 ** 15)])
def test_walsh_theorem_shape_thresholds(row, K_min):
    """SPEC_WALSH §9.1: d = floor(K^eps) >= 2 needs K_root >= 2^21 (eps = 1/21) or 2^15 (eps = 1/15): None just below,
    d = 2 at the threshold (t = (r, r), r = 2^(K/2), h = floor(2^c) = 1)."""
    assert theorem_shape(K_min - 1, row.eps, row.c) is None
    s = theorem_shape(K_min, row.eps, row.c)
    assert (s.d, s.ell, s.chunk_bits) == (2, K_min // 2, 1) and s.t == (1 << (K_min // 2),) * 2
    assert all(theorem_shape(K, row.eps, row.c) is None for K in range(1, 65))


def test_theorem_mode_shape_is_none_for_every_row():
    """No cutoff certificate exists (SPEC §6.2; SPEC_WALSH §9.1 does not supply P_tape either): theorem mode is never
    entered, not even where the Walsh rows' theorem_shape exists."""
    for row in ROWS:
        for K in list(range(1, 41)) + [2 ** 15, 2 ** 21]:
            assert theorem_mode_shape(K, row) is None


def test_faithful_schedule_rows():
    """faithful_schedule(row): name, theorem_row and the row's policy preset; unknown rows are rejected."""
    assert (faithful_schedule().name, faithful_schedule().theorem_row, faithful_schedule().layer) == \
        ("faithful", "printed", LAYER_THEOREM)
    for name, pol in (("walsh47", LAYER_WALSH_47), ("walsh46", LAYER_WALSH_46)):
        s = faithful_schedule(name)
        assert (s.name, s.theorem_row, s.layer, s.bridge_d) == (f"faithful-{name}", name, pol, None)
    with pytest.raises(ValueError):
        faithful_schedule("walsh48")
    with pytest.raises(ValueError):
        Schedule(name="x", theorem_row="bogus")


@pytest.mark.parametrize("row", ["walsh47", "walsh46"])
def test_faithful_walsh_schedules_fall_back(row):
    """SPEC_WALSH §9.1: at every feasible size the faithful Walsh schedules run the 2D fallback (SPEC §6.4): exact
    products, counter multiply.fallback_2d, never the theorem branch or the bridge."""
    ctx = make_ctx(faithful_schedule(row))
    rng = random.Random(len(row))
    for n in (65, 500, 3000):
        a, b = rng.getrandbits(n) | (1 << (n - 1)), rng.getrandbits(n)
        assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    assert c["multiply.fallback_2d"] == 6 and c.get("multiply.theorem_mode", 0) == 0 and c.get("bridge.dft", 0) == 0


def test_walsh_theorem_branch_plumbing(monkeypatch):
    """Force the (unreachable) theorem branch for the Walsh row at a tiny size: the bridge with the shape's d, the Walsh
    middle (not Bluestein), the network engine under the schedule's layer (a test-mode layer with the row's
    beta = 1/8, since the published guard is not executable) and Lemma 3/12 movements, with the SPEC §2.5 test
    fixtures C1 / B1 in place of the real h = 100 networks (never executable)."""
    import subnlogn.multiply as mm
    seen = []

    def forced(K, row):
        seen.append(row.name)
        return theorem_shape(K, eps=Fraction(1, 2), c=Fraction(1, 2))

    monkeypatch.setattr(mm, "theorem_mode_shape", forced)
    layer = LayerPolicy(mode="test", guard="compiled", beta=ROW_WALSH_47.beta)
    ctx = make_ctx(faithful_schedule("walsh47").with_(layer=layer, mul_direct_bits=0, net_cx="C1", net_bit="B1"))
    rng = random.Random(47)
    a, b = rng.getrandbits(96), rng.getrandbits(96)
    assert root_parameters(96)[2] == 5             # forced shape: d = 2, l = 3, t = (4, 8), h = 1
    assert multiply(a, b, ctx) == a * b
    c = ctx.inst.counts
    assert seen == ["walsh47", "walsh47"]
    assert c["multiply.theorem_mode"] == 2 and c["bridge.dft"] == 2 and c["prop14.network_layer"] == 0
    assert c["walsh.positional_map"] > 0 and c["walsh.chunk_round"] > 0 and c["m6.layer.network"] > 0
    assert c.get("bluestein.tensor_dft", 0) == 0 and c.get("bluestein.complex_convolution", 0) == 0
    assert c["bridge.axis_reverse"] > 0                 # storage <-> tensor by Lemma 12 (SPEC_WALSH §6.3)


def test_theorem_mode_layer_must_match_the_row(monkeypatch):
    """A theorem-mode layer that is not the row's preset is rejected before the branch runs (here the printed
    LAYER_THEOREM, beta = 1/2, under the Walsh row 47, beta = 1/8)."""
    import subnlogn.multiply as mm
    monkeypatch.setattr(mm, "theorem_mode_shape", lambda K, row: theorem_shape(K, eps=Fraction(1, 2),
                                                                                c=Fraction(1, 2)))
    ctx = make_ctx(faithful_schedule("walsh47").with_(layer=LAYER_THEOREM, mul_direct_bits=0))
    with pytest.raises(AssertionError, match="does not match the parameter row"):
        multiply((1 << 95) + 3, (1 << 94) + 5, ctx)
