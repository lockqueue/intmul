"""SPEC v1.1 §4.0 LayerPolicy and the integer rules reading it (leaf test §4.5, batching plan §4.6,
guard width §4.8), against the values printed in SPEC §4.8/§4.10 and SPEC_WALSH."""

from fractions import Fraction

import pytest

from subnlogn.m6.policy import (LAYER_TEST, LAYER_THEOREM, GuardInfeasible, LayerPolicy,
                                base_m_pieces, batch_plan, capped_pow, ceil_log, compiled_delta,
                                guard_exponent, is_leaf, layer_delta, published_delta)
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_C1, fixture_C2


@pytest.fixture(scope="module")
def C1():
    return compile_network(fixture_C1())


def test_presets_are_the_printed_values():
    p = LAYER_THEOREM
    assert (p.mode, p.beta, p.leaf, p.C1, p.guard, p.batching, p.forced_q0, p.bad_set) == \
        ("theorem", Fraction(1, 2), "beta", None, "published", "theorem", None, "eq23")
    t = LAYER_TEST
    assert (t.mode, t.leaf, t.C_leaf_e, t.guard, t.batching) == ("test", "count", 1, "compiled", "forced")


@pytest.mark.parametrize("bad", [dict(mode="x"), dict(leaf="x"), dict(guard="x"), dict(batching="x"),
                                 dict(bad_set="x"), dict(beta=Fraction(0)), dict(beta=0.5),
                                 dict(C_leaf_e=0), dict(forced_q0=3),   # forced_q0 needs test mode
                                 dict(mode="test", batching="forced", forced_q0=3)])
def test_invalid_policies_rejected(bad):
    with pytest.raises(ValueError):
        LayerPolicy(**bad)


def test_capped_pow_and_ceil_log():
    assert capped_pow(3, 4, 100) == 81 and capped_pow(3, 5, 100) == 101
    assert [ceil_log(x, 3) for x in (1, 2, 3, 4, 9, 10, 27, 28, 40)] == [0, 1, 1, 2, 2, 3, 3, 4, 4]
    assert base_m_pieces(11, 3) == [9, 1, 1] and base_m_pieces(7, 3) == [3, 3, 1]


def test_leaf_rule_exact():
    # printed beta = 1/2: leaf iff e < sqrt(d); d = 20 -> e <= 4 leaf, 5 not (5^2 = 25 >= 20)
    assert [is_leaf(e, 20, LAYER_THEOREM) for e in (1, 2, 4, 5, 9)] == [True, True, True, False, False]
    assert not is_leaf(4, 16, LAYER_THEOREM) and is_leaf(3, 16, LAYER_THEOREM)   # 16 < 16 is false
    walsh = LayerPolicy(beta=Fraction(1, 8))
    assert not is_leaf(3, 13, walsh)            # 3^8 >= 13: the network already runs at d = 13
    assert is_leaf(1, 13, walsh)
    count = LayerPolicy(mode="test", leaf="count", C_leaf_e=3)
    assert is_leaf(3, 10 ** 9, count) and not is_leaf(4, 2, count)


def test_batch_plan_faithful_d20(C1):
    """SPEC §4.10: d = 20, D = 19, K = 1: q0 = 8, k0 = 3, rows 256 -> 270, pieces 9 + 1 + 1."""
    plan = batch_plan(19, 20, 1, C1, LayerPolicy(mode="test", guard="compiled"))
    assert (plan.individual, plan.q0, plan.k0, plan.pieces, plan.row_len, plan.row_pad) == \
        (False, 8, 3, (9, 1, 1), 256, 270)
    assert batch_plan(8, 20, 1, C1, LAYER_THEOREM).individual          # D <= q0


def test_batch_plan_walsh_and_forced_q0(C1):
    walsh = LayerPolicy(beta=Fraction(1, 8), mode="test", guard="compiled")
    plan = batch_plan(13, 13, 1, C1, walsh)                              # SPEC §4.10 / SPEC_WALSH W-T12
    assert (plan.q0, plan.pieces, plan.k0, plan.row_len, plan.row_pad) == (6, (3, 3, 1), 3, 64, 81)
    dev11 = LayerPolicy(mode="test", leaf="count", guard="compiled", forced_q0=4)
    plan = batch_plan(13, 13, 1, C1, dev11)                             # Dev-11: one 9-piece
    assert (plan.q0, plan.pieces, plan.k0, plan.row_len, plan.row_pad) == (4, (9,), 2, 16, 18)
    forced = batch_plan(9, 2, 1, C1, LAYER_TEST)
    assert (forced.q0, forced.pieces, forced.k0, forced.row_len, forced.row_pad) == (0, (9,), 2, 1, 9)


def test_guard_exponent_and_published_delta(C1):
    # B = 13 + 64 * 7^3 = 21965, nu = 10 (3^10 >= B > 3^9), C1 = max(20, 13) = 20
    assert guard_exponent(LAYER_THEOREM, C1) == 20
    assert guard_exponent(LayerPolicy(C1=14), C1) == 14                 # Walsh row value, >= nu + 3
    with pytest.raises(AssertionError):
        guard_exponent(LayerPolicy(C1=12), C1)
    B = 13 + 64 * 7 ** 3
    assert published_delta(LAYER_THEOREM, C1, 2) == 128 * 3 * B * B * 2 ** 20
    with pytest.raises(GuardInfeasible):
        layer_delta(C1, 3, 2, 1, LAYER_THEOREM)


@pytest.mark.parametrize("fixture", [fixture_C1, fixture_C2])
def test_compiled_delta_values(fixture):
    net = compile_network(fixture())
    if fixture is fixture_C1:   # SPEC §4.8: E_net = 140, A(3) = 244, A(9) = 3312, A(27) = 43196
        assert compiled_delta(net, 3, 2, 1, LAYER_TEST) == 244 + 1 + 25
        assert compiled_delta(net, 9, 2, 1, LAYER_TEST) == 3312 + 4 + 25
        assert compiled_delta(net, 27, 2, 1, LAYER_TEST) == 43196 + 13 + 25
        pol = LayerPolicy(mode="test", guard="compiled")
        # d = 20, D = 19: pieces 9 (node, leaf children: A = 13*24 + 140 = 452), 1, 1; 8 preprocessed
        assert compiled_delta(net, 19, 20, 1, pol) == 452 + 8 + 8 + 8 * 8 + 9 + 25
    assert compiled_delta(net, 2, 2, 1, LAYER_TEST) == 16 + 1 + 25      # e % m != 0: leaves only
