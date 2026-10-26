"""Mutation-sensitivity tests: each one kills a deliberate mutant that
the fast suite let through, by pinning a specified constant, exercising a check with an input that must trip it,
or asserting that a faithful path is taken rather than a silent fallback."""

import random
from fractions import Fraction

import pytest

import path_model as PM
from conftest import make_ctx
from subnlogn.bridge.bridge_dft import bridge_geometry, normalization_exponent
from subnlogn.bridge.deconv import deconv_axis
from subnlogn.fixedpoint import FxVec
from subnlogn.instrument import Instrument
from subnlogn.m6.cnet import _row_add_direct
from subnlogn.m6.engine import compiled_fixture, make_engine
from subnlogn.m6.policy import LAYER_TEST
from subnlogn.middle3.bluestein import complex_convolution
from subnlogn.middle3.synth import Synth
from subnlogn.schedule import test_schedule

_CACHE: dict = {}


def test_engine_lemma13_swaps_use_the_bit_network():
    """make_engine(net_bit=B1) routes Lemma 13's chunk exchanges through Lemma 12 on the bit network (SPEC §3.8,
    §4.3), never silently through the bitwise base case: THREE row additions on L = f K = 4 slots (f = 2, K = 2,
    rho = 1, 2^12 records) equal the address-permutation oracle, and the counts are exact (a
    shortcut after the first row addition, mutant A36, must fail).  Independent closed form (path_model): z is the
    physically rightmost slot, so each call makes 8 exchanges (the four y-target lines), each ONE Lemma 12 call on
    u = 4 bits that makes one Prop 11 call at level 1 (e = 3, k = 2, rho = 1, e - rho = 2 = one 2^1 piece)."""
    net, b1 = compiled_fixture("C1", _CACHE), compiled_fixture("B1", _CACHE)
    inst = Instrument()
    eng = make_engine(net, 2, LAYER_TEST, net_bit=b1, inst=inst)
    nb, K, rho = 12, 2, 1
    dst, src, z = [11, 9], [7, 5], [3, 1]
    rng = random.Random(12)
    arr = [(rng.getrandbits(16), rng.getrandbits(16)) for _ in range(1 << nb)]
    calls = 3
    for _ in range(calls):
        nxt = eng.row_add(arr, 1, nb, dst, src, z, K, rho)
        assert nxt == _row_add_direct(arr, dst, src)
        arr = nxt
    one = PM.lemma13_row_add(PM.Eng(net, 2, LAYER_TEST, K, b1), {0: min(dst), 1: min(src), 2: min(z)}, 0, 1, 2,
                             len(dst), 1 << nb)
    assert one["lemma13.swap"] == 8 and PM.l12_calls(4, b1) == 1
    exp = {k: calls * v for k, v in one.items() if not k.startswith("m6.")}
    PM.assert_exact(inst.counts, exp)


def test_prop18_disk_test_uses_the_squared_radius():
    """SPEC v1.2 §5.10: the Prop 18 output must lie in the caller's disk before narrowing.  Constant operands 1/2
    give M_C = 1/4 everywhere: inside the default 0.701 disk, outside a caller radius of 1/8, so the test must
    fire (a check against radius^1 instead of radius^2 would let |z| = 1/4 < sqrt(1/8) through)."""
    t, p = (4, 4), 24
    R, r = 16, 4
    half = (1 << p) // 2
    f = [(half, 0)] * R
    sy = Synth((4,), 2, 1)
    out = complex_convolution(f, f, t, p, sy)
    assert all(abs(a - (1 << p) // 4) < (1 << (p - 12)) and abs(b) < (1 << (p - 12)) for a, b in out)
    with pytest.raises(AssertionError, match="disk"):
        complex_convolution(f, f, t, p, sy, disk=Fraction(1, 8))
    complex_convolution(f, f, t, p, sy, disk=Fraction(1, 4) + Fraction(1, 1 << 10))   # just inside: passes


def test_deconv_declared_width_is_enforced():
    """The bridge's deconvolution states are asserted within the declared width f + K + 6
    (magnitude bits q + K + 5).  Inputs 2^(q+K+8) (outside the contract) must trip that check, which a lax width
    would let through."""
    d, K = 2, 4
    geom = bridge_geometry(K, d)
    q, w = 40, 30
    ctx = make_ctx(test_schedule(bridge_d=d))
    big = 1 << (q + K + 8)
    Y = FxVec([big] * geom.R, [-big] * geom.R, q)
    with pytest.raises(AssertionError, match="magnitude bits"):
        deconv_axis(ctx, Y, geom, 2, w)
    small = 1 << q
    deconv_axis(ctx, FxVec([small] * geom.R, [0] * geom.R, q), geom, 2, w)          # in-contract input passes


@pytest.mark.parametrize("t", [(4, 4), (4, 8), (8, 8, 16), (2, 2, 4)])
def test_r2_prescaling_exponent(t):
    """br_r2 §5.1, (5.1)-(5.2): S = 2^(H + ceil(lg(R/t_1)/2) + 4) with 2^H twice the next power of two above
    max(1, max|Re|, max|Im|), hence 16 sqrt(Q) X <= S < 128 sqrt(Q) X (Q = R/t_1, X = max(1, ||x||)); checked
    exactly, including inputs whose sup-norm coordinate has both parts nonzero (X just above a power of two)."""
    from subnlogn.bridge.geometry import BridgeGeometry
    geom = BridgeGeometry(t)
    R, Q = geom.R, geom.R // geom.tt(1)
    p = 20
    rng = random.Random(R)
    cases = []
    for k in range(-3, 6):
        m = 1 << (p + 2 + k)                        # max |component| = 2^k in absolute units
        re = [rng.randint(-m, m) for _ in range(R)]
        im = [rng.randint(-m, m) for _ in range(R)]
        re[0], im[0] = m, max(1, m >> 3)            # |x_0| slightly above 2^k
        cases.append((re, im))
    cases.append(([0] * R, [0] * R))
    for re, im in cases:
        x = FxVec(re, im, p + 2)
        e = normalization_exponent(x, p, geom, "r2")
        X2 = max(Fraction(1), max(Fraction(a * a + b * b, 1 << (2 * (p + 2))) for a, b in zip(re, im)))
        S2 = Fraction(1 << (2 * e))
        assert 256 * Q * X2 <= S2 < 16384 * Q * X2, (t, e)


def test_carry_propagate_flushes_the_final_carry():
    """MS Thm 7.1 part 1: carry propagation in radix 2^b must flush every digit of the final carry.  Inside
    multiply() the R0 >= 2N coefficient slots always absorb it (so dropping the flush is invisible there); here
    the coefficients overflow past the last slot by several digits."""
    from subnlogn.bits import carry_propagate, digits_to_int
    rng = random.Random(7)
    for b in (4, 13, 64):
        for n in (1, 2, 7):
            coeffs = [rng.getrandbits(3 * b) for _ in range(n)]
            digits = carry_propagate(coeffs, b)
            assert all(0 <= d < (1 << b) for d in digits)
            assert digits_to_int(digits, b) == sum(c << (j * b) for j, c in enumerate(coeffs))
    assert carry_propagate([(1 << 8) + 5], 4) == [5, 0, 1]
