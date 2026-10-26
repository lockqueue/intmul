"""Golden constants: the schedule constants are pinned against their sources.

Every formula below is transcribed independently from the cited source line, with integer-only ceil/floor of lg
computed by doubling, and compared with the code over a grid of (p, K, d) and with the literal numbers printed in the
sources.  Sources: MS = the companion manuscript [MS] (line numbers of its source), br_r2 = bridge derivation
r2, br_r3 = bridge derivation r3, SPEC = the internal implementation specification.  The error tests elsewhere
compute their bounds from the schedule under test; these tests are what pin the schedule itself.
"""

import random
from fractions import Fraction

import pytest

from subnlogn.bridge import deconv as bdeconv
from subnlogn.bridge import spread as bspread
from subnlogn.bridge.bridge_dft import bridge_dft
from subnlogn.bridge.precision import certify_bridge_precision
from subnlogn.context import Ctx
from subnlogn.fixedpoint import FxVec
from subnlogn.middle3 import bluestein
from subnlogn.multiply import multiply, root_parameters
from subnlogn.schedule import faithful_schedule, split_2d, test_policy, test_schedule
from subnlogn.walsh import fft as wfft


def ceil_lg(x: int) -> int:
    k, v = 0, 1
    while v < x:
        v, k = 2 * v, k + 1
    return k


def floor_lg(x: int) -> int:
    k = 0
    while x >= 2:
        x, k = x // 2, k + 1
    return k


# -- MS root parameters and the direct-product cutoff --------------------------------------------------------


def ms_root(n: int) -> tuple[int, int, int, int, int]:
    """MS listing L708-712: b = max(4, floor(lg n)), N = ceil(n/b), R0 = 2^K0 = the smallest power of two >= 2N,
    p0 = 2b + 2K0 + 6."""
    b = max(4, floor_lg(n))
    N = -(-n // b)
    K0 = ceil_lg(2 * N)
    return b, N, K0, 1 << K0, 2 * b + 2 * K0 + 6


ROOT_GRID = list(range(1, 300)) + [511, 512, 513, 1000, 4097, 10 ** 5, 123457, 10 ** 6, 2 ** 31 + 5, 10 ** 9]


def test_root_parameters_ms_listing():
    for n in ROOT_GRID:
        b, N, K0, R0, p0 = root_parameters(n)
        assert (b, N, K0, R0, p0) == ms_root(n), n
        assert 2 * N <= R0 < 4 * N                              # MS L776: 2N <= R0 < 4N
    assert root_parameters(10 ** 9)[::2] == (29, 27, 118)       # MS L850: b = 29, K0 = 27, p0 = 118 at n = 10^9
    assert faithful_schedule().mul_direct_bits == 64           # MS listing L706: n <= 64 -> A * B


def test_recovery_constant_ms_thm71():
    """MS L796 (Thm 7.1 part 1): pre-rounding recovery error < 3.19 * 2^(2b + 2K0 - 1) * 2^-p0 = 3.19/128 = 319/12800,
    the exponent 2b + 2K0 - 1 - p0 being -7 for every n; multiply asserts against exactly this value."""
    for n in ROOT_GRID:
        b, _, K0, _, p0 = ms_root(n)
        assert 2 * b + 2 * K0 - 1 - p0 == -7
    rng = random.Random(1)
    for bits in (65, 300, 1000):
        ctx = Ctx(schedule=faithful_schedule())
        a, c = rng.getrandbits(bits) | 1 << (bits - 1), rng.getrandbits(bits) | 1 << (bits - 1)
        assert multiply(a, c, ctx) == a * c
        notes = [v for k, v in ctx.inst.notes if k == "multiply.recovery_margin"]
        assert notes and all(eps == Fraction(319, 12800) and worst <= eps for worst, eps in notes)


# -- MS eq. (cert-sched), Thm 6.3 (slot-width), Lemma 6.5, listing split and leaf rule ------------------------


def ms_level(R: int, p: int, leaf: bool) -> dict:
    """MS eq. (cert-sched) L634-636: p_work = p + 2K + 16, p_child = p + 6K + 32, q_child = p_child + 2,
    m1 = p_child; Thm 6.3 L604-606: W~ = min(2 m1 + 1, r), B_slot = 2q + p + ceil(lg(W~ + 1)) + 4; listing L737-738:
    t1 = 2^floor(K/2), r = 2^ceil(K/2); Lemma 6.5 part 2 (L647, L693): leaf q_b = p + K + 16."""
    K = floor_lg(R)
    if leaf:
        return {"leaf": True, "q_b": p + K + 16}
    k1, k2 = K // 2, -(-K // 2)
    t1, r = 1 << k1, 1 << k2
    p_child = p + 6 * K + 32
    q = p_child + 2
    m1 = p_child
    Wt = min(2 * m1 + 1, r)
    return {"leaf": False, "k1": k1, "k2": k2, "t1": t1, "r": r, "nu": r // t1, "p_work": p + 2 * K + 16,
            "p_child": p_child, "q_child": q, "m1": m1, "W": 2 * m1 + 1, "W_tilde": Wt,
            "B_slot": 2 * q + p + ceil_lg(Wt + 1) + 4}


def _fields(lv, keys):
    return {k: getattr(lv, k) for k in keys}


P_GRID = (8, 9, 12, 16, 24, 33, 64, 100, 118, 200)


@pytest.mark.parametrize("name,sched,leaf_rule", [
    ("faithful", faithful_schedule(), lambda R, p: R <= 4 * p * p),        # MS listing L733: leaf iff R <= 4p^2
    ("test bt=2", test_schedule(base_threshold=2), lambda R, p: R <= 2),    # forced recursion: same formulas
    ("test_policy(3)", test_policy(3), lambda R, p: R <= 2),
])
def test_cert_sched_and_slot_width(name, sched, leaf_rule):
    for p in P_GRID:
        for K in range(1, 25):
            R = 1 << K
            expect = ms_level(R, p, leaf_rule(R, p))
            lv = sched.level(R, p)
            assert _fields(lv, expect) == expect, (name, p, K)


def test_cert_sched_literal_ms_example():
    """MS L850: n = 10^9 gives R0 = 2^27, p0 = 118; under R <= 4p^2 the child R1 = 2^14 is a leaf (one split)."""
    lv0, lv1 = faithful_schedule().chain(1 << 27, 118)
    assert (lv0.p_work, lv0.p_child, lv0.q_child, lv0.t1, lv0.r, lv0.W, lv0.W_tilde, lv0.B_slot) == \
        (188, 312, 314, 1 << 13, 1 << 14, 625, 625, 760)
    assert lv1.leaf and lv1.R == 1 << 14 and lv1.q_b == 312 + 14 + 16


def test_split_ms_listing():
    """MS listing L737-738: t1 = 2^floor(K/2), r = 2^ceil(K/2)."""
    for K in range(0, 65):
        assert split_2d(K) == (K // 2, -(-K // 2))


def test_drop_in_headroom_bits():
    """br_r2 L1482 (§8): 'Allow a few additional integer headroom bits for the uniformly specified solver prefixes;
    adding four is sufficient.'"""
    assert faithful_schedule().solver_headroom_bits == 4
    assert test_schedule().solver_headroom_bits == 4


# -- bridge precision contract (r2 Thm 2), r3 profile, p_fft = P + 2 refinement ------------------------


def br2_params(p: int, K: int, d: int) -> tuple[int, int, int]:
    """br_r2 Thm 2 L102-124: (2.8) w = p + K + ceil(lg d) + 20, (2.9) P = 2p + 12K + 32 ceil(lg(p + K + 2)) + 256,
    spatial truncation |e| <= P (m = P).  Returned as (P, w, m)."""
    P = 2 * p + 12 * K + 32 * ceil_lg(p + K + 2) + 256
    return P, p + K + ceil_lg(d) + 20, P


def test_bridge_thm2_and_r3_profile():
    r2, r3 = test_schedule(bridge_d=2), test_schedule(bridge_d=2).with_(bridge_constants="r3")
    for p in P_GRID + (28, 300):
        for K in range(2, 31):
            for d in (2, 3, 4, 5, 8, 10, 16):
                assert r2.bridge_params(p, K, d) == br2_params(p, K, d), (p, K, d)
                P = 2 * p + 6 * K + 128                     # br_r3 L73 (2.3): P = 2p + 6K + 128, w = P, m = P
                assert r3.bridge_params(p, K, d) == (P, P, P), (p, K, d)
    assert faithful_schedule().bridge_constants == "r2"
    assert br2_params(28, 5, 4)[0] == 564                   # SPEC L1383: Appendix A, p = 28, t = (2, 2, 2, 4)


def open5_widths(p: int, t: tuple[int, ...]) -> dict:
    """SPEC §5.10 (p_fft = P + 2) L1342-1358: q = p_fft = P + 2, completed spreads q + 2, Prop 18 output q + 2 + lg M
    (M = R / t_d), deconvolution states q + K + 6."""
    R = 1
    for ti in t:
        R *= ti
    K, M = floor_lg(R), R // t[-1]
    P = br2_params(p, K, len(t))[0]
    q = P + 2
    return {"P": P, "fractional_bits": q, "component_bits": q + 2, "prop18_component_bits": q + 2 + floor_lg(M),
            "solver_component_bits": q + K + 6}


@pytest.mark.parametrize("p,t", [(28, (2, 2, 2, 4)), (10, (4, 4)), (12, (2, 4, 4)), (16, (4, 4, 8, 8)),
                                 (20, (8, 8))])
def test_open5_widths(p, t):
    got = certify_bridge_precision(p, t)
    assert {k: got[k] for k in open5_widths(p, t)} == open5_widths(p, t)
    if (p, t) == (28, (2, 2, 2, 4)):                        # SPEC L1383-1384: 564, 566, 568, 571, 577
        assert [got[k] for k in open5_widths(p, t)] == [564, 566, 568, 571, 577]


class _Recorder:
    def __init__(self, monkeypatch):
        self.monkeypatch = monkeypatch

    def wrap(self, module, name):
        orig, log = getattr(module, name), []

        def wrapper(*args, **kwargs):
            log.append((args, kwargs))
            return orig(*args, **kwargs)

        self.monkeypatch.setattr(module, name, wrapper)
        return log


@pytest.mark.parametrize("middle,d,K", [("direct", 3, 6), ("bluestein", 2, 4), ("walsh", 2, 4)])
def test_bridge_runtime_widths(monkeypatch, middle, d, K):
    """What a bridge call actually uses (SPEC §5.10): records and middle on q = P + 2, overlap-add
    slots of 4P + 16 bits, deconvolution states asserted within q + K + 6 bits (q + K + 5 magnitude bits plus the
    sign), and the Prop 18 disk 1/8 + C18 2^-q with C18 = sqrt(2) M (3l + 1) < (99/70) M (3l + 1)."""
    rec = _Recorder(monkeypatch)
    spreads, solves = rec.wrap(bspread, "spread_row"), rec.wrap(bdeconv, "cyclic_solve")
    blue, walsh = rec.wrap(bluestein, "tensor_positive_dft"), rec.wrap(wfft, "tensor_fft_walsh")
    p, R = 10, 1 << K
    sched = test_schedule(bridge_d=d).with_(bridge_middle=middle, bridge_movement="lemma12")
    ctx = Ctx(schedule=sched, tables={}, capture={})
    rng = random.Random(K)
    big = (1 << (2 * p + 2)) * 7 // 10
    x = FxVec([rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)], p + 2)
    bridge_dft(ctx, x, R, p, d)
    P, w, m, geom = ctx.capture["bridge_params"]
    assert (P, w, m) == br2_params(p, K, d)
    q = P + 2
    assert ctx.capture["bridge_U"].q == q
    assert spreads and all(args[7] == 4 * P + 16 and args[8] == q for args, _ in spreads)
    assert solves and all(kw["max_bits"] == q + K + 5 and args[6] == q for args, kw in solves)
    if middle == "bluestein":
        (args, kw), = blue
        t = geom.t
        M, ell = R // t[-1], floor_lg(t[-1])
        assert args[2] == q and kw["disk"] == Fraction(1, 8) + Fraction(99, 70) * M * (3 * ell + 1) / (1 << q)
    if middle == "walsh":
        (args, _), = walsh
        assert args[2] == q
