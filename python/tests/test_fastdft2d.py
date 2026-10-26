"""FastDFT (M1, negative-carrier drop-in) against the naive exact oracle: the contract
||Z-hat - F_R x|| <= 2^-p max(1, ||x||) (MS eq. (inductive-bound)) and the pre-rounding
certificate (MS Lemma 6.5 with r2 §8 constants), under faithful and forced-deep test schedules."""

import random
from fractions import Fraction

import pytest

from conftest import make_ctx
from oracle import OracleDFT, sqrt_upper
from subnlogn.fastdft2d import fast_dft, certificate_2d
from subnlogn.fixedpoint import FxVec
from subnlogn.schedule import faithful_schedule, test_schedule


def _inputs(kind: str, R: int, p: int, rng: random.Random):
    q = p + 2
    big = (1 << (q + p)) * 7 // 10   # coordinate bound so that |x| <= 2^p (0.7 < 1/sqrt 2)
    if kind == "random_max":
        return ([rng.randint(-big, big) for _ in range(R)], [rng.randint(-big, big) for _ in range(R)])
    if kind == "random_unit":
        return ([rng.randint(-(1 << q), 1 << q) for _ in range(R)],
                [rng.randint(-(1 << q), 1 << q) for _ in range(R)])
    if kind == "constant_max":
        return [big] * R, [-big] * R
    if kind == "alternating":
        return [big * (-1) ** j for j in range(R)], [0] * R
    if kind == "impulse":
        re = [0] * R
        re[rng.randrange(R)] = big
        return re, [0] * R
    if kind == "nyquist_row":
        # supported on the old Nyquist side-information row j1 = t1/2 (r1 §10.6)
        K = R.bit_length() - 1
        t1 = 1 << (K // 2)
        re, im = [0] * R, [0] * R
        for j in range(R):
            if j % t1 == t1 // 2:
                re[j] = rng.randint(-big, big)
                im[j] = rng.randint(-big, big)
        return re, im
    if kind == "zero":
        return [0] * R, [0] * R
    raise ValueError(kind)


KINDS = ["random_max", "random_unit", "constant_max", "alternating", "impulse", "nyquist_row", "zero"]


def _check(sched, R, p, kind, seed):
    rng = random.Random(seed)
    re, im = _inputs(kind, R, p, rng)
    q = p + 2
    ctx = make_ctx(sched, capture=True, monitor=True)
    z = fast_dft(ctx, FxVec(re, im, q), R, p)
    orc = OracleDFT(re, im, q, p)
    A = max(Fraction(1), sqrt_upper(FxVec(re, im, q).sup_norm_sq()))
    lv = sched.level(R, p)
    cert = certificate_2d(lv, A)
    err = sqrt_upper(orc.error_sq_vs(z.re, z.im, z.q))
    assert err <= cert.contract + orc.err, (R, p, kind, float(err * 2 ** p))
    assert err <= cert.total + orc.err
    if not lv.leaf:
        zc = ctx.capture["Zcomp"]
        pre = sqrt_upper(orc.error_sq_vs(zc.re, zc.im, zc.q))
        assert pre <= cert.pre_rounding + orc.err, (R, p, kind)
    return ctx


@pytest.mark.parametrize("R", [2, 4, 8, 16, 32, 64, 128])
@pytest.mark.parametrize("kind", KINDS)
def test_fastdft_deep_test_schedule(R, kind):
    """base_threshold = 2: maximal recursion depth (depth >= 3 for R >= 32)."""
    sched = test_schedule(base_threshold=2)
    p = max(8, R.bit_length() - 1) + 12
    ctx = _check(sched, R, p, kind, seed=R * 17 + len(kind))
    depth = len(sched.chain(R, p)) - 1
    if R >= 32:
        assert depth >= 3
    if R > 2:
        assert ctx.inst.counts["fastdft.node"] >= 1


@pytest.mark.parametrize("R,bt", [(256, 2), (256, 16), (512, 8), (64, 4)])
def test_fastdft_mixed_thresholds(R, bt):
    sched = test_schedule(base_threshold=bt)
    for kind in ("random_max", "nyquist_row"):
        _check(sched, R, 20, kind, seed=R + bt)


@pytest.mark.parametrize("R,p", [(16, 8), (64, 9), (256, 10), (1024, 16), (512, 9), (1024, 10)])
def test_fastdft_faithful_schedule(R, p):
    """Faithful schedule: leaf iff R <= 4 p^2.  (512, 9) and (1024, 10) recurse naturally
    (R > 4p^2) with the certified schedule; the others are leaves."""
    sched = faithful_schedule()
    ctx = _check(sched, R, p, "random_max", seed=R)
    lv = sched.level(R, p)
    assert lv.leaf == (R <= 4 * p * p)
    if not lv.leaf:
        assert ctx.inst.counts["fastdft.node"] >= 1


def test_fastdft_record_heights():
    """Record-width monitor (MS eq. (record-width)): child inputs <= 2^{H_{l+1}} where
    H_{l+1} = H_l + lg r + 1; solver prefixes within the +2+4 headroom (r2 §8)."""
    sched = test_schedule(base_threshold=2)
    R, p = 64, 20
    rng = random.Random(5)
    re, im = _inputs("random_max", R, p, rng)
    ctx = make_ctx(sched, monitor=True)
    fast_dft(ctx, FxVec(re, im, p + 2), R, p)
    H = p + 1   # |x| <= 2^p => coordinates < 2^{H_0} with H_0 = p (+1 slack)
    lv = sched.level(R, p)
    H1 = H + lv.k2 + 1
    assert ctx.inst.heights["d0.spread"] <= lv.q_child + H1
    assert ctx.inst.heights["d0.child_in"] <= lv.q_child + H1
    # solver states (prefixes, prescaled RHS, outputs): within 2^{H_{l+1} + 2 + headroom}
    assert ctx.inst.heights["d0.solver"] <= lv.q_child + H1 + 2 + sched.solver_headroom_bits
