"""The middle tensor DFT of the bridge, behind a pluggable interface.

``middle_dft(ctx, U, geom, P) -> FxVec`` computes the positive normalized tensor DFT
(F_t U)_u = (1/R) sum_c U_c exp(2 pi i sum_i c_i u_i / t_i)  over all d axes (axis 1 included),
in the storage layout (index sum_i c_i A_i, c_1 least significant) and on the scale of U.

Backends (``Schedule.bridge_middle``):
* ``"direct"`` (M2 reference, this module): the tensor product of 1D certified radix-2 FFTs.
* ``"bluestein"`` (M3) and ``"walsh"`` (M9, :mod:`subnlogn.walsh.fft`; SPEC_WALSH §6.1) register here.

Direct backend error (derived here from MS Lemma 6.5's leaf argument; not from the bridge
write-ups): all sum_i lg t_i = K butterfly stages run on the internal grid q_m = P + K + guard
(guard = ``Schedule.bridge_mid_guard``) with twiddles Q_{q_m}(e^{2 pi i k/t_i}); every stage is a
normalized butterfly (1/2)(A +- w B), a sup-norm contraction, so with M = max(1, ||U||)
    ||out_internal - F_t U|| <= 2.16 K 2^{-q_m} M,
and the final rounding to the scale of U adds <= sqrt(2)/2 2^{-q}.
"""

from __future__ import annotations

from .. import certified
from ..basefft import bit_reverse_perm
from ..fixedpoint import FxVec
from .movement import axis_lines

__all__ = ["middle_dft", "direct_middle_dft", "MIDDLE_BACKENDS"]


def _axis_twiddles(ctx, t: int, qm: int) -> tuple[list[int], list[int]]:
    key = ("mid_tw", t, qm)
    tw = ctx.tables.get(key)
    if tw is None:
        re, im = [], []
        for k in range(max(1, t // 2)):
            a, b = certified.unit_root(k, t, qm)
            re.append(a)
            im.append(b)
        tw = (re, im)
        ctx.tables[key] = tw
    return tw


def direct_middle_dft(ctx, U: FxVec, geom, P: int) -> FxVec:
    """Direct tensor DFT (M2 reference backend); see the module docstring for the error bound."""
    q = U.q
    qm = P + geom.K + ctx.schedule.bridge_mid_guard
    up = qm - q
    shr, mul = ctx.shr, ctx.word_mul()              # butterfly products by the word multiplier
    ar = [v << up for v in U.re]
    ai = [v << up for v in U.im]
    nbfly = 0
    for h in range(1, geom.d + 1):
        t = geom.tt(h)
        if t == 1:
            continue
        K_h = t.bit_length() - 1
        rev = bit_reverse_perm(K_h)
        twr, twi = _axis_twiddles(ctx, t, qm)

        def fft_line(digits, vr, vi, t=t, rev=rev, twr=twr, twi=twi):
            nonlocal nbfly
            xr = [vr[rev[j]] for j in range(t)]
            xi = [vi[rev[j]] for j in range(t)]
            hh = 1
            while hh < t:
                step = t // (2 * hh)
                for g in range(0, t, 2 * hh):
                    for j in range(hh):
                        wr, wi = twr[j * step], twi[j * step]
                        lo, hi = g + j, g + j + hh
                        br, bi = xr[hi], xi[hi]
                        tr = shr(mul(br, wr) - mul(bi, wi), qm)
                        ti = shr(mul(br, wi) + mul(bi, wr), qm)
                        a, b = xr[lo], xi[lo]
                        xr[lo], xi[lo] = shr(a + tr, 1), shr(b + ti, 1)
                        xr[hi], xi[hi] = shr(a - tr, 1), shr(b - ti, 1)
                nbfly += t // 2
                hh <<= 1
            return xr, xi

        ar, ai = (list(v) for v in axis_lines(ctx, ar, ai, geom, h, fft_line))   # lines along axis h (§7.2)
    ctx.inst.hit("bridge.middle")
    ctx.inst.hit("basefft.butterfly", nbfly)
    return FxVec([shr(v, up) for v in ar], [shr(v, up) for v in ai], q)


def _bluestein(ctx, U: FxVec, geom, P: int) -> FxVec:
    from ..middle3.bluestein import bluestein_middle_dft    # M3 backend (lazy import)
    return bluestein_middle_dft(ctx, U, geom, P)


def _walsh(ctx, U: FxVec, geom, P: int) -> FxVec:
    from ..walsh.fft import walsh_middle_dft                 # M9 backend (lazy import)
    return walsh_middle_dft(ctx, U, geom, P)


MIDDLE_BACKENDS = {"direct": direct_middle_dft, "bluestein": _bluestein, "walsh": _walsh}


def middle_dft(ctx, U: FxVec, geom, P: int) -> FxVec:
    """Dispatch to the backend named by ``ctx.schedule.bridge_middle``."""
    return MIDDLE_BACKENDS[ctx.schedule.bridge_middle](ctx, U, geom, P)
