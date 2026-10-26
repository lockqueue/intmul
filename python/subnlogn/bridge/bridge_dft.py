"""The d-dimensional CRT-free bridge DFT (M2): F_R x via spreading, a middle tensor DFT and
ordered deconvolution, on the SAME power-of-two grid R = t_1 ... t_d (no CRT, no resampling, no
grid expansion).

Sources: Lemma A (r2 Thm 1, eq. (2.2)-(2.7); r3 eq. (3.5)-(3.7)):

    F_t S_2 S_3 ... S_d = A_2 A_3 ... A_d F_R      (operators compose right to left),

Lemma B (negative half-bin carrier, retained aliases m in {0, 1}, uniform cyclic solver), and the
Lemma C budget (r3 eq. (2.3), §5): P = 2p + 6K + 128, w = P, m = P (or r2's constants, see
:meth:`Schedule.bridge_params`).  Pipeline (r3 §5.1-5.7):

1. exact power-of-two normalization x' = x / 2^e (r2 §5.1 under the faithful r2 profile,
   r3 §5.1 under the r3 profile; :func:`normalization_exponent`);
2. spreading S_d, ..., S_2 (chronological; :mod:`.spread`);
3. middle tensor DFT through the pluggable interface (:mod:`.middle`; M2 uses ``direct``);
4. reorder storage (u_1 least significant) to natural frequency k = Phi(u) (u_1 most significant), an
   axis-order reversal (``Schedule.bridge_movement``: reference index map, or floor(d/2) Lemma 12 exchanges,
   SPEC §7.2; :mod:`.movement`; the spreading's axis exposures and the middles' storage <-> tensor reversals
   follow the same switch);
5. deconvolution B_2^{-1}, ..., B_d^{-1} (chronological; :mod:`.deconv`);
6. exact rescaling by X and one nearest rounding to C~_{p+2}.

All records live on the grid q = P + 2 (finer than r3's 2^-P, so each rounding is < 2^-P).

With ``ctx.capture`` a dict, the call stores (scale q, normalized domain x' = x/X): ``bridge_U``
(spread array, storage order), ``bridge_Ymid`` (middle output, frequency order), ``bridge_Ydeconv``
({h: Y after B_h^{-1}}), ``bridge_Znorm`` (= bridge_Ydeconv[d]), ``bridge_e`` (X = 2^e) and
``bridge_params`` ((P, w, m, geom)).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..checks import require
from ..fixedpoint import FxVec, Rounding
from .deconv import deconv_axis
from .geometry import BridgeGeometry, balanced_factors
from .middle import middle_dft
from .movement import storage_to_tensor
from .spread import spread_axis

__all__ = ["bridge_dft", "BridgeCertificate", "bridge_certificate", "bridge_geometry",
           "normalization_exponent"]

_SQRT2_UP = Fraction(99, 70)          # 99/70 = 1.41428... > sqrt(2)
_FINAL = Fraction(17678, 100000)      # > sqrt(2)/8


def bridge_geometry(K: int, d: int) -> BridgeGeometry:
    return BridgeGeometry(balanced_factors(K, d))


def normalization_exponent(x: FxVec, p: int, geom: BridgeGeometry, profile: str) -> int:
    """Exponent e of the exact power-of-two input normalization x' = x / 2^e.

    profile "r2" (faithful default; r2 §5.1): with X = max(1, ||x||),
    an integer H with X <= 2^H < 4X ("twice the next power of two above max(1, max|Re|, max|Im|)"),
    and S = 2^{H + ceil(lg(R/t_1)/2) + 4}, so 16 sqrt(D) X <= S < 128 sqrt(D) X (r2 (5.1)-(5.2)) and
    every spread array has norm <= 1/8 (r2 §5.2).
    profile "r3" (r3 §5.1): X = 2^e with ||x|| <= X <= 4A, e = max(0, ceil(lg(2 max|coord|)))."""
    mc = max([abs(v) for v in x.re] + [abs(v) for v in x.im] + [0])
    if profile == "r2":
        # next power of two above m = max(1, mc 2^-(p+2)): 2^h0 >= m > 2^(h0-1) (h0 = 0 if m <= 1)
        h0 = max(0, (mc - 1).bit_length() - (p + 2)) if mc > 0 else 0
        H = h0 + 1
        Q = geom.R // geom.tt(1)
        half_lg = ((Q.bit_length() - 1) + 1) // 2          # ceil(lg(Q)/2), Q a power of two
        return H + half_lg + 4
    return max(0, (mc - 1).bit_length() - (p + 1)) if mc > 0 else 0


def bridge_dft(ctx, x: FxVec, R: int, p: int, d: int, geom: BridgeGeometry | None = None) -> FxVec:
    """F_R x by the d-dimensional bridge (see module docstring).  x on C~_{p+2}; result on
    C~_{p+2} in natural frequency order.  Contract (r3 (2.4)): ||out - F_R x|| <= 2^-p max(1,||x||)."""
    from ..hierarchy import assert_improved_allowed
    assert_improved_allowed(ctx)
    if x.q != p + 2 or len(x) != R:
        raise ValueError("bridge_dft expects x on C~_(p+2) of length R")
    K = R.bit_length() - 1
    if geom is None:
        geom = bridge_geometry(K, d)
    if geom.R != R:
        raise ValueError("geometry does not match R")
    if p < max(8, K):
        raise ValueError("Lemma C needs p >= max(8, K)")
    if ctx.schedule.rounding is Rounding.TRUNC:
        raise ValueError("the bridge front end uses nearest rounding; its certificate assumes it")
    P, w, m = ctx.schedule.bridge_params(p, K, geom.d)
    q = P + 2
    shr = ctx.shr
    ctx.inst.hit("bridge.dft")
    e = normalization_exponent(x, p, geom, ctx.schedule.bridge_constants)
    s0 = q - (p + 2 + e)
    if s0 < 0:
        raise AssertionError("P too small for exact normalization")
    U = FxVec([v << s0 for v in x.re], [v << s0 for v in x.im], q)
    # 2. spreading, chronological order h = d, ..., 2.
    for h in range(geom.d, 1, -1):
        U = spread_axis(ctx, U, geom, h, m, w)
    ctx.inst.height("bridge.spread", U.re, U.im)
    if ctx.schedule.bridge_constants == "r2":
        # r2 §5.2: every completed computed spread array has norm <= 1/8 (disk margin for the
        # middle transform).  Exact integer test.
        lim = 1 << (2 * q - 6)
        require(all(a * a + b * b <= lim for a, b in zip(U.re, U.im)),
                "spread array left the 1/8 disk (r2 §5.2; SPEC v1.2 §5.10)")
    cap = ctx.capture        # stage-wise error checks (tests/stage_checks.py); None = no capture
    if cap is not None:
        cap["bridge_U"] = U                       # spread array after all axes (storage order)
    # 3. middle tensor DFT (pluggable).
    Yst = middle_dft(ctx, U, geom, P)
    # 4. storage -> natural frequency order k = Phi(u) (u_1 most significant): the axis-order reversal, by
    #    floor(d/2) Lemma 12 exchanges ("lemma12", SPEC §7.2) or the reference index map ("index").
    yr, yi = storage_to_tensor(ctx, Yst.re, Yst.im, geom)
    Y = FxVec(list(yr), list(yi), q)
    if cap is not None:
        cap["bridge_Ymid"] = Y                    # middle output, natural frequency order
        cap["bridge_Ydeconv"] = {}                # h -> Y after B_h^{-1} (stage h)
    # 5. deconvolution, chronological order h = 2, ..., d.
    for h in range(2, geom.d + 1):
        Y = deconv_axis(ctx, Y, geom, h, w)
        if cap is not None:
            cap["bridge_Ydeconv"][h] = Y
    if ctx.capture is not None:
        ctx.capture["bridge_Znorm"] = Y
        ctx.capture["bridge_e"] = e
        ctx.capture["bridge_params"] = (P, w, m, geom)
    # 6. exact rescale by X = 2^e, one rounding to C~_{p+2}.
    s1 = q - e - (p + 2)
    return FxVec([shr(v, s1) for v in Y.re], [shr(v, s1) for v in Y.im], p + 2)


@dataclass(frozen=True)
class BridgeCertificate:
    """Error budget of one bridge call (exact rational upper bounds; absolute units).

    Normalized-domain terms (input x' = x/X, ||x'|| <= 1):
      spread  = 16 d (P+1) G eta              (r3 (5.4); G = sqrt(Q), Q = R/t_1, eta = 2^-P)
      middle  = 2.16 K 2^{-q_m} max(1, 2G) + sqrt(2)/2 2^{-q}   (direct backend, see .middle)
      alias   = 0.120 (d-1) 2^-w              (r3 (4.16))
      solver  = 64 Q eta sum_{h>=2} t_h       (r3 (4.21) per stage, propagated; cf. r3 (5.10))
      norm    = Q (spread + middle + alias) + solver          (r3 (5.10) with ||B_h^-1|| <= t_h)
    then pre_rounding = N norm with N = 2^e the normalization scale (r2 §5.1: N = S < 128 sqrt(Q) X;
    r3 §5.1: N = X <= 4A), total = pre_rounding + sqrt(2)/8 2^-p, and the contract
    2^-p max(1, ||x||) of r2 (2.10) / r3 (2.4)."""

    spread: Fraction
    middle: Fraction
    alias: Fraction
    solver: Fraction
    norm: Fraction
    X: int
    pre_rounding: Fraction
    total: Fraction
    contract: Fraction


def bridge_certificate(geom: BridgeGeometry, p: int, P: int, w: int, X: int, A: Fraction,
                       mid_guard: int = 16, middle_backend: str = "direct") -> BridgeCertificate:
    R, K, d = geom.R, geom.K, geom.d
    Q = R // geom.tt(1)
    kq = Q.bit_length() - 1
    G = Fraction(1 << (kq // 2)) * (_SQRT2_UP if kq % 2 else 1)
    eta = Fraction(1, 1 << P)
    q = P + 2
    qm = P + K + mid_guard
    spread = 16 * d * (P + 1) * G * eta
    if middle_backend == "direct":
        middle = Fraction(216, 100) * K * max(Fraction(1), 2 * G) / (1 << qm) + Fraction(70711, 100000) / (1 << q)
    elif middle_backend == "bluestein":
        # SPEC §5.9: (E_ring + 22) 2^-p_fft, E_ring = sqrt(2) M (3l + 1), M = R/r, p_fft = q
        r = geom.tt(d)
        ell = r.bit_length() - 1
        middle = (Fraction(141422, 100000) * (R // r) * (3 * ell + 1) + 22) / (1 << q)
    elif middle_backend == "walsh":
        # SPEC_WALSH §5.4, §6.2: direct complex tensor FFT, 12 l 2^-p_fft, p_fft = q (no M factor)
        ell = geom.tt(d).bit_length() - 1
        middle = Fraction(12 * ell, 1 << q)
    else:
        raise ValueError(middle_backend)
    alias = Fraction(120, 1000) * (d - 1) / (1 << w)
    solver = 64 * Q * eta * sum(geom.tt(h) for h in range(2, d + 1))
    norm = Q * (spread + middle + alias) + solver
    if norm >= 1:
        raise AssertionError("intermediate-norm induction (r3 §5.7) needs the normalized error < 1")
    pre = X * norm
    final = _FINAL / (1 << p)
    return BridgeCertificate(spread, middle, alias, solver, norm, X, pre, pre + final, A / (1 << p))
