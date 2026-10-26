"""Coefficient twist (Pr §9.4, SPEC §5.8) and the positive tensor DFT by Bluestein's chirp identity
(Lemma 21 eq. (36) with the conjugation bars of the PDF, §9.5; SPEC §5.9, reading R2), and the
bridge middle backend ``"bluestein"`` (M3, direct layers).

Scalar tensors live on prod_{i<=d} Z/t_i with t_d = r (= 2^l) and are stored in TENSOR order:
index T(c) = sum_i c_i prod_{j>i} t_j (axis 1 most significant, axis d = the polynomial
coefficient index).  iota identifies such a tensor with M = R/r records of R_r (descriptor-only).

complex_convolution(f, g) ~ M_C(f, g) = (f * g)/R (cyclic in all d axes):
    f1 = Q_p(theta+_{c_d} f), g1 = Q_p(theta+_{c_d} g)     (twist x_d -> zeta y, zeta = e^{pi i/r})
    h1 = Prop 18 M_r(iota f1, iota g1)                       (width w + lg M; assert ||h1|| < 0.701)
    return Q_p(theta-_{c_d} iota^{-1} h1)                     (untwist)
Error < (E_ring + 12) 2^-p, E_ring = sqrt(2) M (3l + 1) [Pr L4457-4500].

tensor_positive_dft(x) ~ F_t^+ x = a (conj(a) * (a x)) / R, a_j = e^{pi i sum_i j_i^2/t_i} = zeta^{E_j},
E_j = sum_i j_i^2 (r/t_i) mod 2r:  x0 = Q_p(a x); y0 = complex_convolution(conj(a), x0);
return Q_p(a y0).  Requires ||x|| <= 0.6; error < (E_ring + 22) 2^-p.  The kernel is conj(a): the
bar is essential (reading R2).  One disk-preserving 2r-entry phase table serves chirp and twists.
"""

from __future__ import annotations

from fractions import Fraction

from ..checks import RuntimeCheckError, require
from ..fixedpoint import FxVec, shr_trunc
from .prop18 import normalized_ring_convolution
from .synth import Synth

__all__ = ["complex_convolution", "tensor_positive_dft", "bluestein_middle_dft", "trunc_cmul"]

_NORM_0701_SQ = Fraction(701, 1000) ** 2


def trunc_cmul(ar: int, ai: int, br: int, bi: int, p: int, mul=None) -> tuple[int, int]:
    """Q_p of a product of two grid-p complex numbers: exact product at scale 2p, each component
    truncated toward zero (disk-preserving phase products, SPEC §1.4).  ``mul``: the word-scale
    multiplier for the separable chirp/twist products (``Ctx.word_mul``; br_r2 §6.3, (6.5): "with the
    independent O(N lg N) multiplier"); None = Python's ``*``."""
    if mul is None:
        return shr_trunc(ar * br - ai * bi, p), shr_trunc(ar * bi + ai * br, p)
    return shr_trunc(mul(ar, br) - mul(ai, bi), p), shr_trunc(mul(ar, bi) + mul(ai, br), p)


def _tables(r: int, p: int):
    """The disk-preserving 2r-entry phase table theta[k] ~ e^{pi i k/r} (SPEC §5.9)."""
    from ..certified import phase_table
    return phase_table(r, p)


def complex_convolution(f, g, t: tuple[int, ...], p: int, sy: Synth, mul=None, inst=None, th=None,
                        disk: Fraction | None = None, wmul=None):
    """M_C(f, g) per SPEC §5.8.  f, g: lists of (re, im) numerators (grid 2^-p) in tensor order.
    The Prop 18 output (width p + 2 + lg M) is narrowed by sign extension only after its disk test:
    norm < 0.701 [Pr L4457-4500], or ``disk`` when the caller proves a sharper radius (the bridge
    under r2 pre-scaling: 1/8 + C18 v, SPEC v1.2 §5.10)."""
    r = t[-1]
    if th is None:
        th = _tables(r, p)
    R = len(f)
    M = R // r

    def twist(z, sign):
        out = []
        for idx, (zr, zi) in enumerate(z):
            k = idx % r                                   # c_d = the coefficient index
            wr, wi = th[k]
            if sign < 0:
                wi = -wi                                  # theta-_k = conj(theta+_k)
            out.append(trunc_cmul(zr, zi, wr, wi, p, wmul))
        return out

    f1, g1 = twist(f, +1), twist(g, +1)
    rec = lambda z: [([a for a, _ in z[m * r:(m + 1) * r]], [b for _, b in z[m * r:(m + 1) * r]])
                     for m in range(M)]
    h1, mM = normalized_ring_convolution(rec(f1), rec(g1), sy, p, mul, inst)
    lim = (_NORM_0701_SQ if disk is None else disk * disk) * (1 << (2 * p))
    for re, im in h1:
        for a, b in zip(re, im):
            if not a * a + b * b <= lim:
                raise RuntimeCheckError("Prop 18 output left its disk before narrowing (SPEC §5.10)")
    flat = [(a, b) for re, im in h1 for a, b in zip(re, im)]     # narrowing: values unchanged
    if inst is not None:
        inst.hit("bluestein.complex_convolution")
    return twist(flat, -1)


def tensor_positive_dft(x, t: tuple[int, ...], p: int, K: int = 1, mul=None, inst=None, layer=None,
                        movement=None, disk: Fraction | None = None, wmul=None):
    """F_t^+ x by the chirp identity (SPEC §5.9).  x: list of (re, im) numerators, tensor order,
    ||x|| <= 0.6 (asserted exactly).  Returns the same layout (tensor order = 1D frequency order
    Phi of the bridge)."""
    r = t[-1]
    ell = r.bit_length() - 1
    lim = Fraction(36, 100) * (1 << (2 * p))
    require(all(a * a + b * b <= lim for a, b in x), "Bluestein input must satisfy ||x|| <= 0.6 (SPEC §5.9)")
    th = _tables(r, p)
    sy = Synth(tuple(t[:-1]), ell, K, layer=layer, movement=movement, inst=inst)
    R = len(x)
    strides = []
    s = 1
    for ti in reversed(t):
        strides.append(s)
        s *= ti
    strides.reverse()

    def chirp(idx):
        E = 0
        for ti, st in zip(t, strides):
            c = (idx // st) % ti
            E += c * c * (r // ti)
        return th[E % (2 * r)]

    a = [chirp(i) for i in range(R)]
    x0 = [trunc_cmul(xr, xi, ar, ai, p, wmul) for (xr, xi), (ar, ai) in zip(x, a)]
    abar = [(ar, -ai) for ar, ai in a]
    y0 = complex_convolution(abar, x0, t, p, sy, mul, inst, th, disk=disk, wmul=wmul)
    if inst is not None:
        inst.hit("bluestein.tensor_dft")
    return [trunc_cmul(yr, yi, ar, ai, p, wmul) for (yr, yi), (ar, ai) in zip(y0, a)]


def bluestein_middle_dft(ctx, U: FxVec, geom, P: int) -> FxVec:
    """Bridge middle backend ``"bluestein"`` (M3, direct layers): F_t U with p_fft = q = U.q
    (SPEC §5.10).  Converts the bridge storage layout (index sum c_i A_i) to tensor order and back: the
    axis-order reversal, by floor(d/2) Lemma 12 exchanges under ``bridge_movement="lemma12"`` (SPEC §7.2) or by
    the reference index map (``"index"``, DEVIATIONS D9) -- :mod:`subnlogn.bridge.movement`."""
    from ..bridge.movement import storage_to_tensor, tensor_to_storage
    q = U.q
    t = geom.t
    R = geom.R
    ell = t[-1].bit_length() - 1
    K = ctx.schedule.chunk_bits
    if geom.d < 2 or ell < 2 or not 1 <= K <= ell - 1:
        raise ValueError("Lemma 16 needs d >= 2, r = 2^l with l >= 2 and 1 <= K <= l - 1")
    xr, xi = storage_to_tensor(ctx, U.re, U.im, geom)
    x = list(zip(xr, xi))
    from ..m6.engine import movement_from_schedule
    disk = None
    if ctx.schedule.bridge_constants == "r2":
        # completed spreads have norm <= 1/8, so the scaled Prop 18 result has norm
        # <= 1/8 + C18 v, C18 = sqrt(2) M (3l + 1) < (99/70) M (3l + 1), v = 2^-q (SPEC v1.2 §5.10)
        M = R // t[-1]
        disk = Fraction(1, 8) + Fraction(99, 70) * M * (3 * ell + 1) / (1 << q)
    y = tensor_positive_dft(x, t, q, K, ctx.product_mul(q), ctx.inst, layer=prop14_layer(ctx, geom.d),
                            wmul=ctx.word_mul(),
                            movement=movement_from_schedule(ctx), disk=disk)
    ctx.inst.hit("bridge.middle")
    yr, yi = tensor_to_storage(ctx, [v[0] for v in y], [v[1] for v in y], geom)
    require(len(yr) == R, "Bluestein middle returned a stream of the wrong length (SPEC §5.10)")
    return FxVec(list(yr), list(yi), q)


def prop14_layer(ctx, d: int):
    """The Proposition 14 layer selected by the schedule: None = base case (M3, SPEC §5.11), or the
    complex-network engine (M6, SPEC §4.5-4.7) with the schedule's networks and LayerPolicy
    (``schedule.layer``, SPEC v1.1 §4.0) and Lemma 13 basis changes (SPEC §4.3); d = the tensor
    dimension (leaf rule, q0, k0, Delta)."""
    from ..m6.cnet import simultaneous_H0_network
    from ..m6.engine import engine_from_schedule
    engine = engine_from_schedule(ctx, d)
    if engine is None:
        return None

    def layer(recs, sel_bits, scale, p, truncate=True, *, K=1, rho=0):
        ctx.inst.hit("prop14.network_layer")
        return simultaneous_H0_network(recs, sel_bits, scale, p, engine, K=K, rho=rho,
                                       truncate=truncate, check_disk=truncate)
    return layer
