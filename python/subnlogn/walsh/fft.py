"""The direct complex tensor FFT of the Walsh route and the bridge middle backend ``"walsh"``
(SPEC_WALSH §5-§6; r5 §7.3, l.1294-1336, eqs. (7.8)-(7.9)).

Exact counterpart: the normalized positive tensor DFT (F+_t z)_j = (1/R) sum_k z_k exp(+2 pi i sum_i j_i k_i/t_i)
on t = (t_1..t_d), t_d = r = 2^ell, t_i in {r/2, r}.  Records = lines of the last axis (r contiguous
coefficients); the m0 = sum_{i<d} lg t_i record-address bits hold axes 1..d-1, axis 1 most significant,
each axis high bit first (tensor order).  Precision p = p_fft (SPEC §5.10); Q_p = truncation toward zero.

Order of operations (SPEC_WALSH §5.1): (1) normalized radix-2 DIF FFT of every record, natural order
restored inside the record; (2) the positional map L (§4, CNOT stages); (3) record-axis DIF rounds at named
positions h0 = ell-1, ..., 0 (SPEC §5.3's schedule): chunk rounds b <= h0 <= ell-2 through Prop 14 on chunk
group j = floor((ell-2-h0)/h) + 1 with offset rho = (h0 - b) mod h, prefix rounds (h0 = ell-1 on the long
axes, h0 < b on all axes) by exact H0 factors and ONE Q_p; each round z -> Q_p(theta ⊙ Q_p(H z)) with ONE
combined twiddle per record, theta = th[(-E) mod 2r], E = -sum_i (2r/u_i) b_i k_i (R5 (7.8)); (4) the
unshuffle (LB)^-1 = B^-1 L^-1.  One shared table th = phase_table(r, p) (SPEC §5.9; Dev-W2) serves every
phase: last-axis twiddle e^{2 pi i k/u} = th[(2r/u) k mod 2r].

Error (SPEC_WALSH §5.4; R5 (7.9)): every round and every last-axis level has local error < 6 2^-p on a disk
input; the exact maps are contractions and the positional maps exact, so ||F^ z - F z|| < 12 ell 2^-p.
``truncate=False`` runs the exact counterpart (no Q_p; phases must then be exact fourth roots, i.e. r <= 4
and t_i <= 4): literally the exact DFT over Z[i, 1/2] (SPEC_WALSH §8, W-T9).
"""

from __future__ import annotations

from ..checks import require
from ..certified import phase_table
from ..fixedpoint import FxVec, shr_trunc
from ..m6.prop14 import map_records_with_address, simultaneous_H0, times_i_power
from .gadget import WalshCtx, assert_disk
from .positional import compile_layout, execute_positional_map

__all__ = ["last_axis_fft", "twiddle_index", "tensor_fft_walsh", "walsh_engine", "walsh_middle_dft"]


def _log2(x: int) -> int:
    k = x.bit_length() - 1
    if x < 1 or 1 << k != x:
        raise ValueError(f"{x} is not a power of two")
    return k


def _phase(re: list[int], im: list[int], th_k, p: int, truncate: bool, mul=None):
    """Multiply a coefficient list by the table phase th_k: Q_p of the exact product (truncate), or, in
    exact mode, by the exact fourth root it must be (SPEC_WALSH §5.2: exact fourth roots hit)."""
    tr, ti = th_k
    if truncate:
        if mul is None:                              # unit tests; the pipeline passes Ctx.word_mul
            return ([shr_trunc(a * tr - b * ti, p) for a, b in zip(re, im)],
                    [shr_trunc(a * ti + b * tr, p) for a, b in zip(re, im)])
        return ([shr_trunc(mul(a, tr) - mul(b, ti), p) for a, b in zip(re, im)],
                [shr_trunc(mul(a, ti) + mul(b, tr), p) for a, b in zip(re, im)])
    one = 1 << p
    k = {(one, 0): 0, (0, one): 1, (-one, 0): 2, (0, -one): 3}.get((tr, ti))
    if k is None:
        raise ValueError("exact mode needs phases that are exact fourth roots (r <= 4, t_i <= 4)")
    return times_i_power(re, im, k)


def last_axis_fft(re: list[int], im: list[int], p: int, th, truncate: bool = True, mul=None):
    """Normalized positive radix-2 DIF FFT of one record of r coefficients, natural order out
    (SPEC_WALSH §5.3 ``last_axis_fft``): top output Q_p((x + y)/2), bottom output
    Q_p(th[(2r/u) k] Q_p((x - y)/2)); the final bit reversal is an index map (Dev-W3).  Returns the record
    on the grid p (or, with truncate=False, the exact record at scale p + ell)."""
    r = len(re)
    ell = _log2(r)
    ar, ai = list(re), list(im)
    for v in range(ell - 1, -1, -1):
        u = 1 << (v + 1)
        half, step = u >> 1, (2 * r) // u
        for base in range(0, r, u):
            for k in range(half):
                i0, i1 = base + k, base + k + half
                sr, si = ar[i0] + ar[i1], ai[i0] + ai[i1]
                dr, di = ar[i0] - ar[i1], ai[i0] - ai[i1]
                if truncate:
                    sr, si, dr, di = shr_trunc(sr, 1), shr_trunc(si, 1), shr_trunc(dr, 1), shr_trunc(di, 1)
                (dr,), (di,) = _phase([dr], [di], th[(step * k) % (2 * r)], p, truncate, mul)
                ar[i0], ai[i0], ar[i1], ai[i1] = sr, si, dr, di
    rev = [int(format(j, f"0{ell}b")[::-1], 2) if ell else 0 for j in range(r)]
    return [ar[rev[j]] for j in range(r)], [ai[rev[j]] for j in range(r)]


def twiddle_index(addr: int, h0: int, axes, ell: int, ebit: dict) -> int:
    """(-E) mod 2r for the record at address ``addr`` in the round at named position h0 (R5 (7.8); SPEC
    §5.3 eq. (29)): sum_i (2r/u_i) b_i k_i with u_i = 2^(h0+1), b_i = the current bit at named slot
    (i, h0), k_i = sum_{v<h0} 2^v bit(i, v); ``ebit`` maps named slots to engine bit positions after L."""
    tot, sh = 0, ell - h0
    for i in axes:
        if (addr >> ebit[(i, h0)]) & 1:
            k = 0
            for v in range(h0):
                k |= ((addr >> ebit[(i, v)]) & 1) << v
            tot += k << sh
    return tot % (2 << ell)


def _hadamard_exact(recs: list, ebits) -> list:
    """Unnormalized exact butterflies (u + v, u - v) on each engine bit in ``ebits`` (scale + len)."""
    out = list(recs)
    for b in ebits:
        m = 1 << b
        for x in range(len(out)):
            if not x & m:
                (ar, ai), (br, bi) = out[x], out[x | m]
                out[x] = ([u + v for u, v in zip(ar, br)], [u + v for u, v in zip(ai, bi)])
                out[x | m] = ([u - v for u, v in zip(ar, br)], [u - v for u, v in zip(ai, bi)])
    return out


def tensor_fft_walsh(recs: list, t, p: int, wctx: WalshCtx, truncate: bool = True):
    """F+_t of a complete tensor stored as records (SPEC_WALSH §5.3 ``tensor_fft_walsh``; drop-in for SPEC
    §5.9 ``tensor_positive_dft``).  ``recs[a]`` = (re, im) numerators (grid 2^-p, disk-valued) of the last-
    axis line at record address a (tensor order).  Returns (records, scale): natural frequency order on
    every axis, disk grid at p (scale = p), error < 12 ell 2^-p; or the exact transform (truncate=False)."""
    t = tuple(t)
    d, r = len(t), t[-1]
    ell = _log2(r)
    h = wctx.h
    widths = [_log2(ti) for ti in t[:-1]]
    m0 = sum(widths)
    if d < 2 or ell < 2 or not 1 <= h <= ell - 1 or any(a not in (ell - 1, ell) for a in widths):
        raise ValueError("the Walsh middle needs d >= 2, ell >= 2, 1 <= h <= ell - 1, t_i in {r/2, r}")
    if len(recs) != 1 << m0 or any(len(re) != r or len(im) != r for re, im in recs):
        raise ValueError("tensor_fft_walsh: records must form the complete tensor")
    if truncate:
        assert_disk(recs, p)
    th = phase_table(r, p)
    recs = [last_axis_fft(re, im, p, th, truncate, wctx.mul) for re, im in recs]  # (1)
    wctx.hit("bit_reversal", len(recs))
    wctx.hit("phase", len(recs) * (r // 2) * ell)
    scale = p if truncate else p + ell
    L, B, U, new, b, q = compile_layout(widths, ell, h)
    ebit = {s: m0 - 1 - pos for s, pos in new.items()}
    recs = execute_positional_map(recs, L, scale, wctx)                           # (2)
    for h0 in range(ell - 1, -1, -1):                                             # (3)
        axes = [i for i, a in enumerate(widths) if h0 < a]
        if not axes:
            continue
        sel = [ebit[(i, h0)] for i in axes]
        if b <= h0 <= ell - 2:                    # chunk round: Prop 14 returns Q_p(H x)
            recs, scale = simultaneous_H0(recs, sel, scale, p, wctx.engine, K=h, rho=(h0 - b) % h,
                                          truncate=truncate, check_disk=truncate)
            wctx.hit("chunk_round")
        else:                                     # prefix round: exact H0 on each slot, ONE Q_p
            recs = _hadamard_exact(recs, sel)
            scale += len(sel)
            if truncate:
                s = scale - p
                recs = [([shr_trunc(v, s) for v in re], [shr_trunc(v, s) for v in im]) for re, im in recs]
                scale = p
            wctx.hit("prefix_round")
        recs = map_records_with_address(recs, lambda a, rec: _phase(
            rec[0], rec[1], th[twiddle_index(a, h0, axes, ell, ebit)], p, truncate, wctx.mul))
        wctx.hit("phase", len(recs))
    recs = execute_positional_map(recs, U, scale, wctx)                           # (4)
    if truncate:
        assert_disk(recs, p)
    return recs, scale


def walsh_engine(ctx, d: int):
    """The Prop 14 engine selected by the schedule, as in ``middle3.bluestein.prop14_layer``:
    ``prop14_layer == "base"`` -> None (base case); ``"network"`` -> the network engine over the
    schedule's test networks with ``schedule.layer`` (SPEC v1.1 §4.0), d = the tensor dimension, and
    Lemma 13 basis changes with Lemma 12 swaps on the bit network (SPEC §4.3; ``m6.engine``).  The
    Walsh wrapper never replaces those internal basis changes (SPEC_WALSH §1.2)."""
    from ..m6.engine import engine_from_schedule
    return engine_from_schedule(ctx, d)


def walsh_middle_dft(ctx, U: FxVec, geom, P: int) -> FxVec:
    """Bridge middle backend ``"walsh"`` (SPEC_WALSH §6.1): F_t U with p_fft = q = U.q (SPEC §5.10).  The
    bridge storage layout (index sum c_i A_i) is converted to tensor order and back: the axis-order reversal, by
    floor(d/2) Lemma 12 exchanges under ``bridge_movement="lemma12"`` (SPEC_WALSH §6.3, SPEC §7.2) or by the
    reference index map (``"index"``, DEVIATIONS D13) -- :mod:`subnlogn.bridge.movement`."""
    from ..bridge.movement import storage_to_tensor, tensor_to_storage
    q, t, R = U.q, tuple(geom.t), geom.R
    r = t[-1]
    flat_re, flat_im = storage_to_tensor(ctx, U.re, U.im, geom)
    recs = [(flat_re[a * r:(a + 1) * r], flat_im[a * r:(a + 1) * r]) for a in range(R // r)]
    wctx = WalshCtx(d=geom.d, h=ctx.schedule.chunk_bits, engine=walsh_engine(ctx, geom.d), inst=ctx.inst,
                    mul=ctx.word_mul())
    out, scale = tensor_fft_walsh(recs, t, q, wctx)
    require(scale == q, "Walsh tensor FFT must return scale q (SPEC_WALSH §6.1)")
    ctx.inst.hit("bridge.middle")
    flat_re = [v for re, _ in out for v in re]
    flat_im = [v for _, im in out for v in im]
    out_re, out_im = tensor_to_storage(ctx, flat_re, flat_im, geom)
    require(len(out_re) == R, "Walsh middle returned a stream of the wrong length (SPEC_WALSH §6.1)")
    return FxVec(list(out_re), list(out_im), q)
