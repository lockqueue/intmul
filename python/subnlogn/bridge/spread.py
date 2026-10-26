"""Bridge spreading S_d, S_{d-1}, ..., S_2 (Lemma A: r2 §3.1 eq. (3.1)-(3.2),
r3 eq. (3.1)) with folded MODULATED kernels (Lemma B: r2 §4.7, r3 §5.2).

Axis h >= 2 is spread line by line.  A line fixes every coordinate except the axis-h digit; its
fractional shift is delta_h = (sum_{i<h} j_i A_i) / A_h, computed from the ORIGINAL lower digits
(they are still unspread because axes are processed in the chronological order d, ..., 2).  The lines
are reached by :func:`subnlogn.bridge.movement.axis_lines`: index maps (``bridge_movement="index"``) or
"expose axis h by one nonadjacent swap with the innermost axis and back" (SPEC §7.2; Lemma 12, ``"lemma12"``),
the digits of the other axes (hence delta_h) decoded from the block address.  The
line operation is the cyclic correlation U_k = sum_j v_j H_{h,delta}(j - k) with
H_{h,delta}(a) = sum_l g_h(a + delta - l t_h),  g_h(s) = e^{-pi i s/t_h} sinc(s) e^{-pi s^2/alpha^2},
alpha = 2 sqrt(w ln2/pi),  truncated to |e| <= m and folded modulo t_h (MS §6.1 objects (b)-(d)).
It is computed by exact signed-Kronecker overlap-add and ONE rounding per output (MS Thm 6.3,
r3 §5.2: "Exact signed-Kronecker convolution followed by one final rounding").
"""

from __future__ import annotations

from fractions import Fraction

from ..fixedpoint import FxVec
from ..kronecker import pack, spread_row
from ..tables import FilterRow, filter_row
from .movement import axis_lines

__all__ = ["bridge_filter", "spread_axis"]


def bridge_filter(ctx, delta: Fraction, t: int, m: int, w: int, q: int) -> FilterRow:
    """Folded modulated filter of one bridge line (cached in ``ctx.tables``)."""
    key = ("bridge_filter", delta, t, m, w, q)
    f = ctx.tables.get(key)
    if f is None:
        f = filter_row(delta, t, m, w, q, carrier=-1)
        ctx.tables[key] = f
    return f


def spread_axis(ctx, U: FxVec, geom, h: int, m: int, w: int) -> FxVec:
    """Apply S_h to the storage-layout array U (scale q = U.q).  Returns a new FxVec (scale q)."""
    q = U.q
    t = geom.tt(h)
    shr = ctx.shr
    # Slot width 4P + 16 (SPEC v1.2 §5.10, §7.2; 16(2P+1) 2^{2q} < 2^{4P+15} bounds
    # every real/complex coefficient and overlap sum strictly below half the slot radix), with m = P.
    # The actual integer bound (implementer spec r1 §7.4: every coefficient <= Amax * Hsum < 2^{B-2})
    # is asserted to fit.
    B_slot = 4 * m + 16
    amax = max([abs(v) for v in U.re] + [abs(v) for v in U.im] + [1])
    packed: dict = {}
    mul = ctx.product_mul(q)                 # packed overlap-add products (D1 / hierarchy)

    def line(digits, vr, vi):
        # delta_h from the ORIGINAL lower digits j_1..j_{h-1} of this line (r2 §3.1, r3 §3.1)
        delta = geom.delta(h, sum(digits[i] * geom.A(i) for i in range(1, h)))
        f = bridge_filter(ctx, delta, t, m, w, q)
        if delta not in packed:
            hsum = max(sum(abs(v) for v in f.taps_re), sum(abs(v) for v in f.taps_im), 1)
            if (amax * hsum).bit_length() + 2 > B_slot:
                raise AssertionError("overlap-add coefficients exceed the 4P + 16-bit slot")
            packed[delta] = (B_slot, pack(f.taps_re, B_slot), pack(f.taps_im, B_slot))
        B, Fr, Fi = packed[delta]
        return spread_row(vr, vi, f.taps_re, f.taps_im, Fr, Fi, f.offset, B, q, shr, mul, ctx.inst)

    out_re, out_im = axis_lines(ctx, U.re, U.im, geom, h, line)
    ctx.inst.hit("bridge.spread_axis")
    return FxVec(list(out_re), list(out_im), q)
