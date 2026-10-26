"""Signed radix Kronecker packing (MS Lemma 6.2 ``lem:kronecker``) and the overlap-add row spread
of MS Theorem 6.3 ``thm:spread``, extended to complex (modulated) filters (drop-in, r2 §8:
"complex filters mean ... four real products per block").
"""

from __future__ import annotations

from typing import Callable

from .bits import digits_to_int, int_to_digits
from .checks import RuntimeCheckError, require

__all__ = ["pack", "unpack", "spread_row"]


def pack(coeffs, B: int) -> int:
    """Pack_B(a_0..a_{s-1}) = sum_j a_j 2^{jB} (MS eq. (pack-def)) for signed a_j with
    |a_j| < 2^{B-1}.  Exact, by a linear streaming scan: two's-complement blocks
    d_j = (a_j + g_j) mod 2^B with carries g_{j+1} = (a_j + g_j - d_j)/2^B in {-1, 0}; the value is
    sum d_j 2^{jB} + g_s 2^{sB}, assembled by one bit-string conversion (complement-and-increment
    of the blocks for a negative value; :mod:`subnlogn.bits`)."""
    n = len(coeffs)
    if n == 0:
        return 0
    top, half = 1 << B, 1 << (B - 1)
    g, blocks = 0, []
    for a in coeffs:
        if not -half < a < half:
            raise ValueError("Pack_B needs |a_j| < 2^(B-1)")
        d = (a + g) & (top - 1)          # = (a + g) mod 2^B (a mask: linear, class C)
        g = (a + g - d) >> B
        blocks.append(d)
    if g == 0:
        return digits_to_int(blocks, B)
    c, comp = 1, []                      # 2^{sB} - sum d_j 2^{jB}: complement and increment
    for d in blocks:
        v = top - 1 - d + c
        comp.append(v & (top - 1))
        c = v >> B
    require(c == 0, "Pack_B: complement-and-increment carried out of the s blocks (MS eq. (pack-def))")
    return -digits_to_int(comp, B)


def unpack(T: int, m: int, B: int) -> list[int]:
    """Recover c_0..c_{m-1} with |c_k| < 2^{B-1} from T = sum_k c_k 2^{kB} (MS Lemma 6.2 (ii)):
    centred residues modulo 2^B by one linear scan over the blocks of |T| (sign-extended two's
    complement, carries in {0, 1}; the final carry cancels the sign extension, asserted).  This is
    the lemma's unique decomposition."""
    top, half = 1 << B, 1 << (B - 1)
    if 2 * abs(T) >= 1 << (B * m):
        raise ValueError("T does not fit in m signed slots of B bits")
    eps = -1 if T < 0 else 0
    q = int_to_digits(-T if eps else T, B, m)
    if eps:
        c, comp = 1, []
        for d in q:
            v = top - 1 - d + c
            comp.append(v & (top - 1))
            c = v >> B
        q = comp
    rho, out = 0, []
    for d in q:
        h = ((d + rho + half) & (top - 1)) - half     # centred residue mod 2^B by a mask
        rho = (d + rho - h) >> B
        if rho not in (0, 1):
            raise RuntimeCheckError("unpack: extraction carry left {0, 1} (MS Lemma 6.2 (ii))")
        out.append(h)
    require(rho + eps == 0, "final carry does not cancel the sign extension (MS Lemma 6.2 (ii))")
    return out


def spread_row(v_re: list[int], v_im: list[int], f_re: tuple[int, ...], f_im: tuple[int, ...],
               F_re: int, F_im: int, offset: int, B: int, q: int,
               shr: Callable[[int, int], int], imul=None, inst=None) -> tuple[list[int], list[int]]:
    """One row of Step 1 (MS Thm 6.3) with a complex guarded filter.

    Input: row v (length r) with numerators at scale q (|coordinate| <= 2^{q+p}); filter taps
    f (length W~, scale q) with pre-packed integers F = Pack_B(f).  Overlap-add with block length
    W~: each block is packed (real and imaginary parts), multiplied by F_re and F_im (four exact
    integer products), unpacked into L_b + W~ - 1 exact linear-convolution coefficients at scale
    2q, combined into the complex result, and accumulated modulo r at output index
    (block_start + i - offset) mod r.  After all blocks every output entry is rounded ONCE from
    scale 2q to scale q (error <= sqrt(2)/2 2^-q per entry, MS eq. (spread-err)).
    """
    r = len(v_re)
    Wt = len(f_re)
    acc_re = [0] * r
    acc_im = [0] * r
    mul = imul if imul is not None else (lambda a, b: a * b)
    for start in range(0, r, Wt):
        Lb = min(Wt, r - start)
        Xr = pack(v_re[start:start + Lb], B)
        Xi = pack(v_im[start:start + Lb], B)
        nout = Lb + Wt - 1
        prr = unpack(mul(Xr, F_re), nout, B)
        pii = unpack(mul(Xi, F_im), nout, B)
        pri = unpack(mul(Xr, F_im), nout, B)
        pir = unpack(mul(Xi, F_re), nout, B)
        if inst is not None:                        # the four packed products just executed
            inst.hit("kron.product", 4)
        base = start - offset
        for i in range(nout):
            k = (base + i) % r
            acc_re[k] += prr[i] - pii[i]
            acc_im[k] += pri[i] + pir[i]
    return [shr(a, q) for a in acc_re], [shr(a, q) for a in acc_im]
