"""Step 2 of FastDFT: the twisted Fourier-duality reduction (MS Theorem 3.1 ``thm:twisted``) with
the multiplication-free Synthetic FFT over C[y]/(y^r + 1) (MS eq. (syn-fft), Lemma 2.5
``lem:syn-fft``) and the odd-stride routing (MS eq. (odd-perm), Lemma 2.4(ii)).

Polynomials are rows: ``rows_re[j][k]``, ``rows_im[j][k]`` are the numerators (scale q) of the
coefficient of y^k in P_j(y).
"""

from __future__ import annotations

from typing import Callable

from .basefft import bit_reverse_perm
from .checks import require
from .routing import bit_reverse_tape

def _pymul(a: int, b: int) -> int:
    return a * b


__all__ = ["twist_rows", "nega_shift", "synthetic_fft", "synthetic_fft_tape", "odd_stride_route"]


def twist_rows(rows_re, rows_im, z_re, z_im, q: int, shr: Callable[[int, int], int],
               conjugate: bool, mul=None) -> tuple[list[list[int]], list[list[int]]]:
    """Pre-twist (Thm 3.1 step 1: multiply column k by zeta-bar_k) or post-twist (step 3: by the
    conjugate).  One RM_q per entry: error <= sqrt(2)/2 2^-q each (MS Lemma 6.5 proof).  ``mul`` is the
    word-scale multiplier (``Ctx.word_mul``: the hierarchy in products="hierarchy", MS Thm 7.1 pt 3 (a));
    None = Python's ``*`` (unit tests)."""
    if mul is None:
        mul = _pymul
    out_re, out_im = [], []
    for rr, ri in zip(rows_re, rows_im):
        nr, ni = [], []
        for k in range(len(rr)):
            wr = z_re[k]
            wi = -z_im[k] if conjugate else z_im[k]
            a, b = rr[k], ri[k]
            nr.append(shr(mul(a, wr) - mul(b, wi), q))
            ni.append(shr(mul(a, wi) + mul(b, wr), q))
        out_re.append(nr)
        out_im.append(ni)
    return out_re, out_im


def nega_shift(b: list[int], delta: int) -> list[int]:
    """Coefficients of y^delta B(y) mod (y^r + 1), 0 <= delta < 2r (MS Lemma 2.5 proof:
    b~_k = -b_{k+r-delta} for k < delta, b_{k-delta} for k >= delta).  Exact."""
    r = len(b)
    delta %= 2 * r
    sign = 1
    if delta >= r:
        delta -= r
        sign = -1
    if delta == 0:
        out = list(b)
    else:
        out = [-v for v in b[r - delta:]] + b[:r - delta]
    if sign < 0:
        out = [-v for v in out]
    return out


def synthetic_fft(rows_re, rows_im, nu: int, shr: Callable[[int, int], int], inst=None):
    """G_{t1} of MS eq. (syn-fft): radix-2 DIT over C[y]/(y^r + 1) with omega_{t1} = y^{2 nu}.

    Bit-reverse the t1 input polynomials; in stage s (blocks of 2^s polynomials) butterfly u pairs
    A_u, B_u with twiddle exponent delta_u = 2 nu u 2^{k1-s} and sets
    A_new = Q_q(1/2 (A + y^delta B)), B_new = Q_q(1/2 (A - y^delta B)) (Lemma 2.5).  Zero scalar
    multiplications; error <= k1 sqrt(2)/2 2^-q (eq. (syn-err)); outputs in natural order v1."""
    t1 = len(rows_re)
    k1 = t1.bit_length() - 1
    rev = bit_reverse_perm(k1) if k1 > 0 else [0]
    a_re = [rows_re[rev[j]] for j in range(t1)]
    a_im = [rows_im[rev[j]] for j in range(t1)]
    count = 0
    for s in range(1, k1 + 1):
        half = 1 << (s - 1)
        stride = 2 * nu * (1 << (k1 - s))
        for g in range(0, t1, 2 * half):
            for u in range(half):
                lo, hi = g + u, g + u + half
                d = stride * u
                br = nega_shift(a_re[hi], d)
                bi = nega_shift(a_im[hi], d)
                ar, ai = a_re[lo], a_im[lo]
                a_re[lo] = [shr(x + y, 1) for x, y in zip(ar, br)]
                a_im[lo] = [shr(x + y, 1) for x, y in zip(ai, bi)]
                a_re[hi] = [shr(x - y, 1) for x, y in zip(ar, br)]
                a_im[hi] = [shr(x - y, 1) for x, y in zip(ai, bi)]
                count += 1
    if inst is not None:
        inst.hit("synfft.butterfly", count)
    return a_re, a_im


def synthetic_fft_tape(rows_re, rows_im, nu: int, shr: Callable[[int, int], int], inst=None):
    """G_{t1} as the tape procedure of the proof of MS Lemma 2.5 ``lem:syn-fft`` (L282-L285;
    routing="tape"), on one tape of coefficient records (re, im), polynomial j = records j r .. j r + r - 1.

    Bit reversal: k1 split-and-concatenate passes, the units being whole polynomials
    (:func:`subnlogn.routing.bit_reverse_tape`; "routing.syn_bitrev_pass").  Stage s = 1..k1
    ("routing.syn_stage_split"): the tape holds t1 / 2^s blocks of 2^s polynomials; one scan of a block
    copies its first half (A_u) to T1 and its second half (B_u) to T2, and a k2-bit exponent
    delta_u = 2 nu u 2^(k1-s) grows by the stage stride as u increments.  For each pair u: the first
    r - delta_u records of B_u go to T3 (the head of T2 then rests on b_{r - delta_u}); then a_0..a_{r-1}
    on T1 are read in lockstep with the delta_u negated records -b_{r-delta_u}..-b_{r-1} on T2 followed
    by the r - delta_u records on T3 (= y^delta_u B_u mod y^r + 1, in natural order); A_new = Q_q(1/2 (a + b~))
    goes to the main tape, B_new = Q_q(1/2 (a - b~)) to T4, and T4 is copied to the block's lower half
    after the block.  The same additions and halvings as :func:`synthetic_fft` (with
    :func:`nega_shift`), so the outputs are bit-identical; zero scalar multiplications."""
    t1 = len(rows_re)
    k1 = t1.bit_length() - 1
    r = len(rows_re[0]) if t1 else 0
    tape = []
    for rr, ri in zip(rows_re, rows_im):           # the t1 polynomials, contiguous, natural order
        tape.extend(zip(rr, ri))
    tape = bit_reverse_tape(tape, k1, r, inst, "routing.syn_bitrev_pass")
    count = 0
    for s in range(1, k1 + 1):
        half = 1 << (s - 1)                        # polynomials per half block
        stride = 2 * nu * (1 << (k1 - s))
        span = half * r                            # records per half block
        out: list = []
        head = 0
        while head < len(tape):                    # one block of 2^s polynomials
            T1 = tape[head:head + span]            # (A_u)
            T2 = tape[head + span:head + 2 * span]  # (B_u)
            head += 2 * span
            T4: list = []
            h1 = h2 = 0
            delta = 0
            for _ in range(half):
                T3 = T2[h2:h2 + r - delta]         # b_0 .. b_{r-delta-1}
                h2 += r - delta
                for _ in range(delta):             # a_k with -b_{k + r - delta}
                    ar, ai = T1[h1]
                    br, bi = T2[h2]
                    br, bi = -br, -bi
                    out.append((shr(ar + br, 1), shr(ai + bi, 1)))
                    T4.append((shr(ar - br, 1), shr(ai - bi, 1)))
                    h1 += 1
                    h2 += 1
                for br, bi in T3:                  # a_k with +b_{k - delta}
                    ar, ai = T1[h1]
                    out.append((shr(ar + br, 1), shr(ai + bi, 1)))
                    T4.append((shr(ar - br, 1), shr(ai - bi, 1)))
                    h1 += 1
                delta += stride
                count += 1
            require(h1 == len(T1) and h2 == len(T2), "auxiliary tapes not consumed exactly (MS Lemma 2.5, L282-L285)")
            out += T4                              # lower half of the block
        tape = out
        if inst is not None:
            inst.hit("routing.syn_stage_split")
    if inst is not None:
        inst.hit("synfft.butterfly", count)
    out_re = [[a for a, _ in tape[j * r:(j + 1) * r]] for j in range(t1)]
    out_im = [[b for _, b in tape[j * r:(j + 1) * r]] for j in range(t1)]
    return out_re, out_im


def odd_stride_route(child_re, child_im, t1: int, r: int):
    """Y[u1][u2] = C_{v1}[u2] with u1 = (2 u2 - 1) v1 mod t1 (MS eq. (odd-perm)); returns the
    routed array in column-major form ``cols[u2][u1]`` (Lemma 2.4(ii)).  Exact permutation."""
    cols_re = [[0] * t1 for _ in range(r)]
    cols_im = [[0] * t1 for _ in range(r)]
    for v1 in range(t1):
        cr, ci = child_re[v1], child_im[v1]
        for u2 in range(r):
            u1 = ((2 * u2 - 1) * v1) % t1
            cols_re[u2][u1] = cr[u2]
            cols_im[u2][u1] = ci[u2]
    return cols_re, cols_im
