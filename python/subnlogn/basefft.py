"""BaseRadix2FFT: the certified leaf transform (MS Lemma 6.5 ``lem:forward`` part 2, the leaf
paragraph of its proof, and §2.2 table item (d)).

At a leaf R = 2^K (R <= 4 p^2 under the faithful schedule) the input x on C~_{p+2} is moved
exactly to the internal grid C~_{q_b}, q_b = p + K + 16, bit-reversed, and K decimation-in-time
radix-2 stages are applied.  In stage s, for butterfly j of a block of 2^s records,

    W     = RM_{q_b}(w-bar_{s,j}, B_j),          w-bar_{s,j} = Q_{q_b}(e^{2 pi i j / 2^s}),
    A_new = Q_{q_b}(1/2 (A_j + W)),   B_new = Q_{q_b}(1/2 (A_j - W)),

which realizes the positive normalized DFT (MS eq. (dft-1d)); the halvings give the 1/R.  The
result is rounded once to C~_{p+2}.  Error (Lemma 6.5): e_K <= 2.16 K 2^{-q_b} A < 2^{-p-14} A
before the final rounding (<= sqrt(2)/8 2^-p), A = max(1, ||x||_inf); total < 2^-p A.

Routing (``schedule.routing``): "tape" (default) is the tape realization of MS L693 / L821: an
initial K-pass even/odd split bit reversal (:func:`subnlogn.routing.bit_reverse_tape`), then in stage
s every block of 2^s records is split into its upper and lower halves on T1, T2, paired in lockstep
with the contiguous stage-s twiddle list replayed from the table (§2.2 (d)), A_new written to the
main tape and B_new to a scratch tape that is copied back after the block.  "index" keeps the
index-gather bit reversal and the in-place strided butterflies (oracle; DEVIATIONS D2).  Both run
the same rounding calls on the same integers in the same order per butterfly: bit-identical.
"""

from __future__ import annotations

from .checks import require
from .routing import bit_reverse_tape
from .schedule import Level2D
from .tables import leaf_tables

__all__ = ["base_radix2_fft", "bit_reverse_perm"]


def bit_reverse_perm(K: int) -> list[int]:
    """rev[j] = j with its K low bits reversed."""
    rev = [0] * (1 << K)
    for j in range(1, 1 << K):
        rev[j] = (rev[j >> 1] >> 1) | ((j & 1) << (K - 1))
    return rev


def base_radix2_fft(ctx, re: list[int], im: list[int], lv: Level2D) -> tuple[list[int], list[int]]:
    """F_R x for x = (re + i im) 2^-(p+2); returns numerators on C~_{p+2} (MS Lemma 6.5)."""
    R, K, qb, q = lv.R, lv.K, lv.q_b, lv.p + 2
    shr = ctx.shr
    ctx.inst.hit("fastdft.leaf")
    if R == 1:
        return list(re), list(im)
    tab = leaf_tables(ctx, lv)
    twr, twi = tab.tw_re, tab.tw_im
    up = qb - q
    if ctx.schedule.routing == "tape":
        ar, ai = _stages_tape(ctx, re, im, K, qb, up, tab.stages)
        ctx.inst.hit("basefft.butterfly", K * (R // 2))
        ctx.inst.height(f"leaf.internal.R{R}", ar, ai)
        return [shr(v, up) for v in ar], [shr(v, up) for v in ai]
    mul = ctx.word_mul()                           # butterfly products (MS Thm 7.1 pt 3 (b))
    rev = bit_reverse_perm(K)
    ar = [0] * R
    ai = [0] * R
    for j in range(R):
        ar[rev[j]] = re[j] << up
        ai[rev[j]] = im[j] << up
    h = 1
    nb = 0
    while h < R:
        step = R // (2 * h)
        for g in range(0, R, 2 * h):
            for j in range(h):
                wr = twr[j * step]
                wi = twi[j * step]
                lo = g + j
                hi = lo + h
                br = ar[hi]
                bi = ai[hi]
                tr = shr(mul(br, wr) - mul(bi, wi), qb)
                ti = shr(mul(br, wi) + mul(bi, wr), qb)
                xr = ar[lo]
                xi = ai[lo]
                ar[lo] = shr(xr + tr, 1)
                ai[lo] = shr(xi + ti, 1)
                ar[hi] = shr(xr - tr, 1)
                ai[hi] = shr(xi - ti, 1)
        nb += R // 2
        h <<= 1
    ctx.inst.hit("basefft.butterfly", nb)
    ctx.inst.height(f"leaf.internal.R{R}", ar, ai)
    return [shr(v, up) for v in ar], [shr(v, up) for v in ai]


def _stages_tape(ctx, re: list[int], im: list[int], K: int, qb: int, up: int, stages: list):
    """The tape realization of BaseRadix2FFT's routing (MS L693, L821; routing="tape"): move the
    records (re, im) to C~_{q_b} in one scan, bit-reverse them by K even/odd split passes
    ("routing.leaf_bitrev_pass"), then for each stage s = 1..K ("routing.leaf_stage_split"): split
    every block of 2^s records into its upper halves A_u (to T1) and lower halves B_u (to T2), and
    for each block read T1, T2 and the stage-s twiddle list in lockstep, W_u = RM_{q_b}(w-bar_{s,u},
    B_u), writing A_new = Q(1/2 (A_u + W_u)) to the main tape and B_new = Q(1/2 (A_u - W_u)) to the
    scratch tape T4, which is copied to the block's lower half after the block.  Same expressions and
    rounding calls as the index variant.  Returns the internal (re, im) lists after stage K."""
    shr, inst, mul = ctx.shr, ctx.inst, ctx.word_mul()
    R = 1 << K
    tape = [(a << up, b << up) for a, b in zip(re, im)]
    tape = bit_reverse_tape(tape, K, 1, inst, "routing.leaf_bitrev_pass")
    for s in range(1, K + 1):
        h = 1 << (s - 1)
        wl_re, wl_im = stages[s - 1]
        T1: list = []
        T2: list = []
        head = 0
        while head < R:                            # split: upper halves to T1, lower halves to T2
            T1 += tape[head:head + h]
            T2 += tape[head + h:head + 2 * h]
            head += 2 * h
        out: list = []
        hd = 0                                     # common head of T1 and T2 (lockstep)
        for _ in range(R // (2 * h)):              # one block of 2^s records
            T4: list = []
            for u in range(h):                     # stage-s twiddle list replayed once per block
                wr, wi = wl_re[u], wl_im[u]
                br, bi = T2[hd]
                tr = shr(mul(br, wr) - mul(bi, wi), qb)
                ti = shr(mul(br, wi) + mul(bi, wr), qb)
                xr, xi = T1[hd]
                out.append((shr(xr + tr, 1), shr(xi + ti, 1)))
                T4.append((shr(xr - tr, 1), shr(xi - ti, 1)))
                hd += 1
            out += T4                              # merge back: B_new into the lower half
        require(hd == len(T1) == len(T2), "BaseRadix2FFT stage: tapes T1, T2 not consumed exactly (MS L693, L821)")
        tape = out
        inst.hit("routing.leaf_stage_split")
    return [a for a, _ in tape], [b for _, b in tape]
