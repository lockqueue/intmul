"""Ring records of R_r = C[y]/(y^r + 1) and the preprint's Lemma 17 (signed packing, centered
extraction, normalized ring product), per SPEC §1.4-§1.6 and §5.4-§5.6.

Sources: Pr = the plain-text rendering of [OAI26] (line numbers), SPEC = the internal implementation specification.

Representation (SPEC §1.6; Pr L2609-2633): a record is a list of r = 2^l coefficients
z_0, ..., z_{r-1} in increasing index, each a pair (re, im) of Python ints, the numerators of a
complex value on the grid 2^-p (the grid precision p is carried by the caller).  The ring
identification never reorders coefficients.  Disk grid (Pr L3370): re^2 + im^2 <= 2^{2p}.
Q_p is truncation toward zero of each real and imaginary numerator (SPEC §1.4; Pr (26),
L2629-2633): ||Q_p z - z|| < sqrt(2) 2^-p and ||Q_p z|| <= ||z||.  No floating point anywhere.
"""

from __future__ import annotations

import operator
from typing import Callable

from .checks import RuntimeCheckError, require
from .fixedpoint import shr_trunc

__all__ = ["in_disk", "monomial_shift", "pack_blocks", "pack_to_int", "centered_extract",
           "normalized_ring_product"]

Record = list[tuple[int, int]]


def in_disk(re: int, im: int, p: int) -> bool:
    """Exact disk-grid test re^2 + im^2 <= 2^{2p} for the numerators of 2^-p (re + i im)
    (Pr L3370, D_p; SPEC §1.5)."""
    return re * re + im * im <= 1 << (2 * p)


def monomial_shift(coeffs: Record, E: int) -> Record:
    """y^E z mod (y^r + 1) for any integer E (SPEC §5.4; Pr L3000-3005): write E = e r + s with
    0 <= s < r (floor semantics, also for negative E), split the list before position r - s, put
    the tail before the head, negate the moved tail, and apply the common sign (-1)^e.  A signed
    coefficient rotation, hence an isometry for the coefficient sup norm (Pr L2627)."""
    r = len(coeffs)
    e, s = divmod(E, r)
    out = list(coeffs) if s == 0 else [(-a, -b) for a, b in coeffs[r - s:]] + list(coeffs[:r - s])
    return [(-a, -b) for a, b in out] if e % 2 else out


# -- Lemma 17: signed packing (Pr L3047-3124) -------------------------------------------------------


def _blocks_to_int(blocks: list[int], p: int) -> int:
    """sum_j blocks[j] B0^j for blocks 0 <= d_j < B0 = 2^{4p} = 16^p (p hex digits per block)."""
    if not blocks:
        return 0
    return int("".join(format(d, f"0{p}x") for d in reversed(blocks)), 16)


def _int_to_blocks(N: int, J: int, p: int) -> list[int]:
    """The J base-B0 digits (least significant first) of 0 <= N < B0^J, B0 = 2^{4p}."""
    require(0 <= N < 1 << (4 * p * J), "N does not fit in J blocks of 4p bits (Pr L3125-3180)")
    s = format(N, f"0{p * J}x")
    L = len(s)
    return [int(s[L - (j + 1) * p:L - j * p], 16) for j in range(J)]


def _complement_increment(blocks: list[int], p: int) -> list[int]:
    """B0^n - sum_j d_j B0^j for a nonzero n-block value: complement every block and add one,
    one carry scan (Pr L3121-3123, L3138-3139).  Asserts that no carry leaves the n blocks."""
    B0 = 1 << (4 * p)
    c, out = 1, []
    for d in blocks:
        v = B0 - 1 - d + c
        out.append(v & (B0 - 1))
        c = v >> (4 * p)
    require(c == 0, "complement-and-increment of a zero value (Pr L3121-3123)")
    return out


def pack_blocks(u: list[int], p: int) -> tuple[list[int], int]:
    """Streaming two's-complement encoding of A_u = u(B0) = sum_j u_j B0^j, B0 = 2^{4p} (Pr L3097-3124;
    SPEC §5.5): with gamma_0 = 0, d_j = (u_j + gamma_j) mod B0 in [0, B0) and
    gamma_{j+1} = (u_j + gamma_j - d_j)/B0, which stays in {-1, 0} because |u_j| <= 2^p.  Returns
    (d_0..d_{r-1}, gamma_r); A_u = sum_j d_j B0^j + gamma_r B0^r and gamma_r = -1 iff A_u < 0."""
    B0, lim = 1 << (4 * p), 1 << p
    g, blocks = 0, []
    for uj in u:
        if not -lim <= uj <= lim:
            raise RuntimeCheckError(f"|u_j| <= 2^p violated: {uj} (Pr L3097-3124)")
        dj = (uj + g) & (B0 - 1)         # mod B0 = 2^{4p} and exact division by B0: mask and shift
        g = (uj + g - dj) >> (4 * p)
        if g not in (-1, 0):
            raise RuntimeCheckError("packing carry left {-1, 0} (Pr L3097-3124)")
        blocks.append(dj)
    return blocks, g


def pack_to_int(u: list[int], p: int) -> int:
    """The signed evaluation integer A_u = sum_j u_j 2^{4pj} (Pr L3066-3077), assembled from the
    streaming blocks of :func:`pack_blocks`: the blocks are kept when gamma_r = 0, otherwise
    complemented and incremented to give |A_u| (Pr L3121-3123), and the sign is restored.
    Asserts |A_u| < B0^r / 2 (each magnitude fits in 4pr bits, Pr L3074-3077)."""
    blocks, g = pack_blocks(u, p)
    if g == 0:
        A = _blocks_to_int(blocks, p)
    else:
        A = -_blocks_to_int(_complement_increment(blocks, p), p)
    require((A < 0) == (g == -1), "sign of A_u disagrees with the final packing carry (Pr L3121-3123)")
    require(2 * abs(A) < 1 << (4 * p * len(u)), "|A_u| < B0^r/2 violated (Pr L3074-3077)")
    return A


# -- Lemma 17: centered extraction (Pr L3125-3180) --------------------------------------------------


def centered_extract(Z: int, J: int, p: int) -> list[int]:
    """Recover h_0..h_{J-1} from Z = sum_{j<J} h_j B0^j, |h_j| < B0/2, B0 = 2^{4p} (Pr L3125-3180;
    SPEC §5.5).  Z is written in sign-extended two's complement Z = sum q_j B0^j + eps B0^J
    (0 <= q_j < B0, eps in {-1, 0}; a negative sign is complemented and incremented within J
    blocks).  With rho_0 = 0, h_j is the unique integer in [-B0/2, B0/2) congruent to q_j + rho_j
    and rho_{j+1} = (q_j + rho_j - h_j)/B0, which stays in {0, 1}; at the end rho_J + eps = 0 (a
    negative product has final carry 1, canceled by its sign extension).  All asserted."""
    B0 = 1 << (4 * p)
    half = B0 >> 1
    require(2 * abs(Z) < 1 << (4 * p * J), "Z does not fit in J signed blocks (Pr L3125-3180)")
    eps = -1 if Z < 0 else 0
    q = _int_to_blocks(abs(Z), J, p)
    if eps:
        q = _complement_increment(q, p)
    rho, out = 0, []
    for j in range(J):
        hj = ((q[j] + rho + half) & (B0 - 1)) - half     # centred residue mod B0 = 2^{4p} by a mask
        rho_next = (q[j] + rho - hj) >> (4 * p)          # exact division by B0 as a shift
        if rho_next not in (0, 1):
            raise RuntimeCheckError("extraction carry left {0, 1} (Pr L3125-3180)")
        out.append(hj)
        rho = rho_next
    require(rho + eps == 0, "final carry does not cancel the sign extension (Pr L3125-3180)")
    return out


# -- Lemma 17: normalized ring product (Pr L3047-3220) ----------------------------------------------


def normalized_ring_product(f: Record, g: Record, p: int, r: int,
                            mul: Callable[[int, int], int] = operator.mul) -> Record:
    """Q_p(f g / r) in R_r for disk-grid records f = 2^-p (a + i b), g = 2^-p (c + i e)
    (Pr Lemma 17, L3047-3220; SPEC §5.6).

    Hypotheses (asserted): r = 2^l with 1 <= l < p, p >= 2, every input coefficient on the disk
    grid.  The four streams are packed (:func:`pack_to_int`); the products A_a A_c, A_b A_e,
    A_a A_e, A_b A_c are formed by multiplying absolute values with the independent multiplier
    ``mul`` (default Python ``*``) and restoring the sign (Pr L3077); each is extracted with
    J = 2r (:func:`centered_extract`; padded top coefficient h_{2r-1} = 0 and the bound (31)
    |h_j| <= r 2^{2p} < 2^{3p} < B0/2 asserted).  Real/imaginary streams ac - be, ae + bc are
    reduced modulo y^r + 1 by subtracting the coefficient at j + r from the one at j; each H_j is
    a sum of r signed Gaussian products, |H_j| <= r 2^{2p} (asserted).  The returned numerators
    are trunc0(Re H_j / 2^{p+l}) + i trunc0(Im H_j / 2^{p+l}) (Pr L3193-3216): disk grid
    (asserted), error < sqrt(2) 2^-p by (26), component magnitudes <= 2^p."""
    l = r.bit_length() - 1
    require(r == 1 << l and 1 <= l < p and p >= 2, "Lemma 17 needs r = 2^l, 1 <= l < p, p >= 2")
    require(len(f) == r and len(g) == r, "records must have r coefficients (Lemma 17)")
    require(all(in_disk(x, y, p) for x, y in f) and all(in_disk(x, y, p) for x, y in g),
            "inputs must be disk-grid polynomials (Lemma 17, SPEC §6.8 disk on ring inputs)")
    A = {"a": pack_to_int([z[0] for z in f], p), "b": pack_to_int([z[1] for z in f], p),
         "c": pack_to_int([z[0] for z in g], p), "e": pack_to_int([z[1] for z in g], p)}

    def signed_product(x: int, y: int) -> int:
        m = mul(abs(x), abs(y))
        return -m if (x < 0) != (y < 0) else m

    J, bound = 2 * r, r << (2 * p)
    h = {}
    for k in ("ac", "be", "ae", "bc"):
        hk = centered_extract(signed_product(A[k[0]], A[k[1]]), J, p)
        require(hk[J - 1] == 0 and all(abs(x) <= bound for x in hk), "bound (31) violated (Pr L3125-3180)")
        h[k] = hk
    re_full = [h["ac"][j] - h["be"][j] for j in range(J)]
    im_full = [h["ae"][j] + h["bc"][j] for j in range(J)]
    out = []
    for j in range(r):
        Hre, Him = re_full[j] - re_full[j + r], im_full[j] - im_full[j + r]
        if not Hre * Hre + Him * Him <= bound * bound:
            raise RuntimeCheckError("|H_j| <= r 2^{2p} violated (Pr L3193-3216)")
        z = (shr_trunc(Hre, p + l), shr_trunc(Him, p + l))
        if not in_disk(z[0], z[1], p):
            raise RuntimeCheckError("output left the disk (Pr L3193-3216)")
        out.append(z)
    return out
