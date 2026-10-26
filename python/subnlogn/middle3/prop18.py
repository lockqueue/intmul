"""Proposition 18: normalized ring convolution from the retained layout (SPEC §5.7; Pr L3222-3337).

For arrays f, g on prod_{i<d} Z/t_i of R_r records (disk grid, scale p):
    u = forward(f), v = forward(g)            (same retained order L·B; Lemma 16)
    z = Q_p(u v / r) recordwise                (Lemma 17, via the independent multiplier)
    h = opposite(z)                            (original order)
    h <- h * M exactly                         (append lg M zero bits; output width w + lg M)
Exact target M_r(f, g) = (f * g)/(r M) (cyclic in the d - 1 axes, negacyclic in y), from
F_t^-(f * g) = M (F_t^- f)(F_t^- g) and F_t^+ F_t^- = I/M.  Error < sqrt(2) M (3l + 1) 2^-p
(reading R6).  The output is NOT narrowed here: the caller proves a disk bound first (SPEC §5.7).
"""

from __future__ import annotations

from ..ring import normalized_ring_product
from .synth import Synth

__all__ = ["normalized_ring_convolution", "to_record", "from_record"]


def to_record(re: list[int], im: list[int]) -> list[tuple[int, int]]:
    """(re list, im list) -> the ring module's record (list of coefficient pairs)."""
    return list(zip(re, im))


def from_record(rec) -> tuple[list[int], list[int]]:
    return [a for a, _ in rec], [b for _, b in rec]


def normalized_ring_convolution(f, g, sy: Synth, p: int, mul=None, inst=None):
    """M_r(f, g) with the error/width contract of Prop 18 (module docstring).

    ``f``, ``g``: lists of M records (re list, im list) on grid 2^-p, original axis-major order.
    Returns (records on grid 2^-p with numerators scaled by M, lg M = extra output width)."""
    u, _ = sy.forward(f, p, p, truncate=True)
    v, _ = sy.forward(g, p, p, truncate=True)
    z = []
    for (ur, ui), (vr, vi) in zip(u, v):
        prod = normalized_ring_product(to_record(ur, ui), to_record(vr, vi), p, sy.r,
                                       mul if mul is not None else _pymul)
        z.append(from_record(prod))
    if inst is not None:
        inst.hit("prop18.ring_product", len(z))
    h, _ = sy.opposite(z, p, p, truncate=True)
    mM = sy.n
    return [([x << mM for x in re], [x << mM for x in im]) for re, im in h], mM


def _pymul(a: int, b: int) -> int:
    return a * b
