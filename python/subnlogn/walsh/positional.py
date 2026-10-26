"""Positional permutations of record-address bits (SPEC_WALSH §4; r5 §7.2, l.1247-1292,
eqs. (7.5)-(7.7)), and the compiled layout L, bit reversal B and unshuffle (LB)^-1 of Lemma 16
(SPEC_WALSH §4.4; Pr L2878-2928, L3021-3031; SPEC §5.2).

Conventions (SPEC_WALSH §4.1): positions 0..m0-1 counted from the MOST significant bit of the complete
binary record address (all 2^m0 addresses present, each carrying a contiguous record).  A positional map
``dest[p]`` is the destination of the bit now at position p; it moves records by the move convention
(SPEC §1.2): the record at x goes to y with y_{dest[p]} = x_p.  ``compose(f, g)[j] = f[g[j]]`` (g first),
``inverse(f)[f[j]] = j``.

Execution (§4.3): dest = I1 o I0 (two involutions; I0 executed first, R5 §7.2), every involution a set of
disjoint swaps, every swap three CNOT stages (a ^= b, b ^= a, a ^= b); within a stage all pairs commute
and are batched by the slice containing their target (:func:`subnlogn.walsh.gadget.cnot_batch`).  Targets
on the < h leftover positions use the elementary Lemma 3 two-bit permutation, here a RAM index map
(Dev-W3).  The slices (§4.2): the first J h positions (J = floor(m0/h)) are cut into h-bit chunks from the
most significant end; consecutive chunks are grouped by at most d; each (group, offset rho) is a slice.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..checks import require
from .gadget import WalshCtx, cnot_batch

__all__ = ["Slice", "make_slices", "compose", "inverse", "cycles", "two_involutions", "move_address_bits",
           "apply_positional_oracle", "elementary_cnot", "execute_positional_map", "compile_layout"]


@dataclass(frozen=True)
class Slice:
    """One slice (SPEC_WALSH §4.2): D consecutive h-bit chunks starting at position ``start`` and the bit
    at offset rho (counted from each chunk's least significant bit).  Prop 14 shape
    [A = 2^start] x [2^h]^D x [S = 2^(m0 - start - D h)]."""

    m0: int
    start: int
    D: int
    h: int
    rho: int

    @property
    def positions(self) -> list[int]:
        return [self.start + j * self.h + (self.h - 1 - self.rho) for j in range(self.D)]

    @property
    def A(self) -> int:
        return 1 << self.start

    @property
    def S(self) -> int:
        return 1 << (self.m0 - self.start - self.D * self.h)


def make_slices(m0: int, h: int, d: int) -> tuple[list[Slice], dict[int, int], list[int]]:
    """Slices of an m0-bit address (SPEC_WALSH §4.2): (slices, position -> slice index, leftovers).
    At most h ceil(J/d) <= m0/d + h slices (R5 (7.5))."""
    if h < 1 or d < 1:
        raise ValueError("make_slices needs h >= 1 and d >= 1")
    J = m0 // h
    slices, slice_of = [], {}
    for g in range(-(-J // d)):
        start, D = g * d * h, min(d, J - g * d)
        for rho in range(h):
            sl = Slice(m0, start, D, h, rho)
            for pos in sl.positions:
                slice_of[pos] = len(slices)
            slices.append(sl)
    return slices, slice_of, list(range(J * h, m0))


def compose(f: list[int], g: list[int]) -> list[int]:
    """compose(f, g)[j] = f[g[j]]: apply g first (SPEC_WALSH §4.1)."""
    return [f[x] for x in g]


def inverse(f: list[int]) -> list[int]:
    out = [0] * len(f)
    for j, x in enumerate(f):
        out[x] = j
    return out


def _check_bijection(dest: list[int]) -> None:
    if sorted(dest) != list(range(len(dest))):
        raise ValueError("a positional map must be a bijection of the positions (SPEC_WALSH §8)")


def cycles(dest: list[int]) -> list[list[int]]:
    """The cycles [i_0, i_1, ...] of dest (dest[i_j] = i_{j+1}), fixed points included."""
    _check_bijection(dest)
    seen, out = set(), []
    for s in range(len(dest)):
        if s in seen:
            continue
        cyc, x = [], s
        while x not in seen:
            seen.add(x)
            cyc.append(x)
            x = dest[x]
        out.append(cyc)
    return out


def two_involutions(dest: list[int]) -> tuple[list[int], list[int]]:
    """dest = I1 o I0 with involutions I0: i_j -> i_{-j}, I1: i_j -> i_{1-j} on every cycle (R5 §7.2;
    SPEC_WALSH §4.3).  Execute I0 first."""
    I0, I1 = list(range(len(dest))), list(range(len(dest)))
    for cyc in cycles(dest):
        L = len(cyc)
        for j, pos in enumerate(cyc):
            I0[pos], I1[pos] = cyc[(-j) % L], cyc[(1 - j) % L]
    require(compose(I1, I0) == dest and compose(I0, I0) == list(range(len(dest))) == compose(I1, I1),
            "dest != I1 o I0 with involutions I0, I1 (R5 §7.2; SPEC_WALSH §4.3)")
    return I0, I1


def move_address_bits(x: int, dest: list[int]) -> int:
    """Oracle (tests only): the address y with y_{dest[p]} = x_p, positions from the MSB."""
    m0 = len(dest)
    y = 0
    for p, q in enumerate(dest):
        y |= ((x >> (m0 - 1 - p)) & 1) << (m0 - 1 - q)
    return y


def apply_positional_oracle(recs: list, dest: list[int]) -> list:
    """Oracle (tests only): out[move_address_bits(x)] = recs[x]."""
    out = [None] * len(recs)
    for x, rec in enumerate(recs):
        out[move_address_bits(x, dest)] = rec
    return out


def elementary_cnot(recs: list, c: int, t: int, m0: int) -> list:
    """Lemma 3 two-bit permutation for a leftover target (SPEC_WALSH §4.3): the address involution
    x -> x with x_t ^= x_c; a RAM index map in this backend (Dev-W3)."""
    ec, et = m0 - 1 - c, m0 - 1 - t
    out = [None] * len(recs)
    for x, rec in enumerate(recs):
        out[x ^ (((x >> ec) & 1) << et)] = rec
    return out


def execute_positional_map(recs: list, dest: list[int], p: int, wctx: WalshCtx) -> list:
    """Move every record from x to move_address_bits(x, dest) (SPEC_WALSH §4.3): two involutions, three
    CNOT stages each, pairs batched by the slice of their target (one :func:`cnot_batch` per nonempty
    slice batch), leftover targets by :func:`elementary_cnot`.  ``recs`` is a disk array on the 2^-p
    grid (any grid works: the gadget's exactness argument is relative); the result is exact."""
    m0 = len(dest)
    _check_bijection(dest)
    if len(recs) != 1 << m0:
        raise ValueError("positional maps need the complete address cube of 2^m0 records")
    wctx.hit("positional_map")
    if dest == list(range(m0)):
        return recs
    slices, slice_of, _ = make_slices(m0, wctx.h, wctx.d)
    for inv in two_involutions(dest):
        swaps = [(a, inv[a]) for a in range(m0) if a < inv[a]]
        for stage in ([(b, a) for a, b in swaps], [(a, b) for a, b in swaps], [(b, a) for a, b in swaps]):
            groups: dict = {}
            for c, t in stage:                                   # (control, target)
                groups.setdefault(slice_of.get(t), []).append((c, t))
            for sl, batch in groups.items():
                if sl is None:
                    for c, t in batch:
                        recs = elementary_cnot(recs, c, t, m0)
                        wctx.hit("leftover_cnot")
                else:
                    recs = cnot_batch(recs, batch, slices[sl], p, wctx)
    return recs


def compile_layout(widths: list[int], ell: int, h: int):
    """L, B, U = (LB)^-1 and the named-slot table of Lemma 16's layout (SPEC_WALSH §4.4; SPEC §5.2;
    Pr L2878-2928): ``widths`` = a_i in {ell - 1, ell} of the first d - 1 axes, 1 <= h <= ell - 1.
    Named slot (i, v) = the address bit of weight 2^v of axis i; originally the slots are in axis order,
    high to low.  L moves the long axes' top bits and then the b = (ell - 1) mod h lowest slots of every
    axis into the prefix and orders the remaining chunks chunk-major (each chunk high to low); B is the
    per-axis bit reversal.  Returns (L, B, U, new, b, q) with ``new`` = named slot -> position after L."""
    if not all(a in (ell - 1, ell) for a in widths) or not 1 <= h <= ell - 1:
        raise ValueError("compile_layout needs a_i in {ell-1, ell} and 1 <= h <= ell - 1")
    original = [(i, v) for i, a in enumerate(widths) for v in range(a - 1, -1, -1)]
    old = {s: k for k, s in enumerate(original)}
    b, q = (ell - 1) % h, (ell - 1) // h
    prefix = [(i, ell - 1) for i, a in enumerate(widths) if a == ell]
    prefix += [(i, v) for v in range(b - 1, -1, -1) for i in range(len(widths))]
    rest = [(i, v) for j in range(q) for i in range(len(widths))
            for v in range(ell - 2 - j * h, ell - 2 - (j + 1) * h, -1)]
    new = {s: k for k, s in enumerate(prefix + rest)}
    L = [new[s] for s in original]
    B = [old[(i, widths[i] - 1 - v)] for (i, v) in original]
    U = inverse(compose(L, B))
    require(U == compose(inverse(B), inverse(L)), "U != B^-1 L^-1 (SPEC_WALSH §4.4)")
    return L, B, U, new, b, q
