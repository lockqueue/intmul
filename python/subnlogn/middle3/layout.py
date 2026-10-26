"""Lemma 16's positional layout L (SPEC §5.2; Pr L2878-2928) as an explicit slot descriptor.

Record addresses are n-bit integers.  Physical bit position 0 is the MOST significant address bit
(records occur in lexicographic order of the address fields, first field most significant;
SPEC §1.7).  Named slot (i, h) is the original address bit of weight 2^h of axis i (0-based axes,
D = d - 1 of them; axis i has a_i = lg t_i slots, t_i in {2^(l-1), 2^l}).  Initially the slots
are in axis order and, within an axis, in decreasing h [Pr L2880-2881].

L is built from two kinds of primitive moves on the descriptor [Pr L2885-2909]:
1. prefix moves (Lemma 3 single-bit moves): first (i, l-1) for the long axes in increasing i, then
   (i, h) for h = b-1, ..., 0 and, within each h, increasing i (b = (l-1) mod K); each listed slot
   is moved immediately after the prefix already formed, the others keep their relative order;
2. chunk exchanges (Lemma 12, width K): the remaining slots of each axis form q = floor((l-1)/K)
   chunks of K consecutive slots, chunk (i, j) for j = 1..q from high to low; the physical chunk
   order (1,1),...,(1,q),(2,1),...,(D,q) is changed to (1,1),(2,1),...,(D,1),(1,2),...,(D,q) by
   scanning target positions left to right and exchanging when they differ (<= Dq - 1 exchanges,
   nonadjacent allowed).
The induced record permutation moves the record at address x to L(x) (polynomial suffix intact).
In the RAM backend the moves are explicit index maps (DEVIATIONS D2); in the full pipeline the
chunk exchanges are Lemma 12 calls (M5).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ..checks import require

__all__ = ["LayoutPlan", "layout_plan", "permute_records", "chunk_slots"]


def chunk_slots(i: int, j: int, ell: int, K: int) -> list[tuple[int, int]]:
    """Named slots of chunk (i, j), j = 1..q from high to low: h = l-2-(j-1)K down to l-1-jK."""
    top = ell - 2 - (j - 1) * K
    return [(i, h) for h in range(top, top - K, -1)]


@dataclass
class LayoutPlan:
    """The layout L for axis lengths t (D axes), l = lg r, chunk width K."""

    t: tuple[int, ...]
    ell: int
    K: int
    b: int
    q: int
    n: int                                   # number of address bits = sum_i a_i
    order0: list[tuple[int, int]]            # initial physical order of named slots
    order: list[tuple[int, int]]             # physical order after L
    moves: list[tuple] = field(default_factory=list)   # ("prefix", slot, pos) / ("xchg", p1, p2, K)

    @property
    def pos(self) -> dict[tuple[int, int], int]:
        """slot -> physical position after L (0 = most significant)."""
        return {s: k for k, s in enumerate(self.order)}

    @property
    def pos0(self) -> dict[tuple[int, int], int]:
        return {s: k for k, s in enumerate(self.order0)}

    def address_map(self, inverse: bool = False) -> list[int]:
        """amap[x] = L(x) (or L^{-1}(x)): bit of slot s moves from pos0[s] to pos[s]."""
        n = self.n
        src, dst = (self.pos0, self.pos) if not inverse else (self.pos, self.pos0)
        pairs = [(n - 1 - src[s], n - 1 - dst[s]) for s in self.order0]
        out = [0] * (1 << n)
        for x in range(1 << n):
            y = 0
            for sb, db in pairs:
                y |= ((x >> sb) & 1) << db
            out[x] = y
        return out


def layout_plan(t: tuple[int, ...], ell: int, K: int) -> LayoutPlan:
    """Construct L exactly as in the proof of Lemma 16 [Pr L2882-2909]; SPEC §5.2."""
    D = len(t)
    a = [ti.bit_length() - 1 for ti in t]
    if not all(ai in (ell - 1, ell) for ai in a):
        raise ValueError("Lemma 16 needs t_i in {2^(l-1), 2^l}")
    if not 1 <= K <= ell - 1:
        raise ValueError("Lemma 16 needs 1 <= K <= l - 1")
    b, q = (ell - 1) % K, (ell - 1) // K
    order0 = [(i, h) for i in range(D) for h in range(a[i] - 1, -1, -1)]
    order = list(order0)
    moves: list[tuple] = []
    prefix = [(i, ell - 1) for i in range(D) if a[i] == ell]
    prefix += [(i, h) for h in range(b - 1, -1, -1) for i in range(D)]
    for k, s in enumerate(prefix):
        order.remove(s)
        order.insert(k, s)
        moves.append(("prefix", s, k))
    base = len(prefix)
    chunks = [(i, j) for i in range(D) for j in range(1, q + 1)]      # current physical chunk order
    target = [(i, j) for j in range(1, q + 1) for i in range(D)]
    for k in range(len(target) - 1):
        if chunks[k] != target[k]:
            m = chunks.index(target[k])
            chunks[k], chunks[m] = chunks[m], chunks[k]
            moves.append(("xchg", base + k * K, base + m * K, K))
    order = order[:base] + [s for (i, j) in chunks for s in chunk_slots(i, j, ell, K)]
    require(sorted(order) == sorted(order0), "layout L must permute the address slots (Lemma 16, SPEC §5.2)")
    return LayoutPlan(tuple(t), ell, K, b, q, len(order0), order0, order, moves)


def permute_records(records: list, amap: list[int]) -> list:
    """new[amap[x]] = old[x] (an address permutation moves the payload at x to f(x); SPEC §1.2)."""
    out = [None] * len(records)
    for x, rec in enumerate(records):
        out[amap[x]] = rec
    return out


def execute_layout(plan: LayoutPlan, records: list, swap, inverse: bool = False, inst=None) -> list:
    """Execute L (or L^{-1}) on a complete record stream by the plan's moves (Pr L2885-2909; SPEC
    §5.2), instead of the index map: every prefix move is a Lemma 3 single-digit move
    (:func:`subnlogn.stream.digit_move`) and every chunk exchange is a value exchange of two K-bit
    chunks by ``swap(stream, shape, a, b, inst)`` -- Lemma 12 (:func:`subnlogn.m6.lemma13.
    swap_via_lemma12`, bit network) or the bitwise base case.  The record at address x ends at L(x)
    (or L^{-1}(x)); equal to ``permute_records`` with ``address_map`` (tested)."""
    from ..stream import Field, Shape, digit_move
    n = plan.n
    if len(records) != 1 << n:
        raise ValueError("layout execution needs the complete 2^n record stream")
    order = list(plan.order0)
    befores = []                                   # physical order before each move
    for mv in plan.moves:
        befores.append(list(order))
        if mv[0] == "prefix":
            _, s, k = mv
            order.remove(s)
            order.insert(k, s)
        else:
            _, p1, p2, K = mv
            order[p1:p1 + K], order[p2:p2 + K] = order[p2:p2 + K], order[p1:p1 + K]
    require(order == plan.order, "layout moves do not reach the planned order (Lemma 16, SPEC §5.2)")
    stream = list(records)
    seq = list(zip(plan.moves, befores))
    if inverse:
        seq = seq[::-1]
        order = list(plan.order)
    else:
        order = list(plan.order0)
    shape = Shape(tuple(Field(sl, 2, 2) for sl in order), 1)
    for mv, before in seq:
        if mv[0] == "prefix":
            _, sl, k = mv
            dest = k if not inverse else before.index(sl)
            stream, shape = digit_move(stream, shape, sl, dest, inst)
        else:
            _, p1, p2, K = mv
            names = [f.name for f in shape.fields]
            c1, c2 = names[p1:p1 + K], names[p2:p2 + K]
            j1, j2 = ("xchg", 1), ("xchg", 2)
            shape = shape.join(c1, j1, radix=2).join(c2, j2, radix=2)
            stream, shape = swap(stream, shape, j1, j2, inst)
            # the values moved: position p1 now carries chunk c2's bits and vice versa
            shape = shape.split(j1, [Field(sl, 2, 2) for sl in c2]).split(j2, [Field(sl, 2, 2) for sl in c1])
    final = [f.name for f in shape.fields]
    require(final == (plan.order0 if inverse else plan.order), "layout execution ended in the wrong order (SPEC §5.2)")
    if inst is not None:
        inst.hit("layout.executed")
    return stream
