"""Shared per-level tables (manuscript §2.2, "Shared Per-Level Precomputation", items (a)-(d)),
with the negative half-bin carrier drop-in of r2 §8.

For a non-leaf level (R, p) with t1 = 2^floor(K/2), r = 2^ceil(K/2) (listing l.737-738):

(a) for each row j1 < t1 the guarded folded filter H-bar^(j1) on R~_q (q = q_child), MS §6.1 item
    (d), built from the MODULATED kernel  g(s) = e^{-pi i s/r} sinc(s) e^{-pi s^2/alpha^2},
    alpha = 2 sqrt(p_work ln2/pi)  (r2 (8.1)), folded modulo r (r2 §4.7: fold the modulated
    kernel, never periodize-then-modulate), together with its Kronecker-packed integers
    Pack_{B_slot}(2^q H-bar) (MS Lemma 6.2, Thm 6.3);
(b) the r twist roots  zeta-bar_k = Q_q(e^{pi i k/r}),  k < r  (MS §2.2 (b));
(c) the r solver tuples (c0, c1, mu, rho, gamma)  for u2 < r  (MS §2.2 (c)) with the drop-in
    coefficients c0 = G((u2+1/2)/r), c1 = G((u2+1/2)/r - 1) (r2 (8.2)), mu = Q_q(1/M),
    rho = -Q_q(min/max) and gamma = Q_q(1/(1 - rho^t1)) computed from the STORED rho (r2 (4.17));
(d) at a leaf, the twiddles Q_{q_b}(e^{2 pi i k/R}), k < R/2 (MS §2.2 (d); the per-stage lists
    of the manuscript are the sub-lists k = u 2^{K-s}).

Every table entry is the correctly rounded value Q_q(exact) produced by :mod:`subnlogn.certified`
(error <= 1/2 2^-q per real coordinate), except gamma, which is the exact nearest rounding of the
rational number 1/(1 - rho^L) (no transcendental involved).  Tables are cached in ``ctx.tables``
(explicit, per computation) keyed by every parameter they depend on.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from . import certified
from .checks import require
from .fixedpoint import div_half_even, shr_half_even
from .kronecker import pack
from .schedule import Level2D

__all__ = ["FilterRow", "SolverTuple", "LevelTables2D", "LeafTables", "filter_row",
           "level_tables_2d", "leaf_tables", "closure_gamma", "closure_guard", "solver_tuple",
           "twist_roots"]


@dataclass(frozen=True)
class FilterRow:
    """One row's guarded folded filter in convolution form (MS §6.1 (d), Thm 6.3).

    ``taps`` f_b (b < W~) satisfy, for the cyclic correlation of MS eq. (u-ideal),
    U_k = sum_n (v * f)_n over n = k + offset (mod r), where * is linear convolution.
    If W <= r: f_b = h^tr(m1 - b), offset = m1 (reversed contiguous taps); else
    f_a = h^tr(-a mod r), offset = 0 (folded modulo r).  h^tr is the truncated folded filter.
    """

    taps_re: tuple[int, ...]
    taps_im: tuple[int, ...]
    offset: int
    q: int


@dataclass(frozen=True)
class SolverTuple:
    """Column-solver parameters (MS §5.2 CyclicSolve; drop-in r2 §8, (4.15)-(4.17)), all on R~_q."""

    c0: int
    c1: int
    mu: int
    rho: int
    gamma: int
    forward: bool


@dataclass
class LevelTables2D:
    lv: Level2D
    filters: list[FilterRow]
    packed_re: list[int]
    packed_im: list[int]
    zeta_re: list[int]
    zeta_im: list[int]
    solver: list[SolverTuple]


@dataclass
class LeafTables:
    """Table (d): ``tw_*[k]`` = Q_{q_b}(e^{2 pi i k/R}), k < R/2, and the contiguous stage-s twiddle
    lists ``stages[s-1]`` = (Q_{q_b}(e^{2 pi i u 2^(K-s)/R}))_{u < 2^(s-1)} (re list, im list) that
    stage s replays once per block (MS §2.2 (d): R - 1 records in total, no strided table rescans;
    used by the routing="tape" leaf).  The stage entries are copies of tw entries, so both leaf
    variants multiply by the same integers."""

    lv: Level2D
    tw_re: list[int]
    tw_im: list[int]
    stages: list = field(default_factory=list)


def closure_guard(L: int, t: int, q: int) -> int:
    """Guard precision Q = q + ceil(lg L) + 2 ceil(lg(4t)) + 10 of the closure powering (br_r2 (4.21)
    with u_P -> v = 2^-q, SPEC v1.2 §5.10)."""
    return q + (L - 1).bit_length() + 2 * (4 * t - 1).bit_length() + 10


def closure_gamma(a_hat: int, L: int, q: int, t: int | None = None, method: str = "powering",
                  inst=None) -> int:
    """gamma-hat ~ 1/(1 - rho-hat^L) for the STORED rho-hat = -a_hat 2^-q, L even (r2 (4.17)).

    ``method="powering"`` (default; br_r2 §4.6 "Computing the closure table", eq. (4.21)): binary
    powering of a_hat 2^-q in [0, 1) with every product truncated at the guard precision
    Q = closure_guard(L, t, q) (error <= 2 L 2^-Q for a base in [0, 1]), guarded division
    2^{2Q} // (2^Q - pow) at scale Q (error < 2^-Q), then one final nearest rounding to q.  Since
    1 - a^L >= 1/(2t) (needs a_hat <= 1 - 1/(2t), r2 (4.16)), the pre-rounding error is at most
    (2t)^2 (2L + 1) 2^-Q + 2^-Q <= 2^-(q+10), so |gamma-hat - 1/(1 - rho-hat^L)| <= (1/2 + 2^-10) 2^-q,
    which meets (4.17) with v = 2^-q.  All operands are O(q + K)-bit (an O(P + K)-bit table
    computation, never an L q-bit power).

    ``method="exact"``: the exact rational 2^{q(L+1)} / (2^{qL} - a_hat^L), rounded once (error
    <= 1/2 2^-q); an L q-bit computation, kept only as the test oracle."""
    if L % 2:
        raise ValueError("cycle length must be even")
    if not 0 <= a_hat < (1 << q):
        raise ValueError("need 0 <= a-hat < 1")
    if inst is not None:
        inst.hit("tables.closure_" + method)
    if method == "exact":
        num = 1 << (q * (L + 1))
        den = (1 << (q * L)) - pow(a_hat, L)
        return div_half_even(num, den)
    if method != "powering":
        raise ValueError(method)
    if t is None:
        raise ValueError("the (4.21) powering needs the axis length t (guard and (4.16))")
    if 2 * t * a_hat > (2 * t - 1) << q:
        raise AssertionError("closure needs a-hat <= 1 - 1/(2t) (r2 (4.16))")
    Q = closure_guard(L, t, q)
    one = 1 << Q
    base = a_hat << (Q - q)                    # exact at scale Q
    acc, e = one, L
    while e:                                   # square-and-multiply, every product truncated
        if e & 1:
            acc = (acc * base) >> Q
        e >>= 1
        if e:
            base = (base * base) >> Q
    den = one - acc                            # >= 2^Q (1/(2t) - 2L 2^-Q) > 0
    g = (one << Q) // den                      # guarded division at scale Q
    return shr_half_even(g, Q - q)             # one final nearest rounding to q


def filter_row(delta: Fraction, r: int, m1: int, w: int, q: int, carrier: int = -1) -> FilterRow:
    """Build the guarded folded filter of one row (MS §6.1 (d); drop-in kernel r2 (8.1))."""
    h = certified.folded_kernel(delta, r, m1, w, q, carrier)   # h[d], d in [0, r)
    W = 2 * m1 + 1
    if W <= r:
        taps = [h[(m1 - b) % r] for b in range(W)]
        offset = m1
    else:
        taps = [h[(-a) % r] for a in range(r)]
        offset = 0
    return FilterRow(tuple(t[0] for t in taps), tuple(t[1] for t in taps), offset, q)


def twist_roots(r: int, q: int) -> tuple[list[int], list[int]]:
    """zeta-bar_k = Q_q(e^{pi i k/r}), k < r (MS §2.2 (b), Thm 3.1 steps 1 and 3)."""
    re, im = [], []
    for k in range(r):
        a, b = certified.unit_root(k, 2 * r, q)
        re.append(a)
        im.append(b)
    return re, im


def solver_tuple(u: int, t: int, L: int, w: int, q: int, inst=None) -> SolverTuple:
    """Solver tuple of column/axis digit u for axis length t and cycle length L (drop-in r2 §8)."""
    sc = certified.solver_coeffs(u, t, w, q)
    if sc.forward != (u < t // 2):
        raise AssertionError("dominance must be u < t/2 (r2 §8)")
    if not 0 <= sc.a < (1 << q):
        raise AssertionError("rho-hat must lie in (-1, 0]")
    return SolverTuple(sc.c0, sc.c1, sc.mu, -sc.a, closure_gamma(sc.a, L, q, t, inst=inst), sc.forward)


def level_tables_2d(ctx, lv: Level2D) -> LevelTables2D:
    """Tables (a)-(c) of a non-leaf level (cached in ``ctx.tables``)."""
    key = ("2d", lv.R, lv.p, lv.p_work, lv.q_child, lv.m1, lv.t1, lv.r, lv.B_slot)
    tab = ctx.tables.get(key)
    if tab is not None:
        return tab
    q, t1, r = lv.q_child, lv.t1, lv.r
    filters = [filter_row(Fraction(j1, t1), r, lv.m1, lv.p_work, q) for j1 in range(t1)]
    # Thm 6.3 proof: sum |2^q H-bar_a| <= (W~ + 1) 2^q for each real part (slot bound).
    for f in filters:
        require(len(f.taps_re) == lv.W_tilde, "folded filter row must have W~ taps (MS Thm 6.3)")
        require(sum(abs(v) for v in f.taps_re) <= (lv.W_tilde + 1) << q,
                "slot bound sum |2^q Re H-bar_a| <= (W~ + 1) 2^q violated (MS Thm 6.3 proof)")
        require(sum(abs(v) for v in f.taps_im) <= (lv.W_tilde + 1) << q,
                "slot bound sum |2^q Im H-bar_a| <= (W~ + 1) 2^q violated (MS Thm 6.3 proof)")
    packed_re = [pack(f.taps_re, lv.B_slot) for f in filters]
    packed_im = [pack(f.taps_im, lv.B_slot) for f in filters]
    zr, zi = twist_roots(r, q)
    solver = [solver_tuple(u2, r, t1, lv.p_work, q, inst=ctx.inst) for u2 in range(r)]
    tab = LevelTables2D(lv, filters, packed_re, packed_im, zr, zi, solver)
    ctx.tables[key] = tab
    return tab


def leaf_tables(ctx, lv: Level2D) -> LeafTables:
    """Table (d): Q_{q_b}(e^{2 pi i k/R}) for k < R/2 and the contiguous stage-s lists
    (Q_{q_b}(e^{2 pi i u 2^(K-s)/R}))_{u < 2^(s-1)}, s = 1..K (MS §2.2 (d)); cached."""
    key = ("leaf", lv.R, lv.q_b)
    tab = ctx.tables.get(key)
    if tab is not None:
        return tab
    re, im = [], []
    for k in range(max(1, lv.R // 2)):
        a, b = certified.unit_root(k, max(lv.R, 1), lv.q_b)
        re.append(a)
        im.append(b)
    K = lv.K
    stages = [([re[u << (K - s)] for u in range(1 << (s - 1))],
               [im[u << (K - s)] for u in range(1 << (s - 1))]) for s in range(1, K + 1)]
    tab = LeafTables(lv, re, im, stages)
    ctx.tables[key] = tab
    return tab
