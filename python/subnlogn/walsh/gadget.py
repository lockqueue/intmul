"""The selective Walsh operation and exact controlled flips (SPEC_WALSH §2-§3; r5 §7.1,
l.1175-1245, eqs. (7.1)-(7.4)).

Records (engine format, SPEC v1.1 §4.0): a flat list indexed by the integer record address a (all 2^m0
addresses present); each record is (re list, im list) of integer numerators at one common scale.
Positions in this module are string positions counted from the MOST significant address bit, 0..m0-1
(SPEC_WALSH §1.4); every engine call converts them with eng(j) = m0 - 1 - j.

Identities (SPEC_WALSH §2.1, §3; H0 = (1/2)[[1, 1], [1, -1]], S = diag(1, i)):
    (H_all S_U)^3 = 2^-s ((1+i)/4)^q H_T,   so   H_T = 2^(s+3k+e) (-i)^k (1-i)^e (H_all S_U)^3   (q = 2k + e)
    CNOT^(tensor s) = 2^s H_T CZ H_T,       CZ(x) = (-1)^(sum_i x_{c_i} x_{t_i})
where T = the s wanted (target) positions of one slice, U = its q = D - s unwanted selected positions.
Chronological order: S_U, H_all, S_U, H_all, S_U, H_all, then the scalar (three S_U scans).

Exactness (SPEC_WALSH §2.4-§2.5): values are lifted from the grid p to p_* = p + 8d before a batch; the
completed full layers then land on grids <= 2^-(p+4D) < 2^-p_*, so every Q_{p_*} of the engine discards
only zeros (asserted: ``exact_boundary=True`` on every call), the batch result is a permutation of the
original p-grid values, and lowering back to p discards only zero bits (asserted).  Zero numerical error.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..checks import require
from ..m6.prop14 import map_records_with_address, mul_i_power_by_positions, simultaneous_H0, times_i_power

__all__ = ["WalshCtx", "lift", "lower_exact", "assert_disk", "scalar_correction", "selective_walsh",
           "cnot_batch"]


@dataclass
class WalshCtx:
    """Explicit context of the Walsh route (no global state).

    d       global layer dimension: every slice has D <= d chunks and the lift is p_* = p + 8d (§2.4)
    h       chunk width (``chunk_bits``, h = floor(d^c); 1 or 2 in tests)
    engine  None = Prop 14 base case; a :class:`subnlogn.m6.cnet.CCtx` = the complex-network path
    inst    optional :class:`subnlogn.instrument.Instrument`; counters "walsh.<name>" (SPEC_WALSH §8)
    mul     word-scale multiplier of the phase products (``Ctx.word_mul``); None = ``*``"""

    d: int
    h: int
    engine: object = None
    inst: object = None
    mul: object = None

    def hit(self, name: str, n: int = 1) -> None:
        if self.inst is not None:
            self.inst.hit("walsh." + name, n)


def lift(recs: list, k: int) -> list:
    """Append k fractional zero bits to every numerator (exact, SPEC_WALSH §2.4)."""
    return [([v << k for v in re], [v << k for v in im]) for re, im in recs]


def lower_exact(recs: list, k: int) -> list:
    """Remove k fractional bits, asserting that every removed bit is zero (lossless lowering, §3)."""
    mask = (1 << k) - 1
    if any(v & mask for re, im in recs for v in re + im):
        raise AssertionError("lowering p_* -> p would discard a nonzero bit (SPEC_WALSH §2.5, §3)")
    return [([v >> k for v in re], [v >> k for v in im]) for re, im in recs]


def assert_disk(recs: list, p: int) -> None:
    """Every coefficient lies in the closed unit disk on the 2^-p grid (SPEC_WALSH §2.6, §8)."""
    sq = 1 << (2 * p)
    for re, im in recs:
        for a, b in zip(re, im):
            if a * a + b * b > sq:
                raise AssertionError("value left the unit disk (SPEC_WALSH §2.6)")


def scalar_correction(rec, s: int, k: int, e: int):
    """Multiply one record by 2^(s+3k+e) (-i)^k (1-i)^e (R5 (7.4); SPEC_WALSH §2.2): a fourth-root phase,
    at most one factor (1 - i) ((1-i)(a+ib) = (a+b) + i(b-a)) and one left shift, in a single scan."""
    re, im = times_i_power(rec[0], rec[1], -k)
    if e:
        re, im = [a + b for a, b in zip(re, im)], [b - a for a, b in zip(re, im)]
    sh = s + 3 * k + e
    return [v << sh for v in re], [v << sh for v in im]


def selective_walsh(recs: list, sl, wanted, p_star: int, wctx: WalshCtx) -> list:
    """H_T on the wanted subset T of one slice's D selected positions (SPEC_WALSH §2.3; R5 (7.3)-(7.4)),
    using three completed full Prop 14 layers on all D positions interspersed with S_U, then the closed-
    form scalar.  ``recs`` are p_*-grid disk arrays (already lifted); returns H_T z exactly, a disk array
    at scale p_*.  ``sl`` is a :class:`subnlogn.walsh.positional.Slice`."""
    sel = list(sl.positions)
    wanted = list(wanted)
    if len(set(wanted)) != len(wanted) or not set(wanted) <= set(sel):
        raise ValueError("selective_walsh: the wanted positions must be distinct selected positions")
    unwanted = [j for j in sel if j not in wanted]
    m0 = sl.m0
    e_sel = [m0 - 1 - j for j in sel]
    e_un = [m0 - 1 - j for j in unwanted]
    for _ in range(3):
        if e_un:
            recs = mul_i_power_by_positions(recs, e_un)                    # S_U: one phase per record
            wctx.hit("su_scan")
        recs, sc = simultaneous_H0(recs, e_sel, p_star, p_star, wctx.engine, K=sl.h, rho=sl.rho,
                                   exact_boundary=True)                     # full layer; Q_{p_*} exact
        require(sc == p_star, "exact-boundary layer must return scale p_* (SPEC_WALSH §2.3)")
        wctx.hit("exact_boundary")
    s = len(wanted)
    k, e = divmod(len(unwanted), 2)
    recs = [scalar_correction(rec, s, k, e) for rec in recs]
    wctx.hit("gadget")
    wctx.hit("gadget.q_odd" if e else "gadget.q_even")
    if s == 0:
        wctx.hit("gadget.s0")
    if s == len(sel):
        wctx.hit("gadget.s_full")
    assert_disk(recs, p_star)
    return recs


def cnot_batch(recs: list, pairs, sl, p: int, wctx: WalshCtx) -> list:
    """CNOT^(tensor s) = 2^s H_T CZ H_T on disjoint (control, target) pairs (SPEC_WALSH §3; R5 (7.1)-(7.2)):
    the address involution x -> x with x_t ^= x_c for every pair, applied to the p-grid disk array
    ``recs``.  Targets distinct, inside ``sl``'s selected positions; controls distinct, anywhere else in
    the record address (prefix, suffix, unselected chunk bits, unwanted selected positions, leftovers);
    no control is a target.  Lift to p_* = p + 8d, H_T, CZ (one sign per record), H_T, x 2^s, lossless
    lowering to p (asserted).  Six full-layer calls; zero numerical error."""
    pairs = [tuple(pr) for pr in pairs]
    if not pairs:
        return recs
    ctl, tgt = [c for c, _ in pairs], [t for _, t in pairs]
    m0 = sl.m0
    if len(set(ctl + tgt)) != 2 * len(pairs):
        raise ValueError("cnot_batch: controls and targets must be distinct and disjoint")
    if not set(tgt) <= set(sl.positions) or any(not 0 <= c < m0 for c in ctl):
        raise ValueError("cnot_batch: targets must lie in the slice, controls in the record address")
    k8 = 8 * wctx.d
    p_star = p + k8
    z = lift(recs, k8)
    z = selective_walsh(z, sl, tgt, p_star, wctx)
    eb = [(m0 - 1 - c, m0 - 1 - t) for c, t in pairs]

    def cz(a: int, rec):
        if sum((a >> ec) & (a >> et) & 1 for ec, et in eb) & 1:
            return [-v for v in rec[0]], [-v for v in rec[1]]
        return rec
    z = map_records_with_address(z, cz)
    wctx.hit("cz_scan")
    z = selective_walsh(z, sl, tgt, p_star, wctx)
    s = len(pairs)
    z = [([v << s for v in re], [v << s for v in im]) for re, im in z]
    z = lower_exact(z, k8)
    assert_disk(z, p)
    wctx.hit("slice_batch")
    return z
