"""Proposition 14: the simultaneous normalized butterfly layer H0^{tensor D} (SPEC §4.4, §4.7, §4.9;
Pr (13)-(18), (25), L1888-1904, L2440-2595), base case and building blocks.

Records are ring records of R_r stored as (re list, im list) of integer numerators sharing one
scale (fractional bits), indexed by their address x (as in :mod:`subnlogn.middle3.synth`).  The D
selected bits are given by their bit indices (from the LSB of the address).

Identities used (reading R3: C = HSH = aI + bX, a = (1+i)/2, b = (1-i)/2; H0 = (1/2)[[1,1],[1,-1]]):
    H0 = b S C S  with S = diag(1, i),   hence   H0^{tD} = b^D S_D C^{tD} S_D        (18)
where S_D multiplies a record by i^{x_1+...+x_D} (sum of the selected bits) and
b^D = (-i/2)^{floor(D/2)} b^{D mod 2} (b^2 = -i/2).  A single C kernel on one selected bit maps the
aligned pair (u, v) (bit 0, bit 1) to ((s + t)/2, (s - t)/2) with s = u + v, t = i(u - v)  (25).

Exactness: every halving is exact because the scale (number of fractional bits) is increased
instead of dividing; this is the guarded format of §4.8 (p + Delta fractional bits).  The layer
output is Q_p(H0^{tD} z): exactly one truncation toward zero at the end (Prop 14), a disk-grid
array with error < sqrt(2) 2^-p.  The base case (individual exact C kernels on all D selected
bits, §4.9) is valid for all parameters; the network path (§4.5-4.6, M6) must agree bit for bit.
"""

from __future__ import annotations

from ..fixedpoint import shr_trunc

__all__ = ["times_i_power", "s_phase", "mul_i_power_by_positions", "map_records_with_address",
           "c_single_exact", "finish_layer", "simultaneous_H0_base", "simultaneous_H0",
           "hadamard_direct"]


def times_i_power(re: list[int], im: list[int], k: int) -> tuple[list[int], list[int]]:
    """Multiply a record by i^k (exact signed swap of components)."""
    k %= 4
    if k == 0:
        return re, im
    if k == 1:
        return [-v for v in im], list(re)
    if k == 2:
        return [-v for v in re], [-v for v in im]
    return list(im), [-v for v in re]


def mul_i_power_by_positions(recs: list, positions: list[int]) -> list:
    """Multiply the record at address a by i^{sum_{j in positions} x_j}, x_j = (a >> j) & 1: one
    phase per record applied to all its coefficients (SPEC v1.1 §4.0).  S_D of identity (18) is the
    case positions = the D selected bits."""
    out = []
    for x, (re, im) in enumerate(recs):
        k = sum((x >> b) & 1 for b in positions)
        out.append(times_i_power(re, im, k))
    return out


#: S_D of identity (18) (historical name of :func:`mul_i_power_by_positions`).
s_phase = mul_i_power_by_positions


def map_records_with_address(recs: list, fn) -> list:
    """Per-record scan calling ``fn(a, record)`` with the integer record address a (bit j of a is
    x_j, counted from the LSB; SPEC v1.1 §4.0).  Used for CZ diagonals and complex twiddles."""
    return [fn(a, rec) for a, rec in enumerate(recs)]


def c_single_exact(recs: list, bit: int) -> list:
    """One C kernel (eq. (25)) on a selected address bit, exact: returns numerators of the result
    at scale +1 (the halving consumes one reserved fractional bit)."""
    out = list(recs)
    m = 1 << bit
    for x in range(len(recs)):
        if x & m:
            continue
        (ur, ui), (vr, vi) = recs[x], recs[x | m]
        sr = [a + b for a, b in zip(ur, vr)]
        si = [a + b for a, b in zip(ui, vi)]
        tr = [-(a - b) for a, b in zip(ui, vi)]          # t = i (u - v): re(t) = -(im u - im v)
        ti = [a - b for a, b in zip(ur, vr)]              #               im(t) = re u - re v
        out[x] = ([a + b for a, b in zip(sr, tr)], [a + b for a, b in zip(si, ti)])
        out[x | m] = ([a - b for a, b in zip(sr, tr)], [a - b for a, b in zip(si, ti)])
    return out


def finish_layer(recs: list, scale: int, p: int, *, truncate: bool = True,
                 exact_boundary: bool = False, check_disk: bool = False):
    """The end of Prop 14 (SPEC §4.7): return the exact output (truncate=False), or exactly one
    Q_p (truncation toward zero, ``shr_trunc``).  ``exact_boundary`` asserts that Q_p discards only
    zero bits (the caller proved the exact output lies on the p-grid; SPEC_WALSH §2.5);
    ``check_disk`` asserts |numerator| <= 2^p and the disk |z| <= 1 (H0 has absolute row sums 1 and
    Q_p does not grow components, so a disk-grid input gives a disk-grid output)."""
    if not truncate:
        return recs, scale
    s = scale - p
    if s < 0:
        raise ValueError("Q_p needs the exact scale to be at least p")
    if exact_boundary and s:
        mask = (1 << s) - 1
        if any(v & mask for re, im in recs for v in re + im):
            raise AssertionError("exact_boundary: Q_p would discard a nonzero bit (SPEC §4.7)")
    out = [([shr_trunc(v, s) for v in re], [shr_trunc(v, s) for v in im]) for re, im in recs]
    if check_disk:
        one, sq = 1 << p, 1 << (2 * p)
        for re, im in out:
            for a, b in zip(re, im):
                if abs(a) > one or abs(b) > one or a * a + b * b > sq:
                    raise AssertionError("Prop 14 output left the unit disk (SPEC §4.7)")
    return out, p


def simultaneous_H0_base(recs: list, sel_bits: list[int], scale: int, p: int,
                         truncate: bool = True, *, K: int = 1, rho: int = 0,
                         exact_boundary: bool = False, check_disk: bool = False):
    """Prop 14 base case: S_D, C^{tD} (individual exact kernels), S_D, b^D, then Q_p (SPEC §4.7,
    §4.9).  Returns (records, scale'): scale' = p if truncating, else the exact scale.  ``K`` and
    ``rho`` (chunk geometry) are accepted for interface parity with the network layer; the base
    case does not need them."""
    D = len(sel_bits)
    out = s_phase(recs, sel_bits)
    for b in sel_bits:
        out = c_single_exact(out, b)
    scale += D
    out = s_phase(out, sel_bits)
    t, odd = divmod(D, 2)
    out = [times_i_power(re, im, -t) for re, im in out]   # (-i/2)^t: i^{-t} ...
    scale += t                                            # ... and t exact halvings
    if odd:                                               # factor b = (1 - i)/2: z -> (z - i z)/2
        nxt = []
        for re, im in out:
            ir, ii = times_i_power(re, im, 1)
            nxt.append(([a - c for a, c in zip(re, ir)], [a - c for a, c in zip(im, ii)]))
        out = nxt
        scale += 1
    return finish_layer(out, scale, p, truncate=truncate, exact_boundary=exact_boundary,
                        check_disk=check_disk)


def simultaneous_H0(recs: list, sel_bits: list[int], scale: int, p: int, engine=None, *,
                    K: int = 1, rho: int = 0, truncate: bool = True,
                    exact_boundary: bool = False, check_disk: bool = True):
    """The Prop 14 engine entry used by both routes (SPEC v1.1 §4.0, §4.7): ``engine=None`` runs
    the base case (§4.9), a :class:`subnlogn.m6.cnet.CCtx` runs the complex-network path
    (§4.5-§4.6, policy-driven).  Both return bit-identical outputs (records, scale')."""
    if engine is None:
        return simultaneous_H0_base(recs, sel_bits, scale, p, truncate, K=K, rho=rho,
                                    exact_boundary=exact_boundary, check_disk=check_disk)
    from .cnet import simultaneous_H0_network
    return simultaneous_H0_network(recs, sel_bits, scale, p, engine, K=K, rho=rho,
                                   truncate=truncate, exact_boundary=exact_boundary,
                                   check_disk=check_disk)


def hadamard_direct(recs: list, sel_bits: list[int], scale: int, p: int, truncate: bool = True,
                    **_geometry):
    """Reference: the tensor H0^{tD} applied by individual exact H0 butterflies, then Q_p (the M3
    direct layer of SPEC §5.11); used to cross-check the identity (18) bit for bit."""
    out = list(recs)
    for b in sel_bits:
        m = 1 << b
        for x in range(len(out)):
            if not x & m:
                (ar, ai), (br, bi) = out[x], out[x | m]
                out[x] = ([u + v for u, v in zip(ar, br)], [u + v for u, v in zip(ai, bi)])
                out[x | m] = ([u - v for u, v in zip(ar, br)], [u - v for u, v in zip(ai, bi)])
    scale += len(sel_bits)
    if truncate:
        s = scale - p
        out = [([shr_trunc(v, s) for v in re], [shr_trunc(v, s) for v in im]) for re, im in out]
        scale = p
    return out, scale
