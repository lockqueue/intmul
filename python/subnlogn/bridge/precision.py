"""Exact certificate of the bridge precision schedule for the p_fft = P + 2 refinement (the paper's bridge
precision contract; BR2 Thm 2).

    q_work = f = P + 2,  p_fft = f,  component width w = f + 2 = P + 4,
    Prop 18 output width f + 2 + lg M,  deconvolution states f + K + 6,
    tables certified to error v = 2^-f (ours: correctly rounded, error <= v/2; closure exact).

``certify_bridge_precision`` is the schedule-level checker, transcribed with exact
integers and Fractions (sqrt 2 < 99/70); every inequality of the corrected error chain
the full error chain is asserted.  It returns the widths the code must honour; the code asserts them at
run time (solver states: ``bridge.deconv``; spread arrays: the 1/8 disk; Prop 18: the 0.701 disk
before narrowing).
"""

from __future__ import annotations

from fractions import Fraction
from math import prod

from ..checks import require

__all__ = ["certify_bridge_precision"]


def _clog2(n: int) -> int:
    require(n >= 1, "ceil(lg n) needs n >= 1")
    return (n - 1).bit_length()


def _log2_exact(n: int) -> int:
    require(n > 0 and n & (n - 1) == 0, "exact lg n needs a power of two")
    return n.bit_length() - 1


def certify_bridge_precision(p: int, t: tuple[int, ...]) -> dict:
    """Asserts the corrected error chain for p_fft = P + 2 and returns
    {P, fractional_bits f, component_bits f + 2, prop18_component_bits f + 2 + lg M,
    solver_component_bits f + K + 6, final_constant_upper}."""
    d = len(t)
    require(d >= 2, "bridge precision certificate: d >= 2")
    require(all(a >= 2 and a & (a - 1) == 0 for a in t), "bridge precision certificate: every t_i is a power of two >= 2")
    R = prod(t)
    K = _log2_exact(R)
    r = t[-1]
    ell = _log2_exact(r)
    require(ell >= 2, "bridge precision certificate: ell >= 2")
    require(all(a in (r // 2, r) for a in t), "bridge precision certificate: every t_i is r/2 or r")
    require(p >= max(8, K), "bridge precision certificate: p >= max(8, K)")
    D = R // t[0]
    M = R // r
    P = 2 * p + 12 * K + 32 * _clog2(p + K + 2) + 256
    w_alias = p + K + _clog2(d) + 20
    f = P + 2
    v = Fraction(1, 1 << f)
    require(P >= 20 and w_alias <= P and ell < f, "bridge precision certificate: P >= 20, w_alias <= P, ell < f")
    kd = _log2_exact(D)
    # exact input scaling (H <= p + 1)
    require(f >= 2 * p + (kd + 1) // 2 + 7, "bridge precision certificate: f >= 2p + ceil(lg D / 2) + 7")
    sqrt2_upper = Fraction(99, 70)
    require(sqrt2_upper ** 2 > 2, "bridge precision certificate: 99/70 > sqrt 2")
    Espread = 16 * d * (P + 1) * R * v                    # sqrt(D) replaced by R
    C18 = sqrt2_upper * M * (3 * ell + 1)
    E18 = C18 * v
    Etensor = (C18 + 12 * d + 16) * v
    EY = Espread + Etensor
    require(Espread < Fraction(1, 16), "bridge precision certificate: E_spread < 1/16")
    require(E18 < Fraction(1, 100), "bridge precision certificate: E_18 < 1/100")
    require(Etensor < Fraction(1, 16), "bridge precision certificate: E_tensor < 1/16")
    require(Etensor <= 16 * R * (K + 1) * v, "bridge precision certificate: E_tensor <= 16 R (K + 1) v")
    require(EY <= 32 * d * (P + 1) * R * v, "bridge precision certificate: E_Y <= 32 d (P + 1) R v")
    # solver hypotheses and growth margin
    require(v <= Fraction(1, 64 * max(t)), "bridge precision certificate: v <= 1/(64 max t)")
    require(64 * sum(t[1:]) * v < 1, "bridge precision certificate: 64 (t_2 + ... + t_d) v < 1")
    Esolver = 64 * d * R * R * v
    Earith = (1 << 14) * d * (P + 1) * R ** 3 * v
    require(128 * R * (D * EY + Esolver) <= Earith, "bridge precision certificate: 128 R (D E_Y + E_solver) <= E_arith")
    require(Earith <= Fraction(1, 1 << (p + 12)), "bridge precision certificate: E_arith <= 2^-(p+12)")
    Ealias = Fraction(3, 25) * (d - 1) * D * Fraction(1, 1 << w_alias)
    require(Ealias < Fraction(1, 1 << (p + 23)), "bridge precision certificate: E_alias < 2^-(p+23)")
    # spread packing margin
    require(16 * (2 * P + 1) * (1 << (2 * f)) < (1 << (4 * P + 15)), "bridge precision certificate: spread packing margin")
    final_constant = sqrt2_upper / 8 + Fraction(1, 1 << 12) + Fraction(1, 1 << 23)
    require(final_constant < Fraction(9, 50), "bridge precision certificate: final constant < 0.18")
    return {"P": P, "fractional_bits": f, "component_bits": f + 2,
            "prop18_component_bits": f + 2 + _log2_exact(M), "solver_component_bits": f + K + 6,
            "final_constant_upper": final_constant}
