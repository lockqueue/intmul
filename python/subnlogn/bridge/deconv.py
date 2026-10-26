"""Bridge deconvolution B_2^{-1}, B_3^{-1}, ..., B_d^{-1} in CHRONOLOGICAL order (Lemma A:
r2 (3.9), r3 §3.3; the alias operators do not commute).

B_h acts on natural frequency order: (B_h Z)_k = c0(u_h(k)) Z_k + c1(u_h(k)) Z_{k - q_h mod R},
q_h = R / A_h.  It splits into q_h independent cycles k_v = v q_h + s (0 <= v < A_h) on which
u_h(k) is constant (r2 §6.2), so each cycle is one uniform cyclic solve of length L = A_h with
the drop-in coefficients c0 = G((u_h + 1/2)/t_h), c1 = G((u_h + 1/2)/t_h - 1) (Lemma B, r2 §4.3).
The branch is u_h < t_h/2 (forward) or not (backward, with the +1 shift); the closure gamma uses
the cycle length A_h, not t_h (implementer spec r1 §7.7).  Error per stage (r2 (4.20), r3 (4.21)):
<= 32 t_h^2 2^-P max(1, ||Y||), independent of A_h.
"""

from __future__ import annotations

from ..fixedpoint import FxVec
from ..solver import cyclic_solve
from ..tables import SolverTuple, solver_tuple

__all__ = ["bridge_solver_tuple", "deconv_axis"]


def bridge_solver_tuple(ctx, u: int, t: int, L: int, w: int, q: int) -> SolverTuple:
    key = ("bridge_solver", u, t, L, w, q)
    st = ctx.tables.get(key)
    if st is None:
        st = solver_tuple(u, t, L, w, q, inst=ctx.inst)
        ctx.tables[key] = st
    return st


def deconv_axis(ctx, Y: FxVec, geom, h: int, w: int) -> FxVec:
    """Apply the cyclic solver for B_h to every cycle of axis h (natural frequency order)."""
    q = Y.q
    t = geom.tt(h)
    L = geom.A(h)
    shr = ctx.shr
    out_re = list(Y.re)
    out_im = list(Y.im)
    # declared component width of deconvolution states and prefixes: f + K + 6 with f = q
    # (the p_fft = P + 2 refinement); magnitude bits = width - 1
    width = q + geom.K + 5
    for cyc in geom.cycles(h):
        u = geom.u_digit(h, cyc[0])
        st = bridge_solver_tuple(ctx, u, t, L, w, q)
        zr, zi = cyclic_solve([Y.re[k] for k in cyc], [Y.im[k] for k in cyc], st.mu, st.rho,
                              st.gamma, st.forward, q, shr, ctx.inst, max_bits=width,
                              mul=ctx.word_mul())
        for v, k in enumerate(cyc):
            out_re[k] = zr[v]
            out_im[k] = zi[v]
    ctx.inst.hit("bridge.deconv_axis")
    return FxVec(out_re, out_im, q)
