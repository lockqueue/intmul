"""Multiply: two-call normalized root packing and exact recovery (MS §7.1 listing lines 701-725,
Lemma 2.3 ``lem:two-call``, Theorem 7.1 ``thm:main`` part 1).

    b = max(4, n.bit_length() - 1),  N = ceil(n / b),  K0 = (2N - 1).bit_length(),  R0 = 2^K0,
    p0 = 2b + 2K0 + 6.
    x_AB = (a_j + i b_j) 2^-b  on C~_{p0+2}  (exact),
    y = FastDFT(x_AB),  w_u = conj(RM_{p0+2}(y_u, y_u)),  z = FastDFT(w),
    c_j = round(-2^{2b-1} R0^2 Im z_j)  (= round(-numerator / 2^9) since p0 + 2 = 2b + 2K0 + 8),
    A*B = sum_j c_j 2^{jb}  (carry propagation in radix 2^b).
Recovery is exact because the pre-rounding error is < 3.19/128 < 1/2 (Thm 7.1 part 1).

Transform dispatch (SPEC §6.1-§6.2, §6.6): with ``schedule.bridge_d`` set (test mode) the
d-dimensional bridge runs with the schedule's middle (direct / Bluestein / Walsh).  Otherwise the
faithful dispatcher asks for the theorem shape: theorem mode is entered only if ``theorem_shape``
returns a shape and the cutoff certificate exists; at every feasible size it does not, and the 2D
FastDFT with the negative-carrier drop-in runs (the fallback, SPEC §6.4).  Dev-9
(``schedule.min_root_exponent``, test only) enlarges R0 = 2^K0 beyond the MS minimum, keeping
R0 >= 2N and recomputing p0.

Runtime safety net (``Ctx.safety_net``, on by default; NOT part of the algorithm): every returned
product is checked against the operands modulo fixed word-size moduli (:mod:`subnlogn.safety`).
"""

from __future__ import annotations

from fractions import Fraction

from .checks import require
from .context import Ctx
from .fixedpoint import FxVec, csquare
from .bits import carry_propagate, digits_to_int, int_to_digits
from .safety import check_product
from .theorem import THEOREM_ROWS, theorem_mode_shape

__all__ = ["multiply", "root_parameters"]


def root_parameters(n: int, min_K: int = 0) -> tuple[int, int, int, int, int]:
    """(b, N, K0, R0, p0) of the listing (lines 708-712); ``min_K`` > 0 is the test-only Dev-9
    enlargement K0 = max(K0, min_K) (the two-call identity holds for any R0 >= 2N - 1)."""
    b = max(4, n.bit_length() - 1)
    N = (n + b - 1) // b
    K0 = max((2 * N - 1).bit_length(), min_K)
    R0 = 1 << K0
    p0 = 2 * b + 2 * K0 + 6
    return b, N, K0, R0, p0


def bridge_dimension(schedule, K: int) -> int | None:
    """The bridge dimension run for R = 2^K under a forced ``schedule.bridge_d = d``:
    the largest d' <= d, d' >= 2, whose balanced geometry (``balanced_factors(K, d')``: r = 2^ceil(K/d'),
    t_i in {r/2, r}) satisfies the middle's hypotheses -- every t_i >= 2 (K >= d') for the direct middle
    (M2); additionally ell = ceil(K/d') >= 2 and 1 <= chunk_bits <= ell - 1 for the Bluestein and Walsh
    middles (Lemma 16, SPEC §5.2; SPEC_WALSH §5).  None if no such d' exists (then the 2D FastDFT
    runs)."""
    d = schedule.bridge_d
    for dd in range(min(d, K), 1, -1):
        if schedule.bridge_middle == "direct":
            return dd
        ell = -(-K // dd)
        if ell >= 2 and 1 <= schedule.chunk_bits <= ell - 1:
            return dd
    return None


def _transform(ctx: Ctx, x: FxVec, R: int, p: int) -> FxVec:
    """The transform backend.  With ``schedule.bridge_d = d`` the bridge runs in dimension
    ``bridge_dimension(schedule, K)`` (clamped below d when R is too small for the middle's
    hypotheses: counter ``bridge.d_clamped``); if no admissible dimension >= 2 exists, the 2D FastDFT
    runs (counter ``bridge.fallback_2d``)."""
    from .fastdft2d import fast_dft
    d = ctx.schedule.bridge_d
    K = R.bit_length() - 1
    if d is None:                                   # faithful dispatcher (SPEC §6.1-§6.2, SPEC_WALSH §9.1)
        row = THEOREM_ROWS[ctx.schedule.theorem_row]
        shape = theorem_mode_shape(K, row)
        if shape is None:
            ctx.inst.hit("multiply.fallback_2d")
            return fast_dft(ctx, x, R, p)
        return _theorem_transform(ctx, x, R, p, shape, row)
    d_eff = bridge_dimension(ctx.schedule, K)
    if d_eff is None:
        ctx.inst.hit("bridge.fallback_2d")
        return fast_dft(ctx, x, R, p)
    if d_eff < d:
        ctx.inst.hit("bridge.d_clamped")
    from .bridge.bridge_dft import bridge_dft
    return bridge_dft(ctx, x, R, p, d_eff)


def _theorem_transform(ctx: Ctx, x: FxVec, R: int, p: int, shape, row) -> FxVec:
    """Theorem mode (SPEC §6.1, SPEC_WALSH §9.1; unreachable at feasible sizes, see :mod:`subnlogn.theorem`):
    the bridge with the theorem shape's d and chunk width, the middle of the parameter row ``row`` (Bluestein for the
    printed row, Walsh for the SPEC_WALSH rows), the network engine under the schedule's layer policy (the row's
    preset in the faithful schedules: LAYER_THEOREM, LAYER_WALSH_47, LAYER_WALSH_46) and the address movements by
    Lemma 3/12 (``bridge_movement="lemma12"``).  A theorem-mode layer must carry the row's beta and C1 (C1 = None
    is the printed max(20, nu + 3) of the printed row); a test-mode layer is accepted (forced-branch tests).  The
    schedule's networks must be executable: the faithful schedules name the real h = 100 triple networks (SPEC §2.4,
    resolved lazily by ``m6.engine.network_descriptor``), for which RealNetworkNotExecutable is raised here, before
    any data moves; the forced-branch tests substitute the SPEC §2.5 fixtures C1 / B1."""
    from dataclasses import replace
    from .bridge.bridge_dft import bridge_dft
    from .m6.engine import require_executable
    layer = ctx.schedule.layer
    if layer.mode == "theorem" and (layer.beta != row.beta or
                                    not (layer.C1 == row.C1 or (layer.C1 is None and row.name == "printed"))):
        raise AssertionError(f"theorem-mode layer (beta={layer.beta}, C1={layer.C1}) does not match the "
                             f"parameter row {row.name!r} (beta={row.beta}, C1={row.C1})")
    require_executable(ctx.schedule.net_cx)
    require_executable(ctx.schedule.net_bit)
    ctx.inst.hit("multiply.theorem_mode")
    sched = ctx.schedule.with_(bridge_middle=row.middle, prop14_layer="network",
                               chunk_bits=shape.chunk_bits, bridge_movement="lemma12")
    return bridge_dft(replace(ctx, schedule=sched), x, R, p, shape.d)


def multiply(a: int, b: int, ctx: Ctx | None = None, *, schedule=None,
             products: str | None = None) -> int:
    """Exact product a * b of integers (signs handled outside the algorithm, which multiplies
    non-negative integers; MS Thm 7.1).

    Either pass a context, or a ``schedule`` (default: faithful) and ``products``: "python"
    (default; packed products by Python's exact ``*``, DEVIATIONS D1, counted as
    "python.big_product") or "hierarchy" (the faithful algorithm: packed products by the
    independent multiplier hierarchy of SPEC §6.5; asserts that no Python big product occurred)."""
    if ctx is None:
        from .schedule import faithful_schedule
        ctx = Ctx(schedule=schedule if schedule is not None else faithful_schedule(),
                  products=products if products is not None else "python")
    elif schedule is not None or (products is not None and products != ctx.products):
        raise ValueError("pass either a context or (schedule, products), not both")
    before = ctx.inst.counts.get("python.big_product", 0)
    out = _multiply(a, b, ctx)
    if ctx.products == "hierarchy":
        require(ctx.inst.counts.get("python.big_product", 0) == before,
                "hierarchy mode used Python's * on a packed product")
    return out


def _multiply(a: int, b: int, ctx: Ctx) -> int:
    sign = -1 if (a < 0) != (b < 0) else 1
    A, B = abs(a), abs(b)
    n = max(A.bit_length(), B.bit_length(), 1)
    if n <= ctx.schedule.mul_direct_bits:
        ctx.inst.hit("multiply.direct")
        return sign * (A * B)
    ctx.inst.hit("multiply.call")
    bb, N, K0, R0, p0 = root_parameters(n, ctx.schedule.min_root_exponent)
    q0 = p0 + 2
    mask = (1 << bb) - 1
    sh = q0 - bb
    # digits a_j, b_j of the operands: one linear bit-string split each (subnlogn.bits)
    xr = [d << sh for d in int_to_digits(A, bb, N)] + [0] * (R0 - N)
    xi = [d << sh for d in int_to_digits(B, bb, N)] + [0] * (R0 - N)
    shr = ctx.shr
    y = _transform(ctx, FxVec(xr, xi, q0), R0, p0)
    wr, wi = [], []
    wmul = ctx.word_mul()                       # pointwise squares by the word-scale multiplier
    for u in range(R0):
        sr, si = csquare(y.re[u], y.im[u], q0, shr, wmul)
        wr.append(sr)
        wi.append(-si)
    z = _transform(ctx, FxVec(wr, wi, q0), R0, p0)
    # c_j = round(-2^{2b-1} R0^2 Im z_j): shift s = q0 - (2b - 1) - 2 K0 = 9.
    s = q0 - (2 * bb - 1) - 2 * K0
    require(s == 9, "recovery shift q0 - (2b - 1) - 2 K0 must be 9 (MS Thm 7.1)")
    coeffs = [shr(-v, s) for v in z.im]
    # Certified recovery (MS Thm 7.1 part 1): with both transforms meeting the DFT contract
    # 2^-p max(1, ||x||) (the bridge's BR2 bound 0.18 2^-p is stronger), the exact pre-rounding values
    # -n_j / 2^9 lie within eps_cert = 3.19 * 2^(2b + 2K0 - 1 - p0) = 3.19/128 < 1/2 of the integers
    # c_j.  The measured distance |v_j - round(v_j)| is that error (round(v_j) = c_j since it is
    # < 1/2); it is asserted against eps_cert, which a transform violating its contract would break.
    eps_cert = Fraction(319, 100) * Fraction(1 << (2 * bb + 2 * K0 - 1), 1 << p0)
    require(eps_cert < Fraction(1, 2), "certified recovery bound must be < 1/2 (MS Thm 7.1)")
    worst = max(abs(Fraction(-v, 1 << s) - c) for v, c in zip(z.im, coeffs))
    ctx.inst.note("multiply.recovery_margin", (worst, eps_cert))
    require(worst <= eps_cert, lambda: f"recovery error {worst} above the certified bound {eps_cert} (MS Thm 7.1)")
    maxc = N * mask * mask
    require(all(0 <= c <= maxc for c in coeffs), "recovered coefficient out of range")
    require(all(c == 0 for c in coeffs[2 * N - 1:]), "coefficient beyond degree 2N-2")
    # Carry propagation in radix 2^b (Thm 7.1 part 1): one linear scan with a word-size carry,
    # then the digits are concatenated into the product (subnlogn.bits).
    prod = digits_to_int(carry_propagate(coeffs, bb), bb)
    require(prod.bit_length() <= 2 * n, "product bit above 2n - 1 (SPEC §6.8)")
    if ctx.safety_net:                  # runtime safety net, not part of the algorithm (subnlogn.safety)
        check_product(A, B, prod, ctx.inst)
    return sign * prod
