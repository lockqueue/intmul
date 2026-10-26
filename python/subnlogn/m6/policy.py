"""Parameters of the Proposition 14 engine: :class:`LayerPolicy` (SPEC v1.1 §4.0) and the integer
rules that read it -- the leaf test (§4.5), the batching plan (§4.6) and the guard width (§4.8).

Sources: Pr = the plain-text rendering of [OAI26]; the printed values are Pr L2289-2298
(beta = 1/2, leaf e < d^beta), L2228-2242 (q0, k0, rows), L2353-2365 (E, B, nu, C1, C0, Delta),
L2440-2456 (Prop 14).  Every constant that the Walsh route (SPEC_WALSH) retunes is a field
of an explicit policy carried in the engine context; nothing here is global state.  All rules are
exact integer computations (no floats, and no huge powers: comparisons e^b < d^a stop early).

Presets: ``LAYER_THEOREM`` (the printed Prop 14; the faithful schedule) and ``LAYER_TEST`` (forced
batching Dev-4, count leaf rule Dev-4, compiled guard Dev-3; the test schedule, SPEC §6.3).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..theorem import ROW_WALSH_46, ROW_WALSH_47

__all__ = ["LayerPolicy", "LAYER_THEOREM", "LAYER_TEST", "LAYER_WALSH_47", "LAYER_WALSH_46", "capped_pow",
           "is_leaf", "ceil_log", "ceil_log2", "base_m_pieces", "max_level", "BatchPlan", "batch_plan",
           "guard_exponent", "published_delta", "compiled_delta", "layer_delta", "MAX_GUARD_BITS",
           "GuardInfeasible"]

#: Largest guard width (bits per component) the RAM backend will allocate.  The published
#: Delta = ceil(C0 d^C1) is about 3.7e143 bits already at d = 2 with C1 = 14 (C0 ~ 2.27e139; SPEC §4.10), so
#: asking for it raises :class:`GuardInfeasible` instead of attempting the allocation.  Not a deviation: the published
#: bound is computed exactly (and tested); it is simply not executable at feasible sizes.
MAX_GUARD_BITS = 1 << 18


class GuardInfeasible(ValueError):
    """The requested guard width cannot be allocated (use ``guard="compiled"``, Dev-3)."""


@dataclass(frozen=True)
class LayerPolicy:
    """SPEC §4.0 verbatim; defaults are the printed values [Pr L2289-2298, L2353-2365].

    mode      "theorem" | "test" (test runs claim correctness only, never cost)
    beta      leaf exponent (printed 1/2; Walsh rows 1/8 or 1/64)
    leaf      "beta": leaf iff e == 1 or e < d^beta | "count": leaf iff e <= C_leaf_e (Dev-4)
    C_leaf_e  threshold of the "count" rule
    C1        guard exponent; None = printed max(20, nu + 3)
    guard     "published": Delta = ceil(C0 d^C1) | "compiled": the §4.8 depth recursion (Dev-3)
    batching  "theorem": q0 = ceil(lg W) ceil(log_m 2d), k0 = ceil(log_m d) | "forced" (Dev-4)
    forced_q0 test only (Dev-11): with batching "theorem", reserve this many leading chunks
    bad_set   Lemma 13 exceptional set (§4.2): "eq23" | "safe_segments" (Dev-5)
    row       ParameterRow (certificate data only)
    """

    mode: str = "theorem"
    beta: Fraction = Fraction(1, 2)
    leaf: str = "beta"
    C_leaf_e: int = 1
    C1: int | None = None
    guard: str = "published"
    batching: str = "theorem"
    forced_q0: int | None = None
    bad_set: str = "eq23"
    row: object | None = None

    def __post_init__(self):
        checks = (("mode", ("theorem", "test")), ("leaf", ("beta", "count")),
                  ("guard", ("published", "compiled")), ("batching", ("theorem", "forced")),
                  ("bad_set", ("eq23", "safe_segments")))
        for name, allowed in checks:
            if getattr(self, name) not in allowed:
                raise ValueError(f"LayerPolicy.{name} = {getattr(self, name)!r} not in {allowed}")
        if not isinstance(self.beta, Fraction) or not 0 < self.beta <= 1:
            raise ValueError("LayerPolicy.beta must be a Fraction in (0, 1]")
        if self.C_leaf_e < 1:
            raise ValueError("LayerPolicy.C_leaf_e must be >= 1")
        if self.C1 is not None and self.C1 < 1:
            raise ValueError("LayerPolicy.C1 must be a positive integer or None")
        if self.forced_q0 is not None:
            if self.forced_q0 < 0:
                raise ValueError("LayerPolicy.forced_q0 must be >= 0")
            if self.batching != "theorem":
                raise ValueError("forced_q0 (Dev-11) modifies theorem batching only")
            if self.mode != "test":
                raise ValueError("forced_q0 is test-only (Dev-11)")


LAYER_THEOREM = LayerPolicy()
LAYER_TEST = LayerPolicy(mode="test", leaf="count", guard="compiled", batching="forced")
#: SPEC_WALSH §1.4: the retuned Prop 14 policies of the Walsh rows (theorem mode, SPEC §4.0 theorem defaults: guard
#: "published", batching "theorem"; row = the SPEC_WALSH §1.3 row, certificate data only).
LAYER_WALSH_47 = LayerPolicy(beta=Fraction(1, 8), C1=20, row=ROW_WALSH_47)
LAYER_WALSH_46 = LayerPolicy(beta=Fraction(1, 64), C1=14, row=ROW_WALSH_46)


def capped_pow(base: int, exp: int, cap: int) -> int:
    """base**exp if it is <= cap, else cap + 1 (repeated multiplication, stopping early)."""
    v = 1
    for _ in range(exp):
        v *= base
        if v > cap:
            return cap + 1
    return v


def is_leaf(e: int, d: int, pol: LayerPolicy) -> bool:
    """Leaf test of the C^{tensor e} recursion (SPEC §4.0/§4.5; Pr L2296-2298 "Stop recursion when
    e < d^beta"): e == 1, or e^b < d^a for beta = a/b (exact), or the count rule e <= C_leaf_e."""
    if e == 1:
        return True
    if pol.leaf == "count":
        return e <= pol.C_leaf_e
    a, b = pol.beta.numerator, pol.beta.denominator
    da = d ** a                                   # a is the small numerator of beta
    return capped_pow(e, b, da) < da


def ceil_log(x: int, m: int) -> int:
    """Least j >= 0 with m^j >= x (integers only; x >= 1, m >= 2)."""
    if x < 1 or m < 2:
        raise ValueError("ceil_log needs x >= 1 and m >= 2")
    j, v = 0, 1
    while v < x:
        v *= m
        j += 1
    return j


def ceil_log2(x: int) -> int:
    """Least j >= 0 with 2^j >= x."""
    return ceil_log(x, 2)


def base_m_pieces(n: int, m: int) -> list[int]:
    """Canonical partition of n consecutive chunks into a_j pieces of m^j chunks, n = sum a_j m^j,
    widths in decreasing j from the most significant end (SPEC §3.7, §4.6; Pr L2333-2335)."""
    digits = []
    v = n
    while v:
        digits.append(v % m)
        v //= m
    out: list[int] = []
    for j in range(len(digits) - 1, -1, -1):
        out += [m ** j] * digits[j]
    return out


def max_level(pieces, m: int) -> int:
    """max j over pieces of m^j chunks (0 for no pieces)."""
    return max((ceil_log(p, m) for p in pieces), default=0)


@dataclass(frozen=True)
class BatchPlan:
    """How one layer of D selected chunks is batched (SPEC §4.6; Pr L2228-2242, L2333-2342).

    individual  D <= q0: individual C kernels on every chunk, no network (§4.9)
    q0          leading (most significant) chunks processed individually and joined into the row
                field (0 for forced batching, whose row field is an artificial unit field)
    k0          network depth the padded row count must support (rows padded to a multiple of W^k0)
    pieces      base-m pieces of the remaining chunks, most significant first
    row_len     genuine rows per prefix: 2^(q0 K) (1 for forced batching)
    row_pad     padded rows per prefix: the next multiple of W^k0
    """

    individual: bool
    q0: int
    k0: int
    pieces: tuple[int, ...]
    row_len: int
    row_pad: int


def batch_plan(D: int, d: int, K: int, net, pol: LayerPolicy) -> BatchPlan:
    """SPEC §4.6 ``batched_C_layer`` parameter rules: theorem q0 = ceil(lg W) ceil(log_m 2d) and
    k0 = ceil(log_m d) [Pr L2230-2234], or forced_q0 with k0 = the deepest piece (Dev-11); forced
    batching: a unit row field, k0 = the deepest piece (Dev-4)."""
    m, W = net.m, net.W
    if pol.batching == "theorem":
        q0 = ceil_log2(W) * ceil_log(2 * d, m) if pol.forced_q0 is None else pol.forced_q0
        if D <= q0:
            return BatchPlan(True, D, 0, (), 1, 1)
        pieces = tuple(base_m_pieces(D - q0, m))
        k0 = ceil_log(d, m) if pol.forced_q0 is None else max_level(pieces, m)
        row_len = 1 << (q0 * K)
    else:
        q0 = 0
        pieces = tuple(base_m_pieces(D, m))
        k0 = max_level(pieces, m)
        row_len = 1
    unit = W ** k0
    return BatchPlan(False, q0, k0, pieces, row_len, -(-row_len // unit) * unit)


def guard_exponent(pol: LayerPolicy, net) -> int:
    """C1 of the published guard (SPEC §4.0/§4.8; Pr L2353-2365): B = s + 64 (W + m + 1)^3,
    nu = min{j >= 1 : m^j >= B}, C1 = max(20, nu + 3) unless the policy fixes it; the proof needs
    C1 >= nu + 3 (growth <= 26 m B^2 d^(nu+2) < C0 d^(nu+3), Pr L2413-2425), asserted."""
    B = net.s + 64 * (net.W + net.m + 1) ** 3
    nu = max(1, ceil_log(B, net.m))
    C1 = max(20, nu + 3) if pol.C1 is None else pol.C1
    if C1 < nu + 3:
        raise AssertionError(f"guard exponent C1 = {C1} < nu + 3 = {nu + 3} (Pr L2413-2425)")
    return C1


def published_delta(pol: LayerPolicy, net, d: int) -> int:
    """Published guard Delta = ceil(C0 d^C1), C0 = 128 m B^2 (SPEC §4.8; Pr L2353-2365); exact
    (C0 and d are integers, so the ceiling is the value itself)."""
    B = net.s + 64 * (net.W + net.m + 1) ** 3
    return 128 * net.m * B * B * d ** guard_exponent(pol, net)


def compiled_delta(net, D: int, d: int, K: int, pol: LayerPolicy) -> int:
    """Compiled guard for the supplied network (SPEC §4.8, Dev-3; same proof as Pr L2373-2432):
    A(e) = 8e at a leaf, A(e) = s A(e/m) + E_net at an internal node,
    E_net = 2 sum_gates sum_outputs nnz(row) + 4 s + 4 W + 4, and
    Delta = sum_pieces A(e_piece) + 8 (#individually processed chunks) + floor(D/2) + 9 + 16."""
    m, W, s = net.m, net.W, net.s
    E_net = 2 * sum(sum(1 for z in row if not z.is_zero()) for g in net.gates for row in g.matrix)
    E_net += 4 * s + 4 * W + 4

    def A(e: int) -> int:
        if is_leaf(e, d, pol) or e % m:
            return 8 * e
        return s * A(e // m) + E_net

    plan = batch_plan(D, d, K, net, pol)
    if plan.individual:
        return 8 * D + D // 2 + 9 + 16
    return sum(A(e) for e in plan.pieces) + 8 * plan.q0 + D // 2 + 9 + 16


def layer_delta(net, D: int, d: int, K: int, pol: LayerPolicy) -> int:
    """The guard width the engine allocates (SPEC §4.8): compiled or published per the policy;
    raises :class:`GuardInfeasible` above :data:`MAX_GUARD_BITS`."""
    delta = compiled_delta(net, D, d, K, pol) if pol.guard == "compiled" else \
        published_delta(pol, net, d)
    if delta > MAX_GUARD_BITS:
        raise GuardInfeasible(f"guard width Delta = {delta} bits ({pol.guard}) exceeds "
                              f"{MAX_GUARD_BITS}; the published bound is not executable at "
                              f"feasible sizes, use guard='compiled' (Dev-3)")
    return delta
