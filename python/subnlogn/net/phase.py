"""Complex (phase) frames as exact Gaussian-dyadic operators, and the exact identities checked on them.

SPEC §2.3 [Pr L1173-1310], reading R3: C = HSH = aI + bX with a = (1+i)/2, b = (1-i)/2, and

    C_U = H^{(x)m} diag(i^{q_U(x)}) H^{(x)m},   (C_U)[a][b] = 2^{-m} sum_x (-1)^{(a+b).x} i^{q_U(x)}

(no sqrt(2): the two normalizations of H combine to 2^{-m}).  Zero label -> I, full label -> C^{(x)m} since
q_F(x) = wt(x) [Pr L1285-1286].  Dense 2^m x 2^m matrices are materialized only for small m; for larger m the same
identities are checked on the diagonal (Hadamard-basis) exponents, which is equivalent because every C_U, X_v and
Z_z H = H X_z is diagonalized by H^{(x)m}.
"""

from __future__ import annotations

from functools import lru_cache

from . import f2
from .zi2 import A_COEF, B_COEF, ONE, ZERO, ZI2, i_pow

#: Largest m for which validation multiplies dense 2^m x 2^m Gaussian-dyadic matrices.
DENSE_MAX_M = 4
#: Largest m for which identities are checked at all 2^m Hadamard-basis points (exact); beyond: O(m^2) points.
EXHAUSTIVE_MAX_M = 10


# ----------------------------------------------------------------------------------------------- exponents
def q_values(U, m: int) -> list[int]:
    """[q_U(x) for x in F2^m] (SPEC §2.3); exact, O(2^m dim U)."""
    if not U:
        return [0] * (1 << m)
    P = f2.Projector(U)
    return [P.q(x) for x in range(1 << m)]


def full_q_values(m: int) -> list[int]:
    """q_F(x) = wt(x) mod 4 for the full label F = F2^m [Pr L1286]."""
    return [x.bit_count() % 4 for x in range(1 << m)]


# ----------------------------------------------------------------------------------------------- dense matrices
def kernel_from_exponents(exps, m: int) -> tuple[ZI2, ...]:
    """c(y) = 2^{-m} sum_x (-1)^{x.y} i^{e(x)}: the entry (a, b) of H^m diag(i^e) H^m is c(a xor b) (exact)."""
    n = 1 << m
    out = []
    for y in range(n):
        re = im = 0
        for x in range(n):
            e = exps[x] % 4
            s = -1 if (x & y).bit_count() & 1 else 1
            if e == 0:
                re += s
            elif e == 1:
                im += s
            elif e == 2:
                re -= s
            else:
                im -= s
        out.append(ZI2(re, im, m))
    return tuple(out)


def dense_from_exponents(exps, m: int) -> list[list[ZI2]]:
    """The dense matrix H^{(x)m} diag(i^{e(x)}) H^{(x)m} entrywise from the defining sum (SPEC §2.3)."""
    c = kernel_from_exponents(exps, m)
    n = 1 << m
    return [[c[a ^ b] for b in range(n)] for a in range(n)]


def dense_C(U, m: int) -> list[list[ZI2]]:
    """C_U as an exact 2^m x 2^m Gaussian-dyadic matrix (small m only) [Pr L1207]."""
    return dense_from_exponents(q_values(U, m), m)


def dense_C_inverse(U, m: int) -> list[list[ZI2]]:
    """C_U^{-1} = H^m diag(i^{-q_U}) H^m (entries are again Gaussian integers / 2^m) [Pr L1208-1209]."""
    return dense_from_exponents([-q for q in q_values(U, m)], m)


def dense_identity(m: int) -> list[list[ZI2]]:
    """I on F2^m-indexed arrays."""
    n = 1 << m
    return [[ONE if a == b else ZERO for b in range(n)] for a in range(n)]


def dense_X(v: int, m: int) -> list[list[ZI2]]:
    """X_v with (X_v f)(x) = f(x + v) [Pr L1223]."""
    n = 1 << m
    return [[ONE if b == a ^ v else ZERO for b in range(n)] for a in range(n)]


def dense_Z(mask: int, m: int) -> list[list[ZI2]]:
    """Z on the coordinates of ``mask``: diag((-1)^{wt(mask & x)}) [Pr L1295-1304]."""
    n = 1 << m
    return [[(ZI2(-1) if (mask & a).bit_count() & 1 else ONE) if a == b else ZERO for b in range(n)]
            for a in range(n)]


def dense_Cv(v: int, m: int, sign: int = 1) -> list[list[ZI2]]:
    """C_v = aI + bX_v (sign +1) or C_v^{-1} = bI + aX_v (sign -1) (Prop 8, (15)-(16); R3) [Pr L1815]."""
    a, b = (A_COEF, B_COEF) if sign == 1 else (B_COEF, A_COEF)
    n = 1 << m
    return [[(a if c == r else ZERO) + (b if c == r ^ v else ZERO) for c in range(n)] for r in range(n)]


def matmul(A, B) -> list[list[ZI2]]:
    """Exact product of dense ZI2 matrices."""
    n, p = len(A), len(B[0])
    out = []
    for i in range(n):
        row = [ZERO] * p
        for k, a in enumerate(A[i]):
            if a.is_zero():
                continue
            Bk = B[k]
            for j in range(p):
                if not Bk[j].is_zero():
                    row[j] = row[j] + a * Bk[j]
        out.append(row)
    return out


def scalar_times(z: ZI2, A) -> list[list[ZI2]]:
    """z * A."""
    return [[z * x for x in r] for r in A]


def kron(A, B) -> list[list[ZI2]]:
    """Kronecker product of dense ZI2 matrices (index i1*rows(B) + i2)."""
    return [[a * b for a in ra for b in rb] for ra in A for rb in B]


#: The 2 x 2 kernel C = [[a, b], [b, a]] (R3).
C2 = [[A_COEF, B_COEF], [B_COEF, A_COEF]]
H2_UNNORM = [[ONE, ONE], [ONE, ZI2(-1)]]
S2 = [[ONE, ZERO], [ZERO, ZI2(0, 1)]]
Z2 = [[ONE, ZERO], [ZERO, ZI2(-1)]]
X2 = [[ZERO, ONE], [ONE, ZERO]]


def C_tensor(m: int) -> list[list[ZI2]]:
    """C^{(x)m} by repeated Kronecker products of the 2 x 2 kernel (index convention of ``f2``: bit i = coordinate
    i, so the Kronecker factor for coordinate m-1 is outermost)."""
    M = [[ONE]]
    for _ in range(m):
        M = kron(C2, M)
    return M


# ----------------------------------------------------------------------------------------------- endpoint identities
def corrected_route_dense(U_in, U_out, z_pre: int, z_post: int, theta: int, m: int) -> bool:
    """i^theta Z_{z_post} C_{U_out} C_{U_in}^{-1} Z_{z_pre} == C^{(x)m}, multiplying dense 2^m x 2^m matrices
    (SPEC §2.6 item 6, small m)."""
    K = matmul(dense_Z(z_post, m), matmul(dense_C(U_out, m), matmul(dense_C_inverse(U_in, m), dense_Z(z_pre, m))))
    return scalar_times(i_pow(theta), K) == C_tensor(m)


def corrected_route_exhaustive(U_in, U_out, z_pre: int, z_post: int, theta: int, m: int) -> bool:
    """The same identity on all 2^m Hadamard-basis points: since Z_z H^m = H^m X_z, the corrected operator is
    H^m X_{z_post} diag(i^{theta + q_out - q_in}) X_{z_pre} H^m, which equals C^{(x)m} = H^m diag(i^wt) H^m iff
    z_pre == z_post and theta + q_out(x+z) - q_in(x+z) == wt(x) mod 4 for all x (SPEC §2.3)."""
    if z_pre != z_post:
        return False
    qin, qout = q_values(U_in, m), q_values(U_out, m)
    return all((theta + qout[x ^ z_pre] - qin[x ^ z_pre] - x.bit_count()) % 4 == 0 for x in range(1 << m))


class ProjectionColumns:
    """P_U stored by its columns P_U e_i, so P_U x = XOR of the columns over supp(x) (linearity over F2); makes the
    O(m^2)-point tests cost O(1) per point after O(m dim U) set-up."""

    __slots__ = ("cols",)

    def __init__(self, U, m: int):
        if not U:
            self.cols = (0,) * m
        else:
            P = f2.Projector(U)
            self.cols = tuple(P(1 << i) for i in range(m))

    def __call__(self, x: int) -> int:
        out = 0
        while x:
            low = x & -x
            out ^= self.cols[low.bit_length() - 1]
            x ^= low
        return out


@lru_cache(maxsize=64)
def projection_columns(U: tuple, m: int) -> ProjectionColumns:
    """Pure bounded cache of ``ProjectionColumns`` keyed by the exact label basis and m."""
    return ProjectionColumns(U, m)


def corrected_route_quadratic(U_in, U_out, z_pre: int, z_post: int, theta: int, m: int) -> bool:
    """The same test at the O(m^2) points 0, e_i, e_i + e_j: the defect is a constant plus a Z/4-valued quadratic
    function, determined by those values (SPEC §2.3, §2.6 item 6 for large m).  P(x + z) = P(x) + P(z) and
    P(e_i + e_j) = P e_i + P e_j make every point O(1)."""
    if z_pre != z_post:
        return False
    Pin, Pout = projection_columns(tuple(U_in), m), projection_columns(tuple(U_out), m)
    pz_in, pz_out = Pin(z_pre), Pout(z_pre)
    ci = [c ^ pz_in for c in Pin.cols]
    co = [c ^ pz_out for c in Pout.cols]
    if (theta + pz_out.bit_count() - pz_in.bit_count()) % 4:          # x = 0
        return False
    for i in range(m):                                                 # x = e_i
        if (theta + co[i].bit_count() - ci[i].bit_count() - 1) % 4:
            return False
    for i in range(m):                                                 # x = e_i + e_j: P(x + z) = P e_i + P e_j + P z
        a, b = Pout.cols[i], Pin.cols[i]
        for j in range(i + 1, m):
            if (theta + (a ^ co[j]).bit_count() - (b ^ ci[j]).bit_count() - 2) % 4:
                return False
    return True


# ----------------------------------------------------------------------------------------------- edge identity (Prop 8)
def edge_identity_dense(U_tail, U_head, basis, eps, m: int) -> bool:
    """C_{U_head} C_{U_tail}^{-1} == prod_j C_{v_j}^{eps_j}, dense (Prop 8) [Pr L1221-1256, L1799-1811]."""
    lhs = matmul(dense_C(U_head, m), dense_C_inverse(U_tail, m))
    rhs = dense_identity(m)
    for v, e in zip(basis, eps):
        rhs = matmul(rhs, dense_Cv(v, m, e))
    return lhs == rhs


def edge_identity_exhaustive(U_tail, U_head, basis, eps, m: int) -> bool:
    """Prop 8 on Hadamard-basis exponents: q_head(x) - q_tail(x) == sum_j eps_j [v_j . x] (mod 4) for all x
    (C_v has eigenvalue i^{[v.x]}, its inverse i^{-[v.x]})."""
    qt, qh = q_values(U_tail, m), q_values(U_head, m)
    for x in range(1 << m):
        rhs = sum(e for v, e in zip(basis, eps) if f2.dot(v, x))
        if (qh[x] - qt[x] - rhs) % 4:
            return False
    return True


def edge_identity_quadratic(U_tail, U_head, basis, eps, m: int) -> bool:
    """Prop 8 at the points 0, e_i, e_i + e_j (both sides are Z/4-valued quadratic functions vanishing at 0).
    sum_j eps_j [v_j . x] is evaluated through per-coordinate bit masks of the basis (O(1) per point)."""
    Pt, Ph = projection_columns(tuple(U_tail), m), projection_columns(tuple(U_head), m)
    pos, neg = [0] * m, [0] * m
    for jj, (v, e) in enumerate(zip(basis, eps)):
        for i in f2.support(v):
            if e == 1:
                pos[i] |= 1 << jj
            else:
                neg[i] |= 1 << jj
    ch, ct = Ph.cols, Pt.cols
    for i in range(m):                                                 # x = e_i
        if (ch[i].bit_count() - ct[i].bit_count() - pos[i].bit_count() + neg[i].bit_count()) % 4:
            return False
    for i in range(m):                                                 # x = e_i + e_j
        a, b, p, n = ch[i], ct[i], pos[i], neg[i]
        for j in range(i + 1, m):
            if ((a ^ ch[j]).bit_count() - (b ^ ct[j]).bit_count()
                    - (p ^ pos[j]).bit_count() + (n ^ neg[j]).bit_count()) % 4:
                return False
    return True


def method_for(m: int, requested: str = "auto") -> str:
    """'dense' (m <= DENSE_MAX_M), 'exhaustive' (m <= EXHAUSTIVE_MAX_M) or 'quadratic' (SPEC §2.6 item 6)."""
    if requested != "auto":
        return requested
    if m <= DENSE_MAX_M:
        return "dense"
    if m <= EXHAUSTIVE_MAX_M:
        return "exhaustive"
    return "quadratic"
