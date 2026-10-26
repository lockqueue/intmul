"""Exact rational matrices (tuples of Fractions), Lemma 9, and the fixed odd prime ``q_radix``.

* Bit frames are rational m x m matrices M_v (SPEC §2.2) [Pr L1127-1167, L1436-1464].
* ``lower_bruhat``: Lemma 9, A = E1 * Pi * E2 with E1, E2 invertible lower triangular, topmost nonzero row and its
  rightmost nonzero entry as pivot (SPEC §3.1) [Pr L1377-1395].
* ``choose_prime``: the least odd prime avoiding every denominator of the frames and factors and every numerator of a
  diagonal entry of a triangular factor (SPEC §3.2) [Pr L1407-1413, L1465-1467].

A ``QMatrix`` is a tuple of rows, each a tuple of ``Fraction``.  Everything is exact; no floats.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import lcm

from ..checks import require

QMatrix = tuple[tuple[Fraction, ...], ...]
_F0, _F1 = Fraction(0), Fraction(1)


# ----------------------------------------------------------------------------------------------- construction / algebra
def _q(x) -> Fraction:
    return x if type(x) is Fraction else Fraction(x)


def qmat(rows) -> QMatrix:
    """Coerce a nested sequence of ints/Fractions to a QMatrix (SPEC §2.2: "all entries rational")."""
    return tuple(tuple(_q(x) for x in row) for row in rows)


def identity(m: int) -> QMatrix:
    """I_m (SPEC §2.2, interface (11))."""
    return tuple(tuple(_F1 if i == j else _F0 for j in range(m)) for i in range(m))


def zeros(r: int, c: int | None = None) -> QMatrix:
    """The zero matrix (the frame of a zero label, SPEC §2.4)."""
    c = r if c is None else c
    return tuple(tuple(_F0 for _ in range(c)) for _ in range(r))


def add(A, B) -> QMatrix:
    """A + B."""
    return tuple(tuple(x + y for x, y in zip(ra, rb)) for ra, rb in zip(A, B))


def sub(A, B) -> QMatrix:
    """A - B (edge matrix A_e = M_head - M_tail, SPEC §2.2)."""
    return tuple(tuple(x - y for x, y in zip(ra, rb)) for ra, rb in zip(A, B))


def neg(A) -> QMatrix:
    """-A (Phi_M^{-1} = Phi_{-M}, SPEC §2.2)."""
    return tuple(tuple(-x for x in r) for r in A)


def scale(c, A) -> QMatrix:
    """c * A for a rational scalar c."""
    c = Fraction(c)
    return tuple(tuple(c * x for x in r) for r in A)


def transpose(A) -> QMatrix:
    """A^T."""
    return tuple(zip(*A)) if A else ()


def mul(A, B) -> QMatrix:
    """Exact product A @ B (zero entries of A skipped)."""
    Bt = B
    ncols = len(B[0]) if B else 0
    out = []
    for row in A:
        acc = [_F0] * ncols
        for k, a in enumerate(row):
            if a:
                bk = Bt[k]
                for j in range(ncols):
                    if bk[j]:
                        acc[j] += a * bk[j]
        out.append(tuple(acc))
    return tuple(out)


def mat_vec(A, x) -> tuple[Fraction, ...]:
    """A @ x for a column vector x."""
    return tuple(sum((a * b for a, b in zip(row, x) if a and b), _F0) for row in A)


def kron(A, B) -> QMatrix:
    """Kronecker product A (x) B with index (i1, i2) -> i1*rows(B) + i2 (SPEC §2.4 coordinate convention)."""
    return tuple(tuple(a * b for a in ra for b in rb) for ra in A for rb in B)


def is_zero(A) -> bool:
    """True iff every entry is 0."""
    return all(x == 0 for r in A for x in r)


# ----------------------------------------------------------------------------------------------- rank, inverse, kernel
def _integer_rows(A) -> list[list[int]]:
    """Scale each row by the lcm of its denominators (rank-preserving)."""
    out = []
    for row in A:
        d = 1
        for x in row:
            dx = x.denominator
            if dx != 1 and d % dx:
                d = lcm(d, dx)
        out.append([x.numerator * (d // x.denominator) for x in row])
    return out


def rank_Q(A) -> int:
    """Exact rational rank by fraction-free (Bareiss) elimination; every division is asserted exact.

    SPEC §2.2 (a_e = rank_Q(A_e)), §2.6 item 3 ("recompute each A_e and its exact rank").
    """
    M = _integer_rows(A)
    nr = len(M)
    nc = len(M[0]) if M else 0
    r, prev = 0, 1
    for c in range(nc):
        p = next((i for i in range(r, nr) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pr = M[r]
        piv = pr[c]
        for i in range(r + 1, nr):
            a = M[i][c]
            row = M[i]
            new = []
            for x, y in zip(row, pr):
                q, rem = divmod(piv * x - a * y, prev)
                if rem:
                    raise AssertionError("Bareiss division not exact")
                new.append(q)
            M[i] = new
        prev = piv
        r += 1
        if r == nr:
            break
    return r


def _rref(A) -> tuple[list[list[Fraction]], list[int]]:
    """Reduced row echelon form over Q and its pivot columns."""
    M = [[Fraction(x) for x in row] for row in A]
    nr = len(M)
    nc = len(M[0]) if M else 0
    pivots: list[int] = []
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c]:
                a = M[i][c]
                M[i] = [x - a * y for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == nr:
            break
    return M, pivots


def inverse(A) -> QMatrix:
    """Exact inverse by Gauss-Jordan; raises ValueError if A is singular."""
    m = len(A)
    aug = [list(map(Fraction, row)) + [_F1 if i == j else _F0 for j in range(m)] for i, row in enumerate(A)]
    R, piv = _rref(aug)
    if piv[:m] != list(range(m)):
        raise ValueError("matrix is singular")
    return tuple(tuple(row[m:]) for row in R)


def nullspace(A) -> list[tuple[Fraction, ...]]:
    """A basis of {x : A x = 0} over Q (columns of A index the coordinates of x)."""
    nc = len(A[0]) if A else 0
    R, piv = _rref(A)
    free = [c for c in range(nc) if c not in piv]
    basis = []
    for f in free:
        x = [_F0] * nc
        x[f] = _F1
        for r, c in enumerate(piv):
            x[c] = -R[r][f]
        basis.append(tuple(x))
    return basis


# ----------------------------------------------------------------------------------------------- Lemma 9
def is_lower(A) -> bool:
    """True iff every entry above the diagonal is zero (lower triangular, SPEC §3.1)."""
    return all(A[i][j] == 0 for i in range(len(A)) for j in range(i + 1, len(A[i])))


def is_invertible_lower(A) -> bool:
    """Lower triangular with nonzero diagonal (SPEC §2.6 item 3; Lemma 9's E1, E2) [Pr L1380]."""
    return is_lower(A) and all(A[i][i] != 0 for i in range(len(A)))


def partial_permutation(pivots, m: int) -> QMatrix:
    """Pi with a one at each (i, j) in ``pivots`` (Lemma 9) [Pr L1380-1381]."""
    P = [[_F0] * m for _ in range(m)]
    for i, j in pivots:
        P[i][j] = _F1
    return tuple(tuple(r) for r in P)


def bruhat_product(E1, pivots, E2) -> QMatrix:
    """E1 @ Pi @ E2 = sum over pivots (i, j) of column i of E1 times row j of E2 (exact, O(rank m^2))."""
    m = len(E1)
    out = [[_F0] * m for _ in range(m)]
    for i, j in pivots:
        rowj = E2[j]
        for r in range(m):
            a = E1[r][i]
            if a:
                o = out[r]
                for c in range(m):
                    if rowj[c]:
                        o[c] += a * rowj[c]
    return tuple(tuple(r) for r in out)


@dataclass(frozen=True)
class Bruhat:
    """A Lemma 9 factorization A = E1 Pi E2 with the inverses E1inv = L, E2inv = R (L A R = Pi) [Pr L1394-1395].

    ``pivots`` lists the positions (i, j) of the ones of Pi in elimination order (SPEC §2.1 BitEdge.pivots).
    """

    E1: QMatrix
    E2: QMatrix
    E1inv: QMatrix
    E2inv: QMatrix
    pivots: tuple[tuple[int, int], ...]

    @property
    def rank(self) -> int:
        """Number of ones of Pi = rank_Q(A) (Lemma 9)."""
        return len(self.pivots)


def lower_bruhat_factors(A, check: bool = True) -> Bruhat:
    """Lemma 9 elimination exactly as SPEC §3.1 [Pr L1385-1395]; also returns E1^{-1} = L and E2^{-1} = R.

    Repeatedly: the TOPMOST active row with a nonzero active entry, its RIGHTMOST nonzero active entry as pivot; clear
    entries left of the pivot by column operations (col_k += c col_j, k < j: right multiplication by a lower
    triangular elementary matrix), clear entries below it by row operations (row_k += c row_i, k > i), scale the
    pivot to one, and deactivate its row and column.  Then L A R = Pi, E1 = L^{-1}, E2 = R^{-1}.

    The inverses E1, E2 are maintained incrementally (E1 <- E1 E^{-1} for each row operation E, E2 <- F^{-1} E2 for
    each column operation F); this is the same matrix as SPEC's final ``inverse(L)``, ``inverse(R)`` and costs
    O(rank * m^2) instead of O(m^3).  With ``check`` the identities E1 Pi E2 = A, E1 L = I, R E2 = I, triangularity
    and len(pivots) = rank_Q(A) are asserted (SPEC §3.1 last line).
    """
    m = len(A)
    if any(len(r) != m for r in A):
        raise ValueError("lower_bruhat needs a square matrix")
    B = [[_q(x) for x in row] for row in A]
    L = [[_F1 if i == j else _F0 for j in range(m)] for i in range(m)]
    R = [[_F1 if i == j else _F0 for j in range(m)] for i in range(m)]
    E1 = [[_F1 if i == j else _F0 for j in range(m)] for i in range(m)]
    E2 = [[_F1 if i == j else _F0 for j in range(m)] for i in range(m)]
    rows, cols = list(range(m)), list(range(m))
    pivots: list[tuple[int, int]] = []
    while True:
        i = next((r for r in rows if any(B[r][c] for c in cols)), None)
        if i is None:
            break
        j = max(c for c in cols if B[i][c])
        piv = B[i][j]
        for k in cols:  # clear left of the pivot: col_k -= a col_j (k < j), on B and R; E2: row_j += a row_k
            if k < j and B[i][k]:
                a = B[i][k] / piv
                for r in range(m):
                    if B[r][j]:
                        B[r][k] -= a * B[r][j]
                    if R[r][j]:
                        R[r][k] -= a * R[r][j]
                E2[j] = [x + a * y for x, y in zip(E2[j], E2[k])]
        for k in rows:  # clear below the pivot: row_k -= a row_i (k > i), on B and L; E1: col_i += a col_k
            if k > i and B[k][j]:
                a = B[k][j] / piv
                B[k] = [x - a * y for x, y in zip(B[k], B[i])]
                L[k] = [x - a * y for x, y in zip(L[k], L[i])]
                for r in range(m):
                    if E1[r][k]:
                        E1[r][i] += a * E1[r][k]
        inv = 1 / piv  # scale the pivot row to one; E1: col_i *= piv
        B[i] = [x * inv for x in B[i]]
        L[i] = [x * inv for x in L[i]]
        for r in range(m):
            if E1[r][i]:
                E1[r][i] *= piv
        rows.remove(i)
        cols.remove(j)
        pivots.append((i, j))
    res = Bruhat(E1=tuple(map(tuple, E1)), E2=tuple(map(tuple, E2)), E1inv=tuple(map(tuple, L)),
                 E2inv=tuple(map(tuple, R)), pivots=tuple(pivots))
    if check:
        Pi = partial_permutation(pivots, m)
        require(tuple(map(tuple, B)) == Pi, "L A R != Pi (Lemma 9, SPEC §3.1)")
        require(bruhat_product(res.E1, res.pivots, res.E2) == qmat(A), "E1 Pi E2 != A (Lemma 9, SPEC §3.1)")
        require(all(map(is_invertible_lower, (res.E1, res.E2, res.E1inv, res.E2inv))),
                "factor not lower triangular (Lemma 9, SPEC §3.1)")
        require(mul(res.E1, res.E1inv) == identity(m) and mul(res.E2inv, res.E2) == identity(m),
                "bad inverse (Lemma 9, SPEC §3.1)")
        require(len(pivots) == rank_Q(A), "pivot count != rank (Lemma 9, SPEC §3.1)")
    return res


def lower_bruhat(A) -> tuple[QMatrix, tuple[tuple[int, int], ...], QMatrix]:
    """Lemma 9: ``(E1, pivots, E2)`` with A = E1 Pi E2 (SPEC §3.1 signature) [Pr L1377-1395]."""
    f = lower_bruhat_factors(A)
    return f.E1, f.pivots, f.E2


# ----------------------------------------------------------------------------------------------- the prime q_radix
def denominators(A) -> set[int]:
    """All denominators > 1 of the entries of A (SPEC §3.2 forbidden set)."""
    return {Fraction(x).denominator for r in A for x in r if Fraction(x).denominator > 1}


def diagonal_numerators(A) -> set[int]:
    """|numerators| > 1 of the diagonal entries of A (SPEC §3.2: diagonal units must stay units mod q)."""
    return {abs(Fraction(A[i][i]).numerator) for i in range(len(A)) if abs(Fraction(A[i][i]).numerator) > 1}


def is_prime(n: int) -> bool:
    """Deterministic primality by trial division (the primes used here are tiny)."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            return False
        f += 2
    return True


def is_odd_prime(n: int) -> bool:
    """SPEC §2.6 item 4: q_radix must be an odd prime."""
    return n != 2 and is_prime(n)


def least_odd_prime_avoiding(forbidden) -> int:
    """The smallest odd prime dividing none of the given nonzero integers (trial division) [Pr L1408-1412]."""
    vals = {abs(int(x)) for x in forbidden}
    if 0 in vals:
        raise ValueError("0 cannot be avoided by any prime")
    vals.discard(1)
    q = 3
    while True:
        if is_prime(q) and all(v % q for v in vals):
            return q
        q += 2


def forbidden_integers(frames, factors) -> frozenset[int]:
    """SPEC §3.2: denominators of every frame and of every E1, E2, E1inv, E2inv, plus the numerators of their
    diagonal entries [Pr L1407-1413, L1465-1467]."""
    out: set[int] = set()
    for M in frames:
        out |= denominators(M)
    for f in factors:
        for X in (f.E1, f.E2, f.E1inv, f.E2inv):
            out |= denominators(X) | diagonal_numerators(X)
    return frozenset(out)


def choose_prime(network) -> int:
    """q_radix for a bit network: the least odd prime avoiding ``forbidden_integers`` (SPEC §3.2).

    ``network`` is a ``model.Network`` (compiled here) or a ``model.CompiledNetwork``.  Compiled once per network,
    never per call [Pr L1411-1412].  For a lazy ``triple.TripleNetwork`` (bit) the certified value 5 is returned
    (SPEC v1.2 §2.7 step 9; never computed by trial division over its edges).
    """
    from .model import CompiledNetwork, compile_network  # local import: model depends on this module

    from .triple import TripleNetwork
    if isinstance(network, TripleNetwork):       # from the certificate, not trial division
        if network.kind != "bit":
            raise ValueError("q_radix is defined for bit (F2) networks only")
        return network.q_radix
    c = network if isinstance(network, CompiledNetwork) else compile_network(network, prime=False)
    if c.domain != "F2":
        raise ValueError("q_radix is defined for bit (F2) networks only")
    frames = list(c.net.source) + list(c.net.sink) + [g.frame for g in c.net.gates]
    factors = [e for es in c.edges for e in es]
    return least_odd_prime_avoiding(forbidden_integers(frames, factors))


def specialize(x, Q: int) -> int:
    """The image of the rational a/b in Z/QZ: a * b^{-1} mod Q (SPEC §3.2; requires gcd(b, Q) = 1)."""
    x = Fraction(x)
    return x.numerator * pow(x.denominator, -1, Q) % Q


def specialize_matrix(A, Q: int) -> tuple[tuple[int, ...], ...]:
    """Entrywise ``specialize`` (the matrix acting on Z/q^b Z, SPEC §2.2)."""
    return tuple(tuple(specialize(x, Q) for x in r) for r in A)
