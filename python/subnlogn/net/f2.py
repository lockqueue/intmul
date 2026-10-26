"""F2 linear algebra on m-bit ints and the binary phase-label machinery of the complex network.

Representation: a vector x in F2^m is a Python int whose bit i is coordinate i (coordinate (i1, i2, i3) of the triple
construction is bit (i1*h + i2)*h + i3, SPEC §2.4).  A subspace is given by a tuple of independent vectors (a basis;
"columns of V" in SPEC §2.3).  All functions are exact.

Implements SPEC §2.3 [Pr L1173-1310]: Gram matrices and nondegeneracy, P_U = V (V^T V)^{-1} V^T, q_U(x) = wt(P_U x)
mod 4, the Lemma 6 orthonormal-basis construction [Pr L1091-1104], the directional sign rule of Prop 8
[Pr L1231-1256], the basis extension M of (15)-(16) and its row-addition reduction ``reduce_ops`` [Pr L1818-1877].
"""

from __future__ import annotations

from .errors import NotAnInterface


def dot(x: int, y: int) -> int:
    """The F2 dot product x . y = parity |supp x  cap  supp y| (SPEC §2.3)."""
    return (x & y).bit_count() & 1


def wt(x: int) -> int:
    """Integer Hamming weight wt(x) [Pr L1173]."""
    return x.bit_count()


def vec(coords) -> int:
    """The vector with ones exactly at the given coordinates."""
    x = 0
    for c in coords:
        x |= 1 << c
    return x


def support(x: int) -> tuple[int, ...]:
    """supp(x) in increasing order (O(wt(x)) big-int steps)."""
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return tuple(out)


def tensor(a: int, b: int, nb: int) -> int:
    """a (x) b with index (i, j) -> i*nb + j (SPEC §2.4 coordinate convention)."""
    out = 0
    for i in support(a):
        out |= b << (i * nb)
    return out


def tensor3(a: int, b: int, c: int, h: int) -> int:
    """a (x) b (x) c in F2^(h^3): bit (i1*h + i2)*h + i3 = a_i1 b_i2 c_i3 (u_a = t_a1 (x) t_a2 (x) t_a3) [Pr L855]."""
    return tensor(tensor(a, b, h), c, h)


# ----------------------------------------------------------------------------------------------- spans
class _Echelon:
    """Fully reduced echelon basis keyed by leading bit (each leading bit occurs in exactly one basis vector)."""

    __slots__ = ("lead",)

    def __init__(self, vectors=()):
        self.lead: dict[int, int] = {}
        for v in vectors:
            self.add(v)

    def reduce(self, x: int) -> int:
        """x reduced modulo the span (0 iff x is in the span)."""
        for lb, b in self.lead.items():
            if (x >> lb) & 1:
                x ^= b
        return x

    def add(self, v: int) -> bool:
        """Insert v; returns False if v was already in the span."""
        x = self.reduce(v)
        if not x:
            return False
        lb = x.bit_length() - 1
        for k, b in self.lead.items():
            if (b >> lb) & 1:
                self.lead[k] = b ^ x
        self.lead[lb] = x
        return True

    def basis(self) -> tuple[int, ...]:
        """The canonical basis, leading bits descending."""
        return tuple(self.lead[k] for k in sorted(self.lead, reverse=True))


def echelon(vectors) -> tuple[int, ...]:
    """Canonical (fully reduced, leading bits descending) basis of span(vectors)."""
    return _Echelon(vectors).basis()


def rank(vectors) -> int:
    """dim span(vectors) over F2."""
    return len(_Echelon(vectors).lead)


def is_independent(vectors) -> bool:
    """True iff the vectors are linearly independent."""
    vectors = tuple(vectors)
    return rank(vectors) == len(vectors)


def in_span(x: int, vectors) -> bool:
    """x in span(vectors)."""
    return _Echelon(vectors).reduce(x) == 0


def is_subspace(U, V) -> bool:
    """span(U) subset of span(V) (label nesting, SPEC §2.6 item 5)."""
    e = _Echelon(V)
    return all(e.reduce(u) == 0 for u in U)


def span_equal(U, V) -> bool:
    """span(U) == span(V)."""
    return echelon(U) == echelon(V)


def perp(U, m: int) -> tuple[int, ...]:
    """A basis of U^perp = {x in F2^m : x . u = 0 for all u in U} (standard dot product)."""
    e = _Echelon(U)
    if any(lb >= m for lb in e.lead):
        raise ValueError("vector longer than m bits")
    out = []
    for f in range(m):
        if f in e.lead:
            continue
        x = 1 << f
        for lb, b in e.lead.items():
            if (b >> f) & 1:
                x |= 1 << lb
        out.append(x)
    return tuple(out)


def perp_within(U, V) -> tuple[int, ...]:
    """A basis of span(V)  cap  U^perp, assuming V is independent (the residual of U inside V, SPEC §2.3)."""
    U = tuple(U)
    piv: dict[int, tuple[int, int]] = {}
    out = []
    for v in V:
        s = 0
        for i, u in enumerate(U):
            if dot(u, v):
                s |= 1 << i
        x = v
        while s:
            lb = s.bit_length() - 1
            if lb in piv:
                ps, pv = piv[lb]
                s ^= ps
                x ^= pv
            else:
                piv[lb] = (s, x)
                break
        else:
            out.append(x)
    return tuple(out)


def intersection(U, V, m: int) -> tuple[int, ...]:
    """A basis of span(U)  cap  span(V) (= span(V)  cap  (U^perp)^perp)."""
    return perp_within(perp(U, m), echelon(V))


# ----------------------------------------------------------------------------------------------- Gram matrices
def gram(vectors) -> tuple[int, ...]:
    """Gram matrix V^T V over F2 as row ints (row i, bit j = v_i . v_j) (SPEC §2.3)."""
    vs = tuple(vectors)
    return tuple(sum(dot(a, b) << j for j, b in enumerate(vs)) for a in vs)


def identity_rows(n: int) -> tuple[int, ...]:
    """The n x n identity over F2 as row ints."""
    return tuple(1 << i for i in range(n))


def matrix_rank(rows) -> int:
    """Rank of an F2 matrix given by row ints."""
    return rank(rows)


def matrix_inverse(rows, n: int) -> tuple[int, ...] | None:
    """Inverse of an n x n F2 matrix (row ints) by Gauss-Jordan, or None if singular."""
    a = list(rows)
    inv = [1 << i for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if (a[r] >> c) & 1), None)
        if p is None:
            return None
        a[c], a[p] = a[p], a[c]
        inv[c], inv[p] = inv[p], inv[c]
        for r in range(n):
            if r != c and (a[r] >> c) & 1:
                a[r] ^= a[c]
                inv[r] ^= inv[c]
    return tuple(inv)


def is_nondegenerate(U) -> bool:
    """A label is nondegenerate iff its basis is independent and its Gram matrix is invertible (SPEC §2.3)."""
    U = tuple(U)
    return is_independent(U) and matrix_rank(gram(U)) == len(U)


class Projector:
    """P_U = V (V^T V)^{-1} V^T over F2 for a nondegenerate label U with basis V (SPEC §2.3) [Pr L1175-1179]."""

    __slots__ = ("basis", "ginv")

    def __init__(self, basis):
        self.basis = tuple(basis)
        if not is_independent(self.basis):
            raise NotAnInterface("label basis is not independent")
        ginv = matrix_inverse(gram(self.basis), len(self.basis))
        if ginv is None:
            raise NotAnInterface("label is degenerate (Gram matrix singular over F2)")
        self.ginv = ginv

    def __call__(self, x: int) -> int:
        s = 0
        for i, v in enumerate(self.basis):
            if dot(v, x):
                s |= 1 << i
        out = 0
        for i, row in enumerate(self.ginv):
            if (row & s).bit_count() & 1:
                out ^= self.basis[i]
        return out

    def q(self, x: int) -> int:
        """q_U(x) = wt(P_U x) mod 4 [Pr L1175]."""
        return self(x).bit_count() % 4


def q_form(U):
    """The function x -> q_U(x) = wt(P_U x) mod 4 for a nondegenerate label U (SPEC §2.3)."""
    return Projector(U).q


# ----------------------------------------------------------------------------------------------- Lemma 6 / Prop 8 data
def first_odd_weight_vector(vectors) -> int | None:
    """The first listed vector of odd weight, or None (over F2, v.v = parity(v) is linear, so a space is
    nonalternating iff some basis vector has odd weight; SPEC §2.3)."""
    return next((v for v in vectors if v.bit_count() & 1), None)


def orthonormal_basis(E) -> tuple[int, ...]:
    """An orthonormal basis (v_i . v_j = delta_ij) of the nondegenerate residual span(E) (Lemma 6 construction,
    SPEC §2.3 pseudo-code) [Pr L1081-1104].

    Split off odd-weight unit lines while possible; an alternating nondegenerate remainder is absorbed plane by plane
    into a retained unit w via w+a, w+b, w+a+b.  Raises NotAnInterface for an alternating residual without a unit
    vector, a degenerate residual, or dependent input.
    """
    E = tuple(E)
    if not is_independent(E):
        raise NotAnInterface("residual vectors are not independent")
    if not is_nondegenerate(E):
        raise NotAnInterface("residual is degenerate")
    units: list[int] = []
    rest = list(E)
    while (v := first_odd_weight_vector(rest)) is not None:
        units.append(v)
        rest = list(perp_within([v], rest))
    if rest and not units:
        raise NotAnInterface("alternating residual without a unit vector")
    if rest:
        w = units.pop()
        while rest:
            a = rest[0]
            b = next((r for r in rest if dot(a, r)), None)
            if b is None:
                raise NotAnInterface("degenerate alternating remainder")
            units += [w ^ a, w ^ b]
            w ^= a ^ b
            rest = list(perp_within([a, b], rest))
        units.append(w)
    if gram(units) != identity_rows(len(units)) or len(units) != len(E) or not span_equal(units, E):
        raise NotAnInterface("orthonormal basis construction failed")
    return tuple(units)


def eps_signs(basis, direction: int) -> tuple[int, ...]:
    """Directional signs eps_j = +1 if (direction * popcount(v_j)) % 4 == 1 else -1 (SPEC §2.3, Prop 8 proof)
    [Pr L1245-1254]; direction +1 for tail subset head, -1 for head subset tail."""
    if direction == 0 and basis:
        raise ValueError("an equal-label edge has an empty residual basis")
    return tuple(1 if (direction * v.bit_count()) % 4 == 1 else -1 for v in basis)


def extend_basis(basis, m: int) -> tuple[int, ...]:
    """Columns of an invertible M in GL(m, F2) whose first columns are ``basis`` (then e_0, e_1, ... as needed)
    (SPEC §2.3 coordinate form (16)) [Pr L1826-1828]."""
    if any(v >> m for v in basis):
        raise ValueError("vectors exceed m bits")
    e = _Echelon()
    cols = []
    for v in basis:
        if not e.add(v):
            raise NotAnInterface("residual basis is not independent")
        cols.append(v)
    for i in range(m):
        if len(cols) == m:
            break
        if e.add(1 << i):
            cols.append(1 << i)
    if len(cols) != m:
        raise ValueError("vectors exceed m bits")
    return tuple(cols)


def cols_to_rows(cols, m: int) -> list[int]:
    """Convert a matrix given by column ints into row ints (row r, bit c = entry (r, c))."""
    return [sum(((c >> r) & 1) << j for j, c in enumerate(cols)) for r in range(m)]


def reduce_ops(cols, m: int) -> tuple[tuple[int, int], ...]:
    """Chronological row additions (dst, src) -- row_dst ^= row_src -- with E_n ... E_1 M = I (SPEC §4.3)
    [Pr L1871-1874].

    Gauss-Jordan with additions only: a missing pivot is repaired by adding a lower row that has a one there (one
    addition instead of a three-addition swap; still within the preprint's bound m(m-1) + 3m).
    """
    rows = cols_to_rows(cols, m)
    ops: list[tuple[int, int]] = []
    for c in range(m):
        if not (rows[c] >> c) & 1:
            r = next((r for r in range(c + 1, m) if (rows[r] >> c) & 1), None)
            if r is None:
                raise NotAnInterface("basis extension M is singular")
            rows[c] ^= rows[r]
            ops.append((c, r))
        for r in range(m):
            if r != c and (rows[r] >> c) & 1:
                rows[r] ^= rows[c]
                ops.append((r, c))
    return tuple(ops)


def replay_reduce_ops(cols, ops, m: int) -> tuple[int, ...]:
    """Apply ``ops`` to the rows of M (validation: the result must be the identity, SPEC §2.6 item 5)."""
    rows = cols_to_rows(cols, m)
    for dst, src in ops:
        if dst == src or not (0 <= dst < m and 0 <= src < m):
            raise NotAnInterface(f"illegal row addition {(dst, src)}")
        rows[dst] ^= rows[src]
    return tuple(rows)


def apply_row_ops_to_address(x: int, ops) -> int:
    """Apply row additions x_dst ^= x_src in order to an address vector (moves the value at x to E x; replaying
    ``reduce_ops`` implements P_{M^{-1}}, the reversed list implements P_M; SPEC §4.3)."""
    for dst, src in ops:
        if (x >> src) & 1:
            x ^= 1 << dst
    return x


def mat_vec_cols(cols, x: int) -> int:
    """M x for M given by its columns."""
    out = 0
    for j, c in enumerate(cols):
        if (x >> j) & 1:
            out ^= c
    return out


def quadratic_points(m: int):
    """The points 0, e_i, e_i + e_j (i < j) determining a Z/4-valued quadratic function on F2^m (SPEC §2.3)."""
    yield 0
    for i in range(m):
        yield 1 << i
    for i in range(m):
        for j in range(i + 1, m):
            yield (1 << i) | (1 << j)
