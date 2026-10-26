"""The primes of the Lemma 9 factors of the bit triple network (the prime-alphabet certificate).

Claim (prime-alphabet certificate, parts 1-5): in SPEC's physical lexicographic tensor order, for every h >= 7,
h != 9, every frame and every Lemma 9 factor E1, E2, E1^{-1}, E2^{-1} (SPEC §3.1 pivot rule: topmost row,
rightmost pivot) of every edge matrix lies in Z[1/6], with unit diagonals; so the forbidden primes are S(h) =
{2, 3} and q_radix = 5 (3 is genuinely forbidden: the source frame -P_{U_a} has entries -1/216).

This module provides the checks used to confirm it:
* :func:`factor_primes` -- the literal SPEC §3.1 elimination of one matrix, exact reconstruction, triangularity,
  and the prime support of all frame/factor denominators and of the diagonal numerators; optionally the
  specialization of every identity modulo 5^b (certificate step 5).
* :func:`primitive_matrices` / :func:`brute_force_primitives` -- certificate steps 1-4, EXHAUSTIVE over the
  ordered one-factor primitives at a given h: L_T and I - L_T for every triple T; I - L_S - L_T and the gadget
  [[L_S, -(I - L_S - L_T)], [0, I - L_T]] for every ordered neighboring pair (|S cap T| = 1); optionally the
  tensor-line projections P = L_S (x) L_T and I - P (h^2 x h^2).
* :func:`full_edge_primes` -- certificate step 6: materialized h^3 x h^3 edge matrices of chosen roles (small h),
  factored literally; their ranks are compared with the symbolic certificate by the caller.
* :func:`certify_prime_alphabet` -- the finite arithmetic certificate (verbatim checks).
* :func:`edge_grammar` -- every edge class rewrites (up to sign) to the proved grammar (tensor
  products of tensor-line projections P, I - P, L_t, I - L_t, I - L_S - L_T, identities; the mixed edge;
  the source edge 2 P_{U_a}), checked with the cell calculus of :mod:`.symbolic` on orbit representatives.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations

from ..checks import require
from .qmatrix import identity, kron, lower_bruhat_factors, partial_permutation, specialize_matrix, sub
from .symbolic import CellSystem, edge_calculus, p_line_Q

__all__ = ["prime_factors", "smooth23", "unit23", "factor_primes", "PrimeReport", "mixed_edge", "primitive_matrices",
           "brute_force_primitives", "full_edge_primes", "certify_prime_alphabet", "edge_grammar",
           "grammar_certificate"]


def prime_factors(n: int) -> set[int]:
    """Prime factors of |n| (trial division; the integers here are small)."""
    n, out, f = abs(n), set(), 2
    while f * f <= n:
        while n % f == 0:
            out.add(f)
            n //= f
        f += 1 if f == 2 else 2
    if n > 1:
        out.add(n)
    return out


def smooth23(n: int) -> bool:
    """n != 0 has no prime factor other than 2 and 3 ."""
    n = abs(n)
    if n == 0:
        return False
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n == 1


def unit23(x) -> bool:
    """x is a unit of Z[1/6] ."""
    x = Fraction(x)
    return x != 0 and smooth23(x.numerator) and smooth23(x.denominator)


def _matmod(A, B, Q):
    n, m = len(A), len(B[0])
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(len(B))) % Q for j in range(m)) for i in range(n))


def factor_primes(A, mod_exps: tuple[int, ...] = ()) -> tuple[set[int], int]:
    """(prime support, rank) of one matrix under the literal SPEC §3.1 Lemma 9 elimination: the primes dividing a
    denominator of A, E1, E2, E1^{-1}, E2^{-1} or a numerator of a diagonal entry of E1, E2, E1^{-1}, E2^{-1}
    (SPEC §3.2's forbidden set).  ``lower_bruhat_factors(check=True)`` asserts E1 Pi E2 = A, the inverses and the
    triangularity; for each b in ``mod_exps`` every identity is also checked after specialization mod 5^b."""
    f = lower_bruhat_factors(A, check=len(A) <= 64)
    if len(A) > 64:                                   # structured check for large matrices (O(rank m^2))
        from .qmatrix import bruhat_product, is_invertible_lower, qmat
        require(bruhat_product(f.E1, f.pivots, f.E2) == qmat(A), "E1 Pi E2 != A (Lemma 9 elimination, SPEC §3.1)")
        require(all(map(is_invertible_lower, (f.E1, f.E2, f.E1inv, f.E2inv))),
                "Lemma 9 factor not invertible lower triangular (SPEC §3.1)")
    primes: set[int] = set()
    for X in (A, f.E1, f.E2, f.E1inv, f.E2inv):
        for r in X:
            for x in r:
                d = Fraction(x).denominator
                if d > 1:
                    primes |= prime_factors(d)
    for X in (f.E1, f.E2, f.E1inv, f.E2inv):
        for i in range(len(X)):
            primes |= prime_factors(Fraction(X[i][i]).numerator)
    m = len(A)
    for b in mod_exps:
        Q = 5 ** b
        E1, E2, E1i, E2i, Aq = (specialize_matrix(X, Q) for X in (f.E1, f.E2, f.E1inv, f.E2inv, A))
        Pi = tuple(tuple(int(x) for x in r) for r in partial_permutation(f.pivots, m))
        Iq = tuple(tuple(int(i == j) for j in range(m)) for i in range(m))
        require(_matmod(_matmod(E1, Pi, Q), E2, Q) == Aq, "E1 Pi E2 != A mod 5^b (SPEC §2.7 step 9)")
        require(_matmod(E1, E1i, Q) == Iq and _matmod(E2, E2i, Q) == Iq, "inverses fail mod 5^b (SPEC §2.7 step 9)")
        require(all(E1[i][i] % 5 and E2[i][i] % 5 for i in range(m)), "diagonal not a unit mod 5 (SPEC §2.7 step 9)")
    return primes, f.rank


def _L(T, h):
    return p_line_Q(T, h)


def mixed_edge(h: int, Tp, S, T):
    """The two-factor mixed edge A = I (x) D0 - P0 (x) K with P0 = L_{Tp} (prefix line), D0 = I - L_T,
    K = I - L_S - L_T, |S cap T| = 1 (X = L_S, Y = L_T), lexicographic Kronecker order (prefix factor most
    significant): the side 0 -> 2 edge class at stage 2 before its future factor."""
    I = identity(h)
    LS, LT = _L(S, h), _L(T, h)
    D0, K = sub(I, LT), sub(sub(I, LS), LT)
    return sub(kron(I, D0), kron(_L(Tp, h), K))


def primitive_matrices(h: int, tensor_lines: bool = False, mixed: int | None = 0, seed: int = 0):
    """Certificate steps 1-2 (exhaustive, ordered): yields (kind, key, matrix) for L_T, I - L_T (every triple T),
    I - L_S - L_T and the gadget (every ordered pair with |S cap T| = 1); with ``tensor_lines`` also the
    two-coordinate tensor-line projections L_S (x) L_T and their complements (every ordered pair of triples); with
    ``mixed`` = N > 0 a random sample of N two-factor mixed edges, with ``mixed`` = None all of them."""
    I = identity(h)
    trip = list(combinations(range(h), 3))
    Ls = {T: _L(T, h) for T in trip}
    for T in trip:
        yield "L_T", (T,), Ls[T]
        yield "I-L_T", (T,), sub(I, Ls[T])
    zero = tuple(Fraction(0) for _ in range(h))
    for S in trip:
        for T in trip:
            if len(set(S) & set(T)) != 1:
                continue
            K = sub(sub(I, Ls[S]), Ls[T])
            D0 = sub(I, Ls[T])
            yield "I-L_S-L_T", (S, T), K
            gadget = tuple(tuple(Ls[S][i]) + tuple(-x for x in K[i]) for i in range(h)) + \
                tuple(zero + tuple(D0[i]) for i in range(h))
            yield "gadget", (S, T), gadget
    if tensor_lines:
        I2 = identity(h * h)
        for S in trip:
            for T in trip:
                P = kron(Ls[S], Ls[T])
                yield "P2", (S, T), P
                yield "I-P2", (S, T), sub(I2, P)
    if mixed is None or mixed:
        import random
        pairs = [(S, T) for S in trip for T in trip if len(set(S) & set(T)) == 1]
        keys = [(Tp, S, T) for Tp in trip for S, T in pairs]
        if mixed is not None:
            keys = random.Random(seed).sample(keys, min(mixed, len(keys)))
        for Tp, S, T in keys:
            yield "mixed", (Tp, S, T), mixed_edge(h, Tp, S, T)


@dataclass
class PrimeReport:
    """Counts and the prime support found by a brute-force run."""

    h: int
    counts: dict = field(default_factory=dict)
    primes: set = field(default_factory=set)
    max_dim: int = 0
    seconds: float = 0.0

    def merge(self, other: "PrimeReport") -> None:
        for k, v in other.counts.items():
            self.counts[k] = self.counts.get(k, 0) + v
        self.primes |= other.primes
        self.max_dim = max(self.max_dim, other.max_dim)
        self.seconds += other.seconds


def brute_force_primitives(h: int, tensor_lines: bool = False, mod_exps: tuple[int, ...] = (1, 2, 3),
                           part: int = 0, parts: int = 1, mixed: int | None = 0, seed: int = 0,
                           primitives: bool = True) -> PrimeReport:
    """Factor every primitive of :func:`primitive_matrices` (the slice ``part`` of ``parts``, for parallel runs)
    literally and collect the prime support (certificate steps 1-5).  Raises AssertionError if any identity fails."""
    import time
    t0 = time.time()
    rep = PrimeReport(h)
    for n, (kind, key, A) in enumerate(primitive_matrices(h, tensor_lines, mixed, seed)):
        if n % parts != part or (not primitives and kind in ("L_T", "I-L_T", "I-L_S-L_T", "gadget")):
            continue
        pr, _ = factor_primes(A, mod_exps if len(A) <= 2 * h else ())
        rep.primes |= pr
        rep.counts[kind] = rep.counts.get(kind, 0) + 1
        rep.max_dim = max(rep.max_dim, len(A))
    rep.seconds = time.time() - t0
    return rep


def full_edge_primes(tn, rid: int, dt=None):
    """Certificate step 6 for one role of a small bit triple network: every edge matrix M_head - M_tail
    materialized densely (frames from the symbolic labels, ``triple_dense``), factored literally; returns
    [(edge class, symbolic rank, dense rank, primes)] (frame denominators included via A's denominators and the
    frames themselves)."""
    from .triple_dense import DenseTriple
    dt = dt or DenseTriple(tn)
    out = []
    for tail, head, ft, fh, cls in tn.sym_edges(rid):
        Ft, Fh = dt.frame(rid, tail), dt.frame(rid, head)
        D, X = dt.bit_edge_matrix(Ft, Fh)
        A = tuple(tuple(Fraction(x, D) for x in r) for r in X)
        primes, rank = factor_primes(A)
        for Dv, _ in (Ft, Fh):                         # frame denominators (common denominators of the frames)
            for p in prime_factors(Dv):
                primes.add(p)
        sym = edge_calculus(tn.h, "bit", ft, fh).bit_rank
        out.append((cls, sym, rank, primes))
    return out


def certify_prime_alphabet(h: int) -> dict:
    """The finite arithmetic certificate (verbatim checks): V^T U = I_2 for the four-row alphabet with
    multiplicities (h-5, 2, 2, 1); all nonzero 2 x 2 minors of the U- and 6V-alphabets are units of Z[1/6]; the
    rank-one/rank-one products in disjoint corners are units; tensor-line column coefficients are units and exactly
    normalized; the source denominator 216 excludes 3."""
    require(h >= 7 and h != 9, "the prime-alphabet certificate needs h >= 7, h != 9")
    U = [(0, 0), (1, 0), (0, 1), (1, 1)]
    V6 = [(-1, -1), (2, -1), (-1, 2), (2, 2)]
    mult = [h - 5, 2, 2, 1]
    for i in range(2):
        for j in range(2):
            s = sum(c * v[i] * u[j] for c, u, v in zip(mult, U, V6))
            require(s == (6 if i == j else 0), "prime-alphabet certificate: V^T U != I_2 for multiplicities (h-5, 2, 2, 1)")
    for alphabet in (U, V6):
        for a, b in combinations(alphabet, 2):
            z = a[0] * b[1] - a[1] * b[0]
            require(z == 0 or unit23(z), "prime-alphabet certificate: a nonzero 2 x 2 minor is not a unit of Z[1/6]")
    for u in U[1:]:
        for v in V6:
            require(unit23(u[0] * v[0] + u[1] * v[1]), "prime-alphabet certificate: a disjoint-corner rank-one product is not a unit")
    for k in range(1, 4):
        for a in range(k + 1):
            require(unit23(Fraction((-1) ** (k - a) * 2 ** a, 6 ** k)),
                    "prime-alphabet certificate: tensor-line coefficient not a unit")
        require(3 ** k * Fraction(2 ** k, 6 ** k) == 1,
                "prime-alphabet certificate: tensor-line column not exactly normalized")
    require(Fraction(1, 216).denominator % 3 == 0, "prime-alphabet certificate: the source denominator 216 must exclude 3")
    return {"forbidden_primes": {2, 3}, "smallest_odd_prime": 5}


# ----------------------------------------------------------------------------------------------- grammar (§5, §6)
def _templates(cs: CellSystem, j: int, fixed_line_cells):
    """Candidate grammar terms of the edge grammar as cell sets for an edge at stage j (coordinates 1..3; prefix < j,
    current j, future > j): products pre x cur x fut with pre in {P, I-P, I}, cur in {L_x, I-L_x, C, I}, fut in
    {P, I-P, I}, and the mixed edge ((I-P) x D0 + P x X) x fut for ordered line atoms (X, Y)."""
    k0 = j - 1
    pre_coords, fut_coords = list(range(k0)), list(range(k0 + 1, 3))

    def block(coords, kind):
        allc = [()]
        for k in coords:
            allc = [c + (a,) for c in allc for a in cs.atoms[k]]
        line = tuple(fixed_line_cells[k] for k in coords)
        if kind == "P":
            return {line}
        if kind == "I-P":
            return set(allc) - {line}
        return set(allc)

    cur_atoms = cs.atoms[k0]
    lines = [a for a in cur_atoms if a[0] == "L"]
    curs = {"I": set(cur_atoms)}
    for x in lines:
        curs[f"L[{x[1]}]"] = {x}
        curs[f"I-L[{x[1]}]"] = set(cur_atoms) - {x}
    comp = [a for a in cur_atoms if a[0] == "C"][0]
    curs["C"] = {comp}
    pres = ["P", "I-P", "I"] if pre_coords else [""]
    futs = ["P", "I-P", "I"] if fut_coords else [""]

    def prod3(pre_set, cur_set, fut_set):
        return {p + (c,) + f for p in pre_set for c in cur_set for f in fut_set}

    out = {}
    for pn in pres:
        ps = block(pre_coords, pn) if pn else {()}
        for cn, cset in curs.items():
            for fn in futs:
                fs = block(fut_coords, fn) if fn else {()}
                out[f"({pn or '1'})x{cn}x({fn or '1'})"] = prod3(ps, cset, fs)
    if pre_coords:
        for X in lines:
            for Y in lines:
                if X != Y:
                    for fn in futs:
                        fs = block(fut_coords, fn) if fn else {()}
                        mixed = prod3(block(pre_coords, "I-P"), set(cur_atoms) - {Y}, fs) | \
                            prod3(block(pre_coords, "P"), {X}, fs)
                        out[f"mixed(X={X[1]},Y={Y[1]})x({fn or '1'})"] = mixed
    return out


def edge_grammar(tn, rid: int) -> list:
    """For every edge of role ``rid`` of the bit triple network: the matching grammar term of the edge grammar (edge
    matrix = sign * term, or the source exception 2 P_{U_a}, or zero).  Raises AssertionError if an edge matches
    none.  The cell calculus gives the edge matrix exactly as sum_c lambda_c P_c (``symbolic``)."""
    out = []
    name = tn.role_name(rid)
    for k, (tail, head, ft, fh, cls) in enumerate(tn.sym_edges(rid)):
        j = cls[0]
        cs = CellSystem(tn.h, "bit", [ft.label, fh.label])
        Ct, Ch = cs.cells(ft.label), cs.cells(fh.label)
        lam = {c: fh.sign * (c in Ch) - ft.sign * (c in Ct) for c in Ct | Ch}
        supp = {c for c, v in lam.items() if v}
        vals = {lam[c] for c in supp}
        if not supp:
            out.append((cls, "0"))
            continue
        # the tensor line of this role's own triples in each coordinate (prefix/future lines are tensor lines)
        line_cells = []
        for kk in range(3):
            ls = [a for a in cs.atoms[kk] if a[0] == "L"]
            line_cells.append(ls[0] if len(ls) == 1 else None)
        if vals == {2}:
            require(len(supp) == 1 and all(a[0] == "L" for a in next(iter(supp))),
                    "source exception (edge grammar)")
            out.append((cls, "2*P_U"))
            continue
        require(vals in ({1}, {-1}), lambda: f"non-uniform coefficients on {cls} (edge grammar)")
        if cls[1] in ("X", "Y") and name[0] in ("X", "Y"):
            a = name[1]
            fixed = {kk: ("L", a[kk]) for kk in range(3)}
        else:
            fixed = {kk: line_cells[kk] for kk in range(3)}
        temps = _templates(cs, j, fixed)
        match = [n for n, cells in temps.items() if cells == supp]
        require(match, lambda: f"edge {cls} of {name} matches no grammar term (edge grammar)")
        out.append((cls, ("-" if vals == {-1} else "") + match[0]))
    return out


def grammar_certificate(tn) -> dict:
    """Edge grammar, network part (bit network), symbolically per stage and edge class: one symbolic instance of every
    (stage, edge class) -- the roles of ``TripleNetwork.representatives`` -- rewrites to the grammar (the cell calculus
    is generic in the triples, so the check is a check of the class; NO factorization is transferred by symmetry);
    plus the factor-level identities X^2 = X, Y^2 = Y, XY = YX = 0, K D0 = K used by the block reduction (exact h x h).
    Returns {term: number of class instances} and the alphabet certificate."""
    terms: dict = {}
    for rid, _, _ in tn.representatives():
        for _, t in edge_grammar(tn, rid):
            terms[t] = terms.get(t, 0) + 1
    h = tn.h
    T0, nbrs = tn.representative_triples()
    S = nbrs[0][0]
    X, Y = _L(T0, h), _L(S, h)
    I = identity(h)
    K, D0 = sub(sub(I, X), Y), sub(I, Y)

    def mm(A, B):
        Bt = list(zip(*B))
        return tuple(tuple(sum(a * b for a, b in zip(r, c) if a and b) for c in Bt) for r in A)
    Z = tuple(tuple(Fraction(0) for _ in range(h)) for _ in range(h))
    require(mm(X, X) == X and mm(Y, Y) == Y and mm(X, Y) == Z and mm(Y, X) == Z and mm(K, D0) == K,
            "prime-alphabet certificate: X^2 = X, Y^2 = Y, XY = YX = 0, K D0 = K fail")
    return {"terms": terms, "alphabet": certify_prime_alphabet(h)}
