"""Symbolic labels of the triple networks and the exact cell calculus (SPEC §2.4 "Symbolic labels"; §2.7 steps 3-6).

A label is an orthogonal sum of pure tensors (U1, U2, U3) of factor tokens from {ZERO, FULL, LINE(T), PERP(T) =
t_T^perp, PERP2(S, T) = <t_S, t_T>^perp} [Pr L840-909].  Factor space F = Q^h with <x, y> = x^T (I - J/9) y (bit) or
F2^h with the dot product (complex); the ambient space is F^(x)3 (dim m = h^3) with coordinate (i1, i2, i3) <-> index
(i1*h + i2)*h + i3.

Cell calculus (Completion, refining SPEC's pure-tensor sums).  For a finite set of labels, collect per coordinate the
set R of triples their tokens mention.  If the lines <t>, t in R, are nondegenerate and pairwise orthogonal (checked
with the exact inner products <t_S, t_T> = |S cap T| - 1 resp. |S cap T| mod 2 [Pr L843-848]), the factor space splits
orthogonally into the ATOMS <t> (t in R) and <R>^perp, and every token is an orthogonal sum of atoms.  The tensor
products of atoms ("cells") form an orthogonal decomposition of F^(x)3 into nondegenerate pieces, so every label is a
union of cells; nesting = inclusion of cell sets, the orthogonal residual = set difference, dim = sum over cells of the
product of atom dimensions (1 for a line, h - |R| for <R>^perp).  The cell projections P_c = (x)_k P_atom are
mutually annihilating idempotents with sum I (verified on exact h x h factor matrices in ``certify``), so for a bit
edge with frames s_t P_{U_t} -> s_h P_{U_h} (s = -1 only at the X sources [Pr L1128]) the edge matrix is
sum_c lambda_c P_c and rank_Q = sum of dim c over cells with lambda_c != 0.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from . import f2
from .errors import NotAnInterface
from .qmatrix import QMatrix, identity, inverse, mul, nullspace, qmat, sub, transpose

Triple = tuple[int, int, int]
ZERO = ("ZERO",)
FULL = ("FULL",)


def LINE(T) -> tuple:
    """The token <t_T> (a triple line)."""
    return ("LINE", tuple(T))


def PERP(T) -> tuple:
    """The token t_T^perp (complement of a triple line in F)."""
    return ("PERP", tuple(T))


def PERP2(S, T) -> tuple:
    """The token <t_S, t_T>^perp (complement of two neighboring triple lines)."""
    S, T = sorted((tuple(S), tuple(T)))
    return ("PERP2", S, T)


def token_dim(tok, h: int) -> int:
    """dim of a factor token: ZERO 0, FULL h, LINE 1, PERP h-1, PERP2 h-2 (SPEC §2.4)."""
    return {"ZERO": 0, "FULL": h, "LINE": 1, "PERP": h - 1, "PERP2": h - 2}[tok[0]]


def token_refs(tok) -> tuple[Triple, ...]:
    """The triples a token mentions."""
    return tuple(tok[1:])


def render_token(tok, names: dict | None = None) -> str:
    """Human-readable token, triples renamed through ``names`` (e.g. {(0,1,2): 'tX'})."""
    nm = (lambda T: names.get(T, str(T))) if names else str
    if tok[0] in ("ZERO", "FULL"):
        return {"ZERO": "0", "FULL": "F"}[tok[0]]
    if tok[0] == "LINE":
        return f"<{nm(tok[1])}>"
    if tok[0] == "PERP":
        return f"{nm(tok[1])}^perp"
    return f"<{nm(tok[1])},{nm(tok[2])}>^perp"


@dataclass(frozen=True)
class SymLabel:
    """An orthogonal sum of pure tensors (3-tuples of tokens); the empty sum is the zero label (SPEC §2.4)."""

    summands: tuple[tuple, ...]

    @staticmethod
    def of(summands) -> "SymLabel":
        """Drop summands containing ZERO."""
        return SymLabel(tuple(tuple(s) for s in summands if ZERO not in s))

    def dim(self, h: int) -> int:
        """Sum over summands of the product of token dimensions."""
        out = 0
        for s in self.summands:
            p = 1
            for tok in s:
                p *= token_dim(tok, h)
            out += p
        return out

    def render(self, names: dict | None = None) -> str:
        """Human-readable orthogonal sum of pure tensors."""
        if not self.summands:
            return "0"
        return " (+) ".join("(" + ",".join(render_token(t, names) for t in s) + ")" for s in self.summands)


ZERO_LABEL = SymLabel(())
FULL_LABEL = SymLabel(((FULL, FULL, FULL),))


@dataclass(frozen=True)
class SymFrame:
    """A frame of the triple network in symbolic form: sign * P_label (bit; sign -1 only at X sources, Prop 7
    [Pr L1127-1129]) or the label itself (complex, sign +1)."""

    sign: int
    label: SymLabel


# ----------------------------------------------------------------------------------------------- inner products
def triple_inner(S, T, kind: str):
    """<t_S, t_T>: |S cap T| - 1 for the rational form x^T (I - J/9) y (bit), |S cap T| mod 2 (complex)
    [Pr L843-848]; for S = T this is the norm 2 resp. 1."""
    k = len(set(S) & set(T))
    return Fraction(k - 1) if kind == "bit" else k % 2


def neighbors(S, T, kind: str) -> bool:
    """Neighbor rule: |S cap T| = 1 (bit); S != T and |S cap T| in {0, 2} (complex) [Pr L642-649]."""
    k = len(set(S) & set(T))
    return k == 1 if kind == "bit" else (S != T and k in (0, 2))


# ----------------------------------------------------------------------------------------------- cells
class CellSystem:
    """Atoms per coordinate for a finite set of labels, and the map label -> set of cells (module docstring)."""

    def __init__(self, h: int, kind: str, labels):
        self.h, self.kind = h, kind
        refs: list[set] = [set(), set(), set()]
        for lab in labels:
            for s in lab.summands:
                for k, tok in enumerate(s):
                    refs[k].update(token_refs(tok))
        self.refs = tuple(tuple(sorted(r)) for r in refs)
        for k, R in enumerate(self.refs):
            for i, S in enumerate(R):
                if triple_inner(S, S, kind) == 0:
                    raise NotAnInterface(f"coordinate {k}: line <{S}> is degenerate")
                for T in R[i + 1:]:
                    if triple_inner(S, T, kind) != 0:
                        raise NotAnInterface(f"coordinate {k}: lines <{S}>, <{T}> are not orthogonal; "
                                             "the cell calculus does not apply")
            if len(R) >= h:
                raise NotAnInterface("too many reference lines")
        self.atoms = tuple(tuple(("L", T) for T in R) + (("C", R),) for R in self.refs)

    def atom_dim(self, atom) -> int:
        """1 for a line <t>, h - |R| for <R>^perp."""
        return 1 if atom[0] == "L" else self.h - len(atom[1])

    def token_atoms(self, k: int, tok) -> frozenset:
        """The atoms whose orthogonal sum is the token (coordinate k)."""
        R = self.refs[k]
        allat = frozenset(self.atoms[k])
        if tok[0] == "ZERO":
            return frozenset()
        if tok[0] == "FULL":
            return allat
        if tok[0] == "LINE":
            return frozenset({("L", tok[1])})
        if tok[0] == "PERP":
            return allat - {("L", tok[1])}
        if tok[0] == "PERP2":
            if tok[1] not in R or tok[2] not in R:
                raise NotAnInterface("PERP2 token outside the reference set")
            return allat - {("L", tok[1]), ("L", tok[2])}
        raise ValueError(tok)

    def cells(self, label: SymLabel) -> frozenset:
        """The cell set of a label; raises if two summands overlap (the sum would not be orthogonal)."""
        out: set = set()
        for s in label.summands:
            a0, a1, a2 = (self.token_atoms(k, tok) for k, tok in enumerate(s))
            cs = {(x, y, z) for x in a0 for y in a1 for z in a2}
            if cs & out:
                raise NotAnInterface(f"label summands are not orthogonal: {label.render()}")
            out |= cs
        return frozenset(out)

    def dim(self, cells) -> int:
        """dim of a union of cells."""
        out = 0
        for c in cells:
            p = 1
            for a in c:
                p *= self.atom_dim(a)
            out += p
        return out

    @staticmethod
    def atom_token(atom) -> tuple:
        """An atom as a factor token: <t> -> LINE(t), <>^perp -> FULL, <t>^perp -> PERP(t), <s,t>^perp -> PERP2."""
        if atom[0] == "L":
            return LINE(atom[1])
        R = atom[1]
        if len(R) == 0:
            return FULL
        if len(R) == 1:
            return PERP(R[0])
        if len(R) == 2:
            return PERP2(R[0], R[1])
        return ("PERPN",) + tuple(R)

    def cells_label(self, cells) -> SymLabel:
        """A union of cells as an orthogonal sum of pure tensors of tokens (cells in a canonical order)."""
        return SymLabel(tuple(tuple(self.atom_token(a) for a in c) for c in sorted(cells)))


@dataclass(frozen=True)
class SymEdgeResult:
    """Outcome of the cell calculus on one edge: direction (+1 increasing, -1 decreasing, 0 equal), the residual as
    an orthogonal sum of pure tensors, its dimension, and (bit) the exact rank of the edge matrix."""

    direction: int
    residual: SymLabel
    dim: int
    bit_rank: int | None


def edge_calculus(h: int, kind: str, tail: SymFrame, head: SymFrame) -> SymEdgeResult:
    """Nesting, orthogonal residual and rank of one edge by the cell calculus (SPEC §2.7 step 4; Lemma 6, Prop 7)."""
    cs = CellSystem(h, kind, [tail.label, head.label])
    Ct, Ch = cs.cells(tail.label), cs.cells(head.label)
    if Ct <= Ch:
        d, res = (0 if Ct == Ch else 1), Ch - Ct
    elif Ch <= Ct:
        d, res = -1, Ct - Ch
    else:
        raise NotAnInterface(f"labels not nested: {tail.label.render()} vs {head.label.render()}")
    rank = None
    if kind == "bit":
        rank = 0
        for c in Ct | Ch:
            lam = head.sign * (c in Ch) - tail.sign * (c in Ct)
            if lam:
                rank += cs.dim([c])
    return SymEdgeResult(direction=d, residual=cs.cells_label(res), dim=cs.dim(res), bit_rank=rank)


# ----------------------------------------------------------------------------------------------- exact factor matrices
def indicator_Q(T, h: int) -> tuple[Fraction, ...]:
    """t_T in Q^h."""
    return tuple(Fraction(1 if i in T else 0) for i in range(h))


def gram0(h: int) -> QMatrix:
    """G0 = I - J/9 (the rational form of the bit labels) [Pr L840-842]."""
    return tuple(tuple(Fraction(1 if i == j else 0) - Fraction(1, 9) for j in range(h)) for i in range(h))


def p_line_Q(T, h: int) -> QMatrix:
    """Closed form P_LINE(T) = t t^T G0 / 2 (SPEC §2.4)."""
    t = indicator_Q(T, h)
    Gt = [sum((Fraction(1 if i == j else 0) - Fraction(1, 9)) * t[j] for j in range(h)) for i in range(h)]
    return tuple(tuple(t[i] * Gt[j] / 2 for j in range(h)) for i in range(h))


def p_atom_Q(atom, h: int) -> QMatrix:
    """Rational projection of an atom: P_<t> = t t^T G0/2, P_<R>^perp = I - sum_{t in R} P_<t>."""
    if atom[0] == "L":
        return p_line_Q(atom[1], h)
    P = identity(h)
    for T in atom[1]:
        P = sub(P, p_line_Q(T, h))
    return P


def token_basis_Q(tok, h: int) -> list[tuple[Fraction, ...]]:
    """A basis of the token's subspace computed independently of the closed forms (G0-orthogonal complements by
    exact nullspaces)."""
    G = gram0(h)
    if tok[0] == "ZERO":
        return []
    if tok[0] == "FULL":
        return [tuple(Fraction(int(i == j)) for j in range(h)) for i in range(h)]
    if tok[0] == "LINE":
        return [indicator_Q(tok[1], h)]
    rows = [tuple(sum(indicator_Q(T, h)[i] * G[i][j] for i in range(h)) for j in range(h)) for T in tok[1:]]
    return nullspace(rows)


def generic_projection_Q(basis, h: int) -> QMatrix:
    """P_U = V (V^T G0 V)^{-1} V^T G0 for a basis V of U (SPEC §2.4 rational projection, factor level)."""
    if not basis:
        return tuple(tuple(Fraction(0) for _ in range(h)) for _ in range(h))
    G = gram0(h)
    V = transpose(qmat(basis))           # h x k
    Vt = qmat(basis)                     # k x h
    return mul(mul(V, inverse(mul(mul(Vt, G), V))), mul(Vt, G))


def indicator_F2(T) -> int:
    """t_T in F2^h as an int."""
    return f2.vec(T)


def p_atom_F2(atom, h: int) -> tuple[int, ...]:
    """Binary projection of an atom as row ints: P_<t> = t t^T, P_<R>^perp = I + sum t t^T (mod 2) (SPEC §2.4)."""
    rows = [0] * h if atom[0] == "L" else [1 << i for i in range(h)]
    for T in ((atom[1],) if atom[0] == "L" else atom[1]):
        t = indicator_F2(T)
        for i in T:
            rows[i] ^= t
    return tuple(rows)


def token_basis_F2(tok, h: int) -> tuple[int, ...]:
    """A basis of the token's binary subspace (independent of the closed forms)."""
    if tok[0] == "ZERO":
        return ()
    if tok[0] == "FULL":
        return tuple(1 << i for i in range(h))
    if tok[0] == "LINE":
        return (indicator_F2(tok[1]),)
    return f2.perp([indicator_F2(T) for T in tok[1:]], h)
