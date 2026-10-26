"""Exact certificates for the triple networks (``net.certify``; SPEC §2.7, all 10 steps).

The real networks (h = 100: m = 10^6, W ~ 10^20) cannot be executed; they are certified exactly and symbolically from
the lazy descriptor ``TripleNetwork`` -- no dense m x m matrix is built for h >= 21.  Symmetry: (S_h)^3, acting on the
three ground sets, maps roles, gates and labels of the construction to themselves and preserves both bilinear forms,
hence every edge rank; so one representative role per orbit (``TripleNetwork.representatives``) with the orbit size
as multiplicity certifies the class-by-class rank sums (steps 4-5).  The factor-level facts used by the cell calculus
of ``symbolic`` are verified on exact h x h matrices (step 3).  Savings are reported WITH their sign (the real network is h = 100;
other h are informational): "saving network" means s < W m.  q_radix of the
bit network is 5 (step 9 re-checks the finite prime-alphabet
certificate and that every edge class rewrites to the proved grammar, :mod:`.primes`).
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations

from . import f2
from .errors import NotAnInterface
from .qmatrix import rank_Q
from .symbolic import CellSystem, edge_calculus, generic_projection_Q, p_atom_F2, p_atom_Q, token_basis_Q, LINE, \
    PERP, PERP2, triple_inner
from .triple import FORWARD, INVERSE, TripleNetwork, TripleParams, triple_params
from .taubound import _dec, ln_enclosure, log_bound, tau_test  # noqa: F401  (re-exported)
from .zi2 import ZI2

#: Lemma 6 table (SPEC §2.4) [Pr L1001-1058]: residual dimension per (wire, edge) with a = h^(j-1), f = h^(3-j).
LEMMA6 = {("X", "in->2"): lambda a, h, f: (a - 1) * (h - 1), ("X", "2->3"): lambda a, h, f: h - 1,
          ("X", "3->6"): lambda a, h, f: 0, ("X", "6->7"): lambda a, h, f: 0, ("X", "last->sink"): lambda a, h, f: 0,
          ("Y", "in->0"): lambda a, h, f: 0, ("Y", "0->1"): lambda a, h, f: (a - 1) * (h - 1),
          ("Y", "1->4"): lambda a, h, f: 0, ("Y", "4->5"): lambda a, h, f: h - 1,
          ("Y", "last->sink"): lambda a, h, f: 0,
          ("center", "source->1"): lambda a, h, f: (a - 1) * h, ("center", "1->3"): lambda a, h, f: h,
          ("center", "3->4"): lambda a, h, f: h, ("center", "4->6"): lambda a, h, f: h,
          ("side", "source->0"): lambda a, h, f: a - 1, ("side", "0->2"): lambda a, h, f: (a - 1) * (h - 1) + 1,
          ("side", "2->5"): lambda a, h, f: h - 2, ("side", "5->7"): lambda a, h, f: 1,
          ("scratch", "last->sink"): lambda a, h, f: a * h * (f - 1)}


def _fail(msg):
    raise NotAnInterface(msg)


@dataclass(frozen=True)
class EdgeClassRow:
    """One edge of an orbit representative: stage, wire, edge name, orbit size, rendered tail/head labels, the
    residual as an orthogonal sum of pure tensors, its dimension vs the Lemma 6 table, direction, (bit) rank."""

    stage: int
    wire: str
    edge: str
    role: str
    multiplicity: int
    tail: str
    head: str
    residual: str
    dim: int
    expected_dim: int
    direction: int
    rank: int


@dataclass(frozen=True)
class GuardConstants:
    """E = 64(W+m+1)^3, B = s + E, nu = min{j >= 1 : m^j >= B}, C1 = max(20, nu+3), C0 = 128 m B^2 [Pr L2353-2372]."""

    E: int
    B: int
    nu: int
    C1: int
    C0: int

    @property
    def C0_digits(self) -> int:
        """Number of decimal digits of C0 (SPEC §2.7 table)."""
        return len(str(self.C0))


@dataclass(frozen=True)
class TripleCertificate:
    """Result of ``certify_triple`` (SPEC §2.7)."""

    h: int
    kind: str
    params: TripleParams
    z_b: int
    z_c: int
    L_over_N: Fraction
    scalar: dict
    factor: dict
    classes: tuple
    rank_sum: int
    abs_dim_change: int
    endpoints: dict
    saving: int
    saves: bool
    eta: Fraction
    tau_exp: int
    log_bound: object
    tau_ok: bool
    guard: GuardConstants | None
    q_radix: object
    dense: dict | None = None
    steps: tuple = field(default=())
    log_mode: str = "crude"
    tau_margin: Fraction = Fraction(0)
    q_radix_provenance: str = ""
    prime_grammar: dict | None = None

    def class_sums(self) -> dict:
        """Class-by-class rank sums: (stage, wire, edge) -> sum of multiplicity x rank (SPEC §2.7 step 5)."""
        out: dict = {}
        for r in self.classes:
            key = (r.stage, r.wire, r.edge)
            out[key] = out.get(key, 0) + r.multiplicity * r.rank
        return out

    def summary(self) -> str:
        """Printable summary of the main certified numbers (SPEC §2.7 expected-numbers table)."""
        p = self.params
        lines = [f"triple network h = {self.h}, kind = {self.kind}",
                 f"  v = {p.v}, N = {p.N}, m = {p.m}, I = {p.I}, z_b = {self.z_b}, z_c = {self.z_c}",
                 f"  W = {p.W}, L/N = {self.L_over_N}, s = {p.s} (rank sum certified: {self.rank_sum})",
                 f"  W m - s = {self.saving} ({'saving' if self.saves else 'NO SAVING'}), eta = {self.eta}",
                 f"  tau = 1 - 2^-{self.tau_exp} ({self.log_mode} log bound L = {_dec(self.log_bound)}): "
                 f"eta 2^{self.tau_exp} >= L ? {self.tau_ok} (margin {_dec(self.tau_margin)})",
                 f"  q_radix: {self.q_radix} ({self.q_radix_provenance})"]
        if self.guard:
            g = self.guard
            lines.append(f"  guard: nu = {g.nu}, C1 = {g.C1}, C0 has {g.C0_digits} digits ({str(g.C0)[:4]}...)")
        return "\n".join(lines)


# ----------------------------------------------------------------------------------------------- step 1
def step1_closed_forms(tn: TripleNetwork) -> dict:
    """Closed forms of SPEC §2.4, with the neighbor counts z recounted by enumerating all triples."""
    h, p = tn.h, tn.params
    T0 = (0, 1, 2)
    by_k = {0: 0, 1: 0, 2: 0, 3: 0}
    for T in combinations(range(h), 3):
        by_k[len(set(T0) & set(T))] += 1
    z_b = 3 * (h - 3) * (h - 4) // 2
    z_c = (h - 3) * (h - 4) * (h - 5) // 6 + 3 * (h - 3)
    if by_k[1] != z_b or by_k[0] + by_k[2] != z_c or (z_b if tn.kind == "bit" else z_c) != p.z:
        _fail("neighbor counts disagree with the closed forms")
    if p.W != 2 * p.N + p.I * (p.v * p.z + p.c) or p.L != p.I * p.c * h:
        _fail("closed forms inconsistent")
    return {"z_b": z_b, "z_c": z_c, "by_intersection": by_k}


# ----------------------------------------------------------------------------------------------- step 2
def _lemma5_symbolic(ops) -> dict:
    """Run one schedule (8 entries of +-V, +-G, +-R, +-J) on formal sums with scratch a, c, source x, target y:
    returns the final state; Lemma 5 needs y -> y + (JV + RG) x (forward) and restored a, c [Pr L715-718]."""
    st = {v: {((), v): 1} for v in "xyac"}

    def addto(var, letter, src, sgn):
        for (w, b), cf in st[src].items():
            key = ((letter,) + w, b)
            st[var][key] = st[var].get(key, 0) + sgn * cf
            if st[var][key] == 0:
                del st[var][key]

    for op in ops:
        sgn = 1 if op[0] == "+" else -1
        {"V": lambda: addto("a", "V", "x", sgn), "G": lambda: addto("c", "G", "x", sgn),
         "R": lambda: addto("y", "R", "c", sgn), "J": lambda: addto("y", "J", "a", sgn)}[op[1]]()
    return st


def step2_scalar(tn: TripleNetwork, dense: bool) -> dict:
    """Scalar layer (SPEC §2.7 step 2): (JV + RG)[S][T] from the lazily generated gate rows for the four
    intersection classes at every stage, recorded as (JV, RG, JV + RG) -- the side term cancels the central one at
    k = 1 (bit) resp. k in {0, 2} (complex) [Pr L719-723]; schedule pairs are mutual inverses; Lemma 5 algebra; the
    stage composition (x, y) -> (-y, x); gates per wire <= 12, fan-in <= W; optional dense v x v invocation check."""
    h, kind = tn.h, tn.kind
    T0 = (0, 1, 2)
    reps = {3: T0, 2: (0, 1, 3), 1: (0, 3, 4), 0: (3, 4, 5)}
    ident = (lambda k: 1 if k == 3 else 0) if kind == "bit" else (lambda k: ZI2(1 if k == 3 else 0))
    classes = {}
    for j in (1, 2, 3):
        fixed = {k: T0 for k in (1, 2, 3) if k != j}
        fwd = j != 2
        Jt, Vt, Rt, Gt = (5, 2, 4, 3) if fwd else (7, 0, 6, 1)
        tb, sb = ("Y", "X") if fwd else ("X", "Y")
        S = T0
        tgt = tn.data_role(tb, j, fixed, S)
        rrow = tn.gate_row(tn.gate_id(j, fixed, Rt), tgt)
        grows = {c: tn.gate_row(tn.gate_id(j, fixed, Gt), c) for c in rrow if c != tgt}
        for k, T in reps.items():
            src = tn.data_role(sb, j, fixed, T)
            val = ZI2(0) if kind == "complex" else 0
            if tn.is_neighbor(S, T):
                a = tn.role_id(("A", j, tuple(fixed.items()), S, T))
                cj = tn.gate_row(tn.gate_id(j, fixed, Jt, tn.triple_rank(S)), tgt).get(a, 0)
                cv = tn.gate_row(tn.gate_id(j, fixed, Vt, tn.triple_rank(T)), a).get(src, 0)
                val = val + cj * cv
            jv = val
            for c, g in grows.items():
                val = val + rrow[c] * g.get(src, 0)
            if kind == "bit":
                val %= 2
            if val != ident(k):
                _fail(f"stage {j}: (JV + RG) at |S cap T| = {k} is {val!r}, expected {ident(k)!r}")
            classes[(j, k)] = (jv, val - jv if kind == "complex" else (val - jv) % 2, val)
        _check_pairs(tn, j, fixed)
    st = _lemma5_symbolic(FORWARD)
    want = {"x": {((), "x"): 1}, "y": {((), "y"): 1, (("J", "V"), "x"): 1, (("R", "G"), "x"): 1},
            "a": {((), "a"): 1}, "c": {((), "c"): 1}}
    if st != want:
        _fail("forward schedule does not realize y += (JV + RG) x with restored scratch")
    st = _lemma5_symbolic(INVERSE)   # logical source = y, target = x: with the roles renamed
    want_inv = {"x": {((), "x"): 1}, "y": {((), "y"): 1, (("J", "V"), "x"): -1, (("R", "G"), "x"): -1},
                "a": {((), "a"): 1}, "c": {((), "c"): 1}}
    if st != want_inv:
        _fail("inverse schedule does not realize target -= (JV + RG) source")
    s1, s2 = ((1, 0), (1, 1)), ((1, -1), (0, 1))          # (x, y) column vectors: y += x ; x -= y
    mm = lambda A, B: tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)) for i in range(2))  # noqa
    comp = mm(s1, mm(s2, s1))
    if comp != ((0, -1), (1, 0)):
        _fail("Lemma 5 stage composition")
    reps_r = tn.representatives()
    for rid, _, desc in reps_r:
        o = tn.route(rid)
        want_sign = 1 if (kind == "bit" or desc != "Y data") else -1
        if (desc == "X data" and o != rid + tn.N) or (desc == "Y data" and o != rid - tn.N) or \
                ("data" not in desc and o != rid) or tn.route_sign(rid) != want_sign:
            _fail(f"route/route sign of {desc} disagree with Lemma 5")
    gpw = max(len(tn.vertices(rid)) - 2 for rid, _, _ in reps_r)
    fan = max(tn.z + 1, tn.v + tn.c)
    if gpw > 12 or fan > tn.W:
        _fail("gates per wire or fan-in bound violated")
    out = {"classes": classes, "lemma5": comp, "gates_per_wire": gpw, "max_fan_in": fan, "dense": False}
    if dense:
        _dense_invocation(tn)
        out["dense"] = True
    return out


def _check_pairs(tn: TripleNetwork, j: int, fixed: dict) -> None:
    """Schedule rows (0,5), (1,4), (2,7), (3,6) of one invocation are mutual inverses: same roles, unit diagonal,
    negated off-diagonal coefficients (transvections with N^2 = 0) [Pr L671-675].  Checked on the rows of the
    representative bank triple T0, of sampled side wires and of C_0, C_{h-1}, Cstar; full role lists are compared
    when they are small."""
    T0 = (0, 1, 2)
    r0 = tn.triple_rank(T0)
    one = 1 if tn.kind == "bit" else ZI2(1)
    base = 2 * tn.N + tn.inv_index(j, fixed) * tn.n_inv_roles
    for t1, t2 in ((0, 5), (1, 4), (2, 7), (3, 6)):
        side = t1 in (0, 2)
        g1, g2 = tn.gate_id(j, fixed, t1, r0 if side else 0), tn.gate_id(j, fixed, t2, r0 if side else 0)
        info = tn.gate_info(g1)
        if info.op[1] != tn.gate_info(g2).op[1] or info.op[0] == tn.gate_info(g2).op[0]:
            _fail(f"stage {j}: times {t1},{t2} are not an operation and its negation")
        if (tn.z if side else tn.v) <= 2000 and tn.gate_roles(g1) != tn.gate_roles(g2):
            _fail(f"stage {j}: paired gates {t1},{t2} touch different roles")
        sample = [tn.data_role(info.bank, j, fixed, T0)]
        if side:
            for r in sorted({0, tn.z // 2, tn.z - 1}):
                T = tn.nbr_unrank(T0, r)
                S_, T_ = (T0, T) if info.op[1] == "J" else (T, T0)
                sample.append(tn.role_id(("A", j, tuple(sorted(fixed.items())), S_, T_)))
        else:
            sample += [base + tn.v * tn.z, base + tn.v * tn.z + tn.h - 1, base + tn.v * tn.z + tn.c - 1]
        for r in sample:
            a, b = tn.gate_row(g1, r), tn.gate_row(g2, r)
            if set(a) != set(b) or a[r] != one or b[r] != one:
                _fail(f"stage {j}: gates at times {t1},{t2} differ on role {r}")
            for kk in a:
                if kk != r and not ((a[kk] == b[kk]) if tn.kind == "bit" else (a[kk] == -b[kk])):
                    _fail(f"stage {j}: gates at times {t1},{t2} are not mutual inverses")


def _dense_invocation(tn: TripleNetwork) -> None:
    """Dense v x v check of one full invocation (stage 1, other coordinates T0): JV + RG = I_v, every entry
    computed from the gate rows (SPEC §2.7 step 2, "when v <= 2024")."""
    T0 = (0, 1, 2)
    fixed = {2: T0, 3: T0}
    G = tn.gate_id(1, fixed, 3)
    base = 2 * tn.N + tn.inv_index(1, fixed) * tn.n_inv_roles
    grows = {c: tn.gate_row(G, c) for c in range(base + tn.v * tn.z, base + tn.v * tn.z + tn.c)}
    zero = 0 if tn.kind == "bit" else ZI2(0)
    for rs in range(tn.v):
        S = tn.triple(rs)
        tgt = tn.data_role("Y", 1, fixed, S)
        row: dict = {}
        jrow = tn.gate_row(tn.gate_id(1, fixed, 5, rs), tgt)
        for a, cj in jrow.items():
            if a == tgt:
                continue
            T = tn.role_name(a)[4]
            src = tn.data_role("X", 1, fixed, T)
            cv = tn.gate_row(tn.gate_id(1, fixed, 2, tn.triple_rank(T)), a)[src]
            row[src] = row.get(src, zero) + cj * cv
        for c, cr in tn.gate_row(tn.gate_id(1, fixed, 4), tgt).items():
            if c != tgt:
                for src, cg in grows[c].items():
                    if src < 2 * tn.N:
                        row[src] = row.get(src, zero) + cr * cg
        want = tn.data_role("X", 1, fixed, S)
        for src, val in row.items():
            if tn.kind == "bit":
                val %= 2
            if val != (1 if src == want else 0):
                _fail(f"dense invocation: (JV + RG)[{S}] has entry {val!r} at role {src}")
        if row.get(want, zero) in (0, ZI2(0)):
            _fail("dense invocation: missing diagonal")


# ----------------------------------------------------------------------------------------------- step 3
def _imul(A, B):
    Bt = list(zip(*B))
    return [[sum(x * y for x, y in zip(r, c)) for c in Bt] for r in A]


def step3_factor(tn: TripleNetwork) -> dict:
    """Factor layer on exact h x h matrices (SPEC §2.7 step 3).  Bit: G0 = I - J/9 invertible (h != 9), <t,t> = 2,
    <t_S,t_T> = |S cap T| - 1; for every reference set R used (none, {T0}, {T0, neighbor} per type) the atom
    projections are idempotent, G0-self-adjoint (so orthogonal projections onto nondegenerate atoms) and sum to I.
    Complex: t.t = 1, neighbors orthogonal, atom projections idempotent, symmetric, pairwise annihilating, sum to I,
    each atom nondegenerate and containing an odd-weight vector (Lemma 6 proof) [Pr L840-852, L1081-1090]."""
    h, kind = tn.h, tn.kind
    T0, nbrs = tn.representative_triples()
    R_sets = [(), (T0,)] + [(T0, T) for T, _ in nbrs]
    pairs = {k: T for k, T in {3: T0, 2: (0, 1, 3), 1: (0, 3, 4), 0: (3, 4, 5)}.items()}
    out = {"R_sets": R_sets}
    if kind == "bit":
        G9 = [[9 * (i == j) - 1 for j in range(h)] for i in range(h)]
        if rank_Q(G9) != h:
            _fail("G0 = I - J/9 is singular")
        t = lambda T: [1 if i in T else 0 for i in range(h)]  # noqa: E731
        for k, T in pairs.items():
            val = Fraction(sum(a * b for a, b in zip(t(T0), (sum(G9[i][j] * t(T)[j] for j in range(h))
                                                               for i in range(h)))), 9)
            if val != k - 1 or val != triple_inner(T0, T, "bit"):
                _fail(f"<t_S, t_T> != |S cap T| - 1 at k = {k}")
        for R in R_sets:
            atoms = [("L", T) for T in R] + [("C", R)]
            tot = [[0] * h for _ in range(h)]
            for at in atoms:
                P = p_atom_Q(at, h)
                A = [[int(x * 18) for x in r] for r in P]
                if any(Fraction(x) * 18 != int(Fraction(x) * 18) for r in P for x in r):
                    _fail("unexpected denominator")
                if _imul(A, A) != [[18 * x for x in r] for r in A]:
                    _fail(f"atom {at} projection not idempotent")
                colsum = [sum(A[i][j] for i in range(h)) for j in range(h)]
                GA = [[9 * A[i][j] - colsum[j] for j in range(h)] for i in range(h)]       # G9 A
                AtG = [[9 * A[j][i] - colsum[i] for j in range(h)] for i in range(h)]      # A^T G9
                if GA != AtG:
                    _fail(f"atom {at} projection not G0-self-adjoint")
                if Fraction(sum(A[i][i] for i in range(h)), 18) != (1 if at[0] == "L" else h - len(R)):
                    _fail(f"atom {at} has the wrong rank")
                tot = [[x + y for x, y in zip(r, s)] for r, s in zip(tot, A)]
            if tot != [[18 * (i == j) for j in range(h)] for i in range(h)]:
                _fail(f"atoms of R = {R} do not sum to I")
        if h <= 30:
            for tok in (LINE(T0), PERP(T0)) + tuple(PERP2(T0, T) for T, _ in nbrs):
                closed = p_atom_Q(("L", T0) if tok[0] == "LINE" else ("C", tuple(tok[1:])), h)
                if generic_projection_Q(token_basis_Q(tok, h), h) != closed:
                    _fail(f"closed-form projection of {tok} differs from V (V^T G V)^-1 V^T G")
            out["generic_crosscheck"] = True
    else:
        for k, T in pairs.items():
            if f2.dot(f2.vec(T0), f2.vec(T)) != triple_inner(T0, T, "complex"):
                _fail("binary triple inner product")
        I = tuple(1 << i for i in range(h))
        for R in R_sets:
            atoms = [("L", T) for T in R] + [("C", R)]
            Ps = [p_atom_F2(at, h) for at in atoms]
            mulF = lambda A, B: tuple(_rowmul(r, B) for r in A)  # noqa: E731
            acc = (0,) * h
            for at, P in zip(atoms, Ps):
                if mulF(P, P) != P or P != tuple(f2.cols_to_rows(P, h)):
                    _fail(f"atom {at}: binary projection not idempotent / symmetric")
                basis = (f2.vec(at[1]),) if at[0] == "L" else f2.perp([f2.vec(T) for T in R], h)
                if len(basis) != (1 if at[0] == "L" else h - len(R)) or not f2.is_nondegenerate(basis):
                    _fail(f"atom {at} degenerate or of wrong dimension")
                wit = f2.vec(at[1]) if at[0] == "L" else 1 << min(set(range(h)) - set().union(*map(set, R)))
                if wit.bit_count() % 2 != 1 or _rowapply(P, wit) != wit:
                    _fail(f"atom {at} has no odd-weight vector")
                if h <= 30 and _projmat(basis, h) != P:
                    _fail(f"atom {at}: closed form differs from V (V^T V)^-1 V^T")
                acc = tuple(a ^ b for a, b in zip(acc, P))
            for x in range(len(Ps)):
                for y in range(len(Ps)):
                    if x != y and any(mulF(Ps[x], Ps[y])):
                        _fail("atom projections do not annihilate each other")
            if acc != I:
                _fail(f"atoms of R = {R} do not sum to I")
    return out


def _rowmul(r: int, B) -> int:
    out = 0
    while r:
        low = r & -r
        out ^= B[low.bit_length() - 1]
        r ^= low
    return out


def _rowapply(P, x: int) -> int:
    return sum(((row & x).bit_count() & 1) << i for i, row in enumerate(P))


def _projmat(basis, h):
    pr = f2.Projector(basis)
    return tuple(f2.cols_to_rows([pr(1 << i) for i in range(h)], h))


# ----------------------------------------------------------------------------------------------- steps 4-5
def _names(tn: TripleNetwork, rid: int) -> dict:
    T0, nbrs = tn.representative_triples()
    names = {T0: "T0"}
    for T, _ in nbrs:
        names[T] = f"T{len(set(T0) & set(T))}"
    return names


def step4_5_labels_ranks(tn: TripleNetwork) -> tuple[tuple, int, int]:
    """Label layer and rank sum (SPEC §2.7 steps 4-5): for every orbit representative and every edge, the cell
    calculus gives nesting, the residual (orthogonal sum of pure tensors), its dimension (checked against the Lemma 6
    table), the direction (only center 3->4 decreases, by exactly h) and the exact bit rank (= dim except the stage-1
    X source edge 2 P_{U_a}, rank 1 [Pr L1160-1165]).  Returns (rows, rank sum, sum of |dim changes|)."""
    h, kind = tn.h, tn.kind
    rows, rank_sum, abs_sum, mult_sum = [], 0, 0, 0
    for rid, mult, desc in tn.representatives():
        mult_sum += mult
        names = _names(tn, rid)
        for k, (tail, head, ft, fh, cls) in enumerate(tn.sym_edges(rid)):
            j, wire, edge = cls
            res = edge_calculus(h, kind, ft, fh)
            a, f = h ** (j - 1), h ** (3 - j)
            exp = LEMMA6[(wire, edge)](a, h, f)
            if res.dim != exp:
                _fail(f"{desc} {cls}: residual dimension {res.dim} != Lemma 6 table {exp}")
            if (res.direction < 0) != (wire == "center" and edge == "3->4"):
                _fail(f"{desc} {cls}: unexpected direction {res.direction}")
            if res.direction < 0 and res.dim != h:
                _fail("decreasing center edge must lose exactly h")
            rank = res.bit_rank if kind == "bit" else res.dim
            want_rank = 1 if (kind == "bit" and wire == "X" and edge == "in->2" and j == 1) else exp
            if rank != want_rank:
                _fail(f"{desc} {cls}: rank {rank} != {want_rank}")
            rank_sum += mult * rank
            abs_sum += mult * res.dim
            rows.append(EdgeClassRow(stage=j, wire=wire, edge=edge, role=desc, multiplicity=mult,
                                     tail=ft.label.render(names) if ft.sign > 0 else "-" + ft.label.render(names),
                                     head=fh.label.render(names), residual=res.residual.render(names), dim=res.dim,
                                     expected_dim=exp, direction=res.direction, rank=rank))
    p = tn.params
    if mult_sum != p.W:
        _fail("orbit sizes do not add up to W")
    if abs_sum != p.W * p.m - 2 * p.N + 2 * p.L:
        _fail("sum of |dim changes| != W m - 2N + 2L  (7)")
    if rank_sum != p.s:
        _fail(f"certified rank sum {rank_sum} != closed form s = {p.s}")
    return tuple(rows), rank_sum, abs_sum


# ----------------------------------------------------------------------------------------------- step 6
def step6_endpoints(tn: TripleNetwork, seed: int = 0) -> dict:
    """Endpoints (SPEC §2.7 step 6).  Bit: on every representative route the cell coefficients of
    M_sink(rho(w)) - M_source(w) are all 1, i.e. the difference is sum_c P_c = I (Prop 7; factor level
    P_LINE + P_PERP = I from step 3).  Complex: U_a and U_a^perp partition the cells, so q_{U_a^perp} = wt - q_{U_a}
    and q_{U_a}(x) = wt(u_a)[u_a . x]; with omega = wt(u_a) = 27 odd and theta = 27 = omega (mod 4) the Z_{supp u_a}
    correction gives theta + q_out(x+z) - q_in(x+z) = wt(x) + (theta - omega) + 2(omega - 1)[u.x] = wt(x)
    (27 + 29 = 0 mod 4 in SPEC's form); other routes are 0 -> F, i.e. C^(x)m; plus explicit evaluations at random
    points and at e_i, e_i + e_j (i, j in supp u_a) [Pr L1285-1310]."""
    h, kind, m = tn.h, tn.kind, tn.m
    out = {}
    for rid, _, desc in tn.representatives():
        o = tn.route(rid)
        src, snk = tn.source_frame(rid), tn.sink_frame(o)
        cs = CellSystem(h, kind, [src.label, snk.label])
        Cs, Ct = cs.cells(src.label), cs.cells(snk.label)
        allcells = {(x, y, z) for x in cs.atoms[0] for y in cs.atoms[1] for z in cs.atoms[2]}
        if kind == "bit":
            lam = {c: snk.sign * (c in Ct) - src.sign * (c in Cs) for c in allcells}
            if any(v != 1 for v in lam.values()):
                _fail(f"{desc}: M_sink(rho(w)) - M_source(w) != I")
        else:
            if Cs & Ct or (Cs | Ct) != allcells:
                _fail(f"{desc}: source and sink labels do not split the full space")
            z_pre, z_post, th = tn.pre_zmask(rid), tn.post_zmask(o), tn.post_ipow(o)
            if desc == "X data":
                a = tn.role_name(rid)[1]
                u = f2.tensor3(f2.vec(a[0]), f2.vec(a[1]), f2.vec(a[2]), h)
                omega = u.bit_count()
                if omega != 27 or f2.dot(u, u) != 1 or len(Cs) != 1 or cs.dim(Cs) != 1:
                    _fail("U_a must be the line of u_a, of weight 27 and norm 1")
                if tuple(z_pre) != tuple(z_post) or tuple(z_pre) != f2.support(u):
                    _fail("pre/post Z masks must both be supp(u_a)")
                if th % 4 != omega % 4 or omega % 2 != 1:
                    _fail("theta must equal wt(u_a) mod 4 with wt(u_a) odd")
                rng = random.Random(seed)
                sup = f2.support(u)
                pts = [rng.getrandbits(m) for _ in range(16)] + [1 << i for i in sup[:5]] + \
                      [(1 << i) | (1 << j) for i in sup[:4] for j in (sup[-1], 0, m - 1) if i != j]
                for x in pts:
                    y = x ^ u
                    q_in = (u.bit_count() if f2.dot(u, y) else 0) % 4
                    q_out = (y ^ (u if f2.dot(u, y) else 0)).bit_count() % 4
                    if (th + q_out - q_in - x.bit_count()) % 4:
                        _fail("corrected X -> Y route fails at a test point")
                out["omega"], out["theta"] = omega, th
            elif z_pre or z_post or th:
                _fail(f"{desc}: unexpected endpoint corrections")
    out["routes_checked"] = len(tn.representatives())
    return out


# ----------------------------------------------------------------------------------------------- steps 7-8
def step7_savings(p: TripleParams, tau_exp: int, mode: str = "crude") -> dict:
    """W m - s with its sign, eta exactly, and the tau test with the log bound of ``mode`` (``tau_test``)."""
    sav = p.W * p.m - p.s
    ok, margin = tau_test(p, tau_exp, mode)
    return {"saving": sav, "saves": sav > 0, "eta": Fraction(sav, p.W * p.m), "log_bound": log_bound(p.m, mode),
            "tau_ok": ok, "tau_margin": margin}


def guard_constants(p: TripleParams) -> GuardConstants:
    """SPEC §2.7 step 8 / §4.8 [Pr L2353-2372]."""
    E = 64 * (p.W + p.m + 1) ** 3
    B = p.s + E
    nu = 1
    while p.m ** nu < B:
        nu += 1
    return GuardConstants(E=E, B=B, nu=nu, C1=max(20, nu + 3), C0=128 * p.m * B * B)


# ----------------------------------------------------------------------------------------------- driver
def certify_triple(h: int, kind: str, tau_exp: int = 50, dense_scalar: bool | None = None,
                   dense_spot: int = 0, seed: int = 0, network: TripleNetwork | None = None,
                   log_bound: str = "crude", prime_brute_force: bool = False,
                   prime_dense: bool = False) -> TripleCertificate:
    """Certify the triple network (h, kind) exactly (SPEC §2.7 steps 1-10).

    ``dense_scalar``: dense v x v invocation check (default: when v <= 2024).  ``dense_spot``: number of random
    invocations per stage for the dense spot check of step 10 (only for m <= 1000; 0 = skip).  Never builds an
    m x m matrix for h >= 21.  Raises NotAnInterface if any check fails; savings are reported, never asserted.
    ``network``: certify this descriptor instance instead of ``TripleNetwork(h, kind)`` (tests of broken variants).
    ``log_bound``: 'crude' (default, the preprint's ln m < max(20, bitlen m)) or 'sharp' (certified ln m enclosure)
    for the tau test of step 7.  Step 9 (bit network): 9a prime alphabet, 9b edge grammar always;
    ``prime_brute_force`` adds 9c (h <= 12: literal lower_bruhat on every ordered primitive and gadget) and
    ``prime_dense`` adds 9d (m <= 512: one materialized edge per stage and edge class)."""
    tn = TripleNetwork(h, kind) if network is None else network
    if (tn.h, tn.kind) != (h, kind):
        raise ValueError("network does not match (h, kind)")
    p = tn.params
    steps = []
    s1 = step1_closed_forms(tn)
    steps.append("1 closed forms")
    if dense_scalar is None:
        dense_scalar = p.v <= 2024
    scalar = step2_scalar(tn, dense_scalar)
    steps.append("2 scalar layer")
    factor = step3_factor(tn)
    steps.append("3 factor layer")
    rows, rank_sum, abs_sum = step4_5_labels_ranks(tn)
    steps += ["4 label layer", "5 rank sum"]
    endpoints = step6_endpoints(tn, seed)
    steps.append("6 endpoints")
    sv = step7_savings(p, tau_exp, log_bound)
    steps.append("7 savings")
    guard = guard_constants(p) if kind == "complex" else None
    steps.append("8 guard constants" if guard else "8 (bit: no guard constants)")
    prime_grammar = None
    if kind == "bit":                       # q_radix = 5; its finite certificate (cheap)
        from .primes import brute_force_primitives, certify_prime_alphabet, full_edge_primes, grammar_certificate
        prime_grammar = {"9a": certify_prime_alphabet(h), "9b": grammar_certificate(tn)["terms"]}
        steps += ["9a prime alphabet",
                  "9b edge grammar per stage and class (mixed edge, 2 P_U; X^2 = X, XY = YX = 0, K D0 = K)"]
        if prime_brute_force:
            if h > 12:
                raise ValueError("the 9c brute force is for h <= 12")
            rep = brute_force_primitives(h)
            if not rep.primes <= {2, 3}:
                _fail(f"9c: primes {sorted(rep.primes)} outside {{2, 3}}")
            prime_grammar["9c"] = {"counts": dict(rep.counts), "primes": sorted(rep.primes)}
            steps.append("9c brute force: literal lower_bruhat on every ordered primitive and gadget")
        if prime_dense:
            if p.m > 512:
                raise ValueError("the 9d dense check is for m <= 512")
            seen, primes = {}, set()
            for rid, _, _ in tn.representatives():
                for cls, sym, rank, pr in full_edge_primes(tn, rid):
                    if sym != rank:
                        _fail(f"9d: dense rank {rank} != symbolic {sym} on {cls}")
                    seen[cls] = seen.get(cls, 0) + 1
                    primes |= pr
            if not primes <= {2, 3}:
                _fail(f"9d: primes {sorted(primes)} outside {{2, 3}}")
            prime_grammar["9d"] = {"edges": sum(seen.values()), "classes": len(seen), "primes": sorted(primes)}
            steps.append("9d one materialized edge per (stage, edge class): literal lower_bruhat")
    else:
        steps.append("9 q_radix not applicable (complex network)")
    dense = None
    if dense_spot:
        from .triple_dense import DenseTriple, dense_spot_check
        if p.m > 1000:
            raise ValueError("the dense spot check is only for m <= 1000")
        dt = DenseTriple(tn)
        spot = dense_spot_check(tn, dense_spot, seed, dt)
        dense = {"edges": len(spot), "methods": sorted({r.method for r in spot})}
        steps.append("10 dense spot check")
    return TripleCertificate(h=h, kind=kind, params=p, z_b=s1["z_b"], z_c=s1["z_c"], L_over_N=Fraction(p.L, p.N),
                             scalar=scalar, factor=factor, classes=rows, rank_sum=rank_sum, abs_dim_change=abs_sum,
                             endpoints=endpoints, saving=sv["saving"], saves=sv["saves"], eta=sv["eta"],
                             tau_exp=tau_exp, log_bound=sv["log_bound"], tau_ok=sv["tau_ok"], guard=guard,
                             q_radix=tn.q_radix, dense=dense, steps=tuple(steps), log_mode=log_bound,
                             tau_margin=sv["tau_margin"], q_radix_provenance=tn.q_radix_provenance,
                             prime_grammar=prime_grammar)


def first_saving_h(kind: str, start: int = 7, stop: int = 200) -> int:
    """The least admissible h whose closed forms give s < W m (bit: 39, complex: 22; SPEC §2.7 thresholds)."""
    for h in range(start, stop):
        if kind == "bit" and h == 9:
            continue
        if triple_params(h, kind).saving > 0:
            return h
    raise ValueError("no saving h in range")

