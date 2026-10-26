"""Validation of any supplied network (``net.validate``; SPEC §2.6 = S1 §3.5 + S2 §3.6).  Run at compile time; fail
loudly with ``NotAnInterface`` naming the role / edge / check.

Checks: 1 structure; 2 scalar map (exact W x W composition = the declared signed permutation); 3 bit frames (A_e,
exact rank, A_e = E1 Pi E2, triangular factors, endpoint identities (11)); 4 the prime q_radix; 5 phase labels
(nondegenerate, nested, residual basis, eps, M_cols, reduce_ops, Prop 8 edge identity); 6 phase endpoints (corrected
route = C^{(x)m} per column); 7 counts W, m, s and the saving W m - s (never needed for correctness).
The per-edge / per-role checkers are reused for samples of large lazily generated networks (``triple_dense``).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from . import f2, phase
from .errors import NotAnInterface
from .model import DOMAINS, SOURCE, BitEdge, CompiledNetwork, Network, PhaseEdge, compile_network, frame_at, \
    role_vertices, zmask_int
from .qmatrix import bruhat_product, identity, is_invertible_lower, is_odd_prime, mul, qmat, rank_Q, sub
from .zi2 import ZI2


@dataclass(frozen=True)
class ValidationReport:
    """Outcome of ``validate`` (SPEC §2.6 item 7): counts, the saving W m - s with its sign, and how endpoints were
    checked ('dense' 2^m x 2^m matrices, 'exhaustive' over all Hadamard points, or 'quadratic' O(m^2) points)."""

    domain: str
    W: int
    m: int
    s: int
    saving: int
    saves: bool
    q_radix: int | None
    n_edges: int
    endpoint_method: str | None
    aux_roles: tuple[int, ...]


def _fail(msg: str):
    raise NotAnInterface(msg)


# ----------------------------------------------------------------------------------------------- 1 structure
def _check_bit_frame(M, m: int, where: str):
    if not (isinstance(M, tuple) and len(M) == m and all(isinstance(r, tuple) and len(r) == m for r in M)):
        _fail(f"{where}: bit frame must be an m x m tuple matrix (m = {m})")
    if not all(isinstance(x, (int, Fraction)) and not isinstance(x, bool) for r in M for x in r):
        _fail(f"{where}: bit frame entries must be rational")


def check_label(U, m: int, where: str):
    """A label: a tuple of independent m-bit ints spanning a nondegenerate subspace (SPEC §2.3, §2.6 item 5)."""
    if not (isinstance(U, tuple) and all(isinstance(u, int) and 0 < u < (1 << m) for u in U)):
        _fail(f"{where}: label must be a tuple of nonzero m-bit ints")
    if not f2.is_independent(U):
        _fail(f"{where}: label basis is not independent")
    if not f2.is_nondegenerate(U):
        _fail(f"{where}: label is degenerate (Gram matrix singular over F2)")


def check_structure(c: CompiledNetwork):
    """SPEC §2.6 item 1: legal unique role ids per gate, every role has a source and a sink, one frame per gate,
    every edge joins consecutive vertices of its role, route a permutation, signs +-1 (all +1 over F2)."""
    check_network_structure(c.net)
    check_compiled_structure(c)


def check_network_structure(net: Network):
    """The part of SPEC §2.6 item 1 that needs only the raw network (run before compiling, for clear messages)."""
    if net.domain not in DOMAINS:
        _fail(f"unknown domain {net.domain!r}")
    W, m = net.W, net.m
    if W < 2 or m < 2:
        _fail(f"need W >= 2 and m >= 2 [Pr L1436], got W = {W}, m = {m}")
    if len(set(net.roles)) != W:
        _fail("role names are not unique")
    for name, seq in (("source", net.source), ("sink", net.sink), ("route", net.route),
                      ("route_sign", net.route_sign)):
        if len(seq) != W:
            _fail(f"{name} must have one entry per role")
    if sorted(net.route) != list(range(W)):
        _fail("route is not a permutation of the roles")
    if any(s not in (1, -1) for s in net.route_sign):
        _fail("route signs must be +1 or -1")
    if net.domain == "F2" and any(s != 1 for s in net.route_sign):
        _fail("over F2 every route sign is +1")
    for g, gate in enumerate(net.gates):
        k = len(gate.roles)
        if k == 0 or len(set(gate.roles)) != k or any(not (isinstance(w, int) and 0 <= w < W) for w in gate.roles):
            _fail(f"gate {g}: roles must be distinct legal role ids")
        if len(gate.matrix) != k or any(len(r) != k for r in gate.matrix):
            _fail(f"gate {g}: matrix must be len(roles) x len(roles)")
        for r in gate.matrix:
            for x in r:
                if net.domain == "F2" and x not in (0, 1):
                    _fail(f"gate {g}: F2 entries must be 0 or 1")
                if net.domain == "ZI2":
                    try:
                        ZI2.of(x)
                    except (TypeError, ValueError):
                        _fail(f"gate {g}: entry {x!r} is not in Z[i, 1/2]")
    frames = [(f"source of role {w}", F) for w, F in enumerate(net.source)] + \
             [(f"sink of role {w}", F) for w, F in enumerate(net.sink)] + \
             [(f"gate {g}", gate.frame) for g, gate in enumerate(net.gates)]
    for where, F in frames:
        if net.domain == "F2":
            _check_bit_frame(F, m, where)
        else:
            check_label(F, m, where)
    corr = (net.pre_zmask, net.post_zmask, net.post_ipow)
    if net.domain == "F2" and any(x is not None and any(map(bool, x)) for x in corr):
        _fail("bit networks have no endpoint corrections")
    for name, x in zip(("pre_zmask", "post_zmask"), corr[:2]):
        if x is not None:
            if len(x) != W:
                _fail(f"{name} must have one entry per role")
            for e in x:
                if not (e is None or isinstance(e, int) or all(isinstance(t, int) and 0 <= t < m for t in e)):
                    _fail(f"{name}: coordinates must lie in [0, m)")
                if zmask_int(e) >> m:
                    _fail(f"{name}: mask exceeds m coordinates")
    if corr[2] is not None and (len(corr[2]) != W or not all(isinstance(t, int) for t in corr[2])):
        _fail("post_ipow must be one integer per role")


def check_compiled_structure(c: CompiledNetwork):
    """SPEC §2.6 item 1 on compiled data: vertex lists = gate touch lists, edges join consecutive vertices."""
    net = c.net
    vertices = role_vertices(net)
    if c.vertices != vertices:
        _fail("compiled vertex lists differ from the gate touch lists")
    for w, (vs, es) in enumerate(zip(vertices, c.edges)):
        pairs = tuple(zip(vs, vs[1:]))
        if tuple((e.role, e.tail, e.head) for e in es) != tuple((w, t, h) for t, h in pairs):
            _fail(f"role {w}: edges do not join consecutive vertices")
        for e in es:
            if not isinstance(e, BitEdge if net.domain == "F2" else PhaseEdge):
                _fail(f"role {w}: edge type does not match the domain")


# ----------------------------------------------------------------------------------------------- 2 scalar map
def compose_scalar_map(net: Network):
    """The exact W x W matrix T of the whole scalar network (out = T @ in), gates applied from saved inputs
    (SPEC §2.1 semantics, §2.6 item 2)."""
    W = net.W
    f2dom = net.domain == "F2"
    zero = 0 if f2dom else ZI2(0)
    T = [[(1 if i == j else 0) if f2dom else ZI2(1 if i == j else 0) for j in range(W)] for i in range(W)]
    for gate in net.gates:
        old = [T[r] for r in gate.roles]
        new = []
        for k in range(len(gate.roles)):
            acc = [zero] * W
            for l, row in enumerate(old):
                cf = gate.matrix[k][l]
                if f2dom:
                    if cf & 1:
                        acc = [(a + b) & 1 for a, b in zip(acc, row)]
                else:
                    cf = ZI2.of(cf)
                    if not cf.is_zero():
                        acc = [a + cf * b for a, b in zip(acc, row)]
            new.append(acc)
        for k, r in enumerate(gate.roles):
            T[r] = new[k]
    return T


def check_scalar_map(net: Network) -> tuple[int, ...]:
    """The composite equals the signed permutation out[route[w]] = route_sign[w] * in[w] for arbitrary values on
    every role (auxiliaries included); returns the auxiliary roles (fixed points with sign +1)."""
    T = compose_scalar_map(net)
    for o in range(net.W):
        for w in range(net.W):
            want = net.route_sign[w] if net.route[w] == o else 0
            got = T[o][w]
            if (got != want) if net.domain == "ZI2" else (got != want % 2):
                _fail(f"scalar map: output role {o} depends on input role {w} with coefficient {got!r}, "
                      f"expected {want} (route/route_sign)")
    return tuple(w for w in range(net.W) if net.route[w] == w and net.route_sign[w] == 1)


# ----------------------------------------------------------------------------------------------- 3 bit frames, 4 prime
def check_bit_edge(e: BitEdge, M_tail, M_head, m: int, where: str = ""):
    """SPEC §2.6 item 3 for one edge: A = M_head - M_tail, rank = rank_Q(A), A = E1 Pi E2 with E1, E2 (and their
    stored inverses) invertible lower triangular and Pi a partial permutation with ``rank`` ones."""
    where = where or f"role {e.role} edge {e.tail}->{e.head}"
    A = sub(qmat(M_head), qmat(M_tail))
    if e.A != A:
        _fail(f"{where}: stored A differs from M_head - M_tail")
    r = rank_Q(A)
    if e.rank != r:
        _fail(f"{where}: stored rank {e.rank} != rank_Q(A) = {r}")
    piv = tuple(e.pivots)
    if len(piv) != r or len({i for i, _ in piv}) != r or len({j for _, j in piv}) != r or \
            any(not (0 <= i < m and 0 <= j < m) for i, j in piv):
        _fail(f"{where}: Pi must be a partial permutation with rank = {r} ones")
    for name in ("E1", "E2", "E1inv", "E2inv"):
        X = getattr(e, name)
        if len(X) != m or not is_invertible_lower(X):
            _fail(f"{where}: {name} is not invertible lower triangular")
    I = identity(m)
    if mul(e.E1, e.E1inv) != I or mul(e.E2, e.E2inv) != I:
        _fail(f"{where}: stored inverse factors are wrong")
    if bruhat_product(e.E1, piv, e.E2) != A:
        _fail(f"{where}: A != E1 Pi E2")


def check_bit_endpoint(M_source, M_sink_route, m: int, where: str):
    """Interface (11): M_sink(rho(w)) - M_source(w) = I_m [Pr L1453-1456]."""
    if sub(qmat(M_sink_route), qmat(M_source)) != identity(m):
        _fail(f"{where}: endpoint identity M_sink(rho(w)) - M_source(w) = I fails")


def forbidden_violations(q: int, frames, factors) -> list[str]:
    """Reasons why q is not admissible (SPEC §3.2): q | a denominator of a frame or factor, or q | the numerator of
    a diagonal entry of a triangular factor."""
    out = []
    for i, M in enumerate(frames):
        if any(Fraction(x).denominator % q == 0 for r in M for x in r):
            out.append(f"q divides a denominator of frame #{i}")
    for e in factors:
        for name in ("E1", "E2", "E1inv", "E2inv"):
            X = getattr(e, name)
            if any(Fraction(x).denominator % q == 0 for r in X for x in r):
                out.append(f"q divides a denominator of {name} on edge {e.role}:{e.tail}->{e.head}")
            if any(Fraction(X[i][i]).numerator % q == 0 for i in range(len(X))):
                out.append(f"q divides a diagonal numerator of {name} on edge {e.role}:{e.tail}->{e.head}")
    return out


def check_prime(q, frames, factors):
    """SPEC §2.6 item 4: q_radix is an odd prime dividing no forbidden integer."""
    if not (isinstance(q, int) and is_odd_prime(q)):
        _fail(f"q_radix = {q!r} is not an odd prime")
    bad = forbidden_violations(q, frames, factors)
    if bad:
        _fail(f"q_radix = {q}: " + "; ".join(bad[:3]))


# ----------------------------------------------------------------------------------------------- 5 phase labels
def check_phase_edge(e: PhaseEdge, U_tail, U_head, m: int, where: str = "", method: str = "auto"):
    """SPEC §2.6 item 5 for one edge: nested labels, direction, residual basis in the larger label, orthogonal to the
    smaller, spanning the residual, Gram = I; eps by the popcount rule; M_cols invertible with the basis first;
    replaying reduce_ops gives I; and Prop 8: C_head C_tail^{-1} = prod C_{v_j}^{eps_j}."""
    where = where or f"role {e.role} edge {e.tail}->{e.head}"
    th, ht = f2.is_subspace(U_tail, U_head), f2.is_subspace(U_head, U_tail)
    if not (th or ht):
        _fail(f"{where}: labels are not nested")
    d = 0 if (th and ht) else (1 if th else -1)
    if e.direction != d:
        _fail(f"{where}: direction {e.direction} != {d}")
    small, large = (U_tail, U_head) if d >= 0 else (U_head, U_tail)
    rho = len(large) - len(small)
    B = tuple(e.basis)
    if len(B) != rho:
        _fail(f"{where}: residual basis has {len(B)} vectors, residual dimension is {rho}")
    if not all(isinstance(v, int) and 0 < v < (1 << m) for v in B) or not f2.is_subspace(B, large):
        _fail(f"{where}: residual basis is not inside the larger label")
    if any(f2.dot(v, u) for v in B for u in small):
        _fail(f"{where}: residual basis is not orthogonal to the smaller label")
    if f2.gram(B) != f2.identity_rows(rho):
        _fail(f"{where}: residual basis is not orthonormal")
    if tuple(e.eps) != f2.eps_signs(B, d):
        _fail(f"{where}: eps signs violate the popcount rule")
    M = tuple(e.M_cols)
    if len(M) != m or M[:rho] != B or f2.rank(M) != m or any(not (0 < c < (1 << m)) for c in M):
        _fail(f"{where}: M_cols must be invertible with the residual basis as its first columns")
    if f2.replay_reduce_ops(M, e.reduce_ops, m) != f2.identity_rows(m):
        _fail(f"{where}: replaying reduce_ops does not reduce M to I")
    meth = phase.method_for(m, method)
    ok = {"dense": phase.edge_identity_dense, "exhaustive": phase.edge_identity_exhaustive,
          "quadratic": phase.edge_identity_quadratic}[meth](U_tail, U_head, B, e.eps, m)
    if not ok:
        _fail(f"{where}: Prop 8 edge identity fails ({meth})")


def check_phase_route(U_src, U_sink, z_pre: int, z_post: int, theta: int, m: int, where: str,
                      method: str = "auto") -> str:
    """SPEC §2.6 item 6 for one route: i^theta Z_post C_sink C_src^{-1} Z_pre = C^{(x)m} per column (the scalar
    route sign is undone once per role and does not enter); returns the method used."""
    meth = phase.method_for(m, method)
    ok = {"dense": phase.corrected_route_dense, "exhaustive": phase.corrected_route_exhaustive,
          "quadratic": phase.corrected_route_quadratic}[meth](U_src, U_sink, z_pre, z_post, theta, m)
    if not ok:
        _fail(f"{where}: corrected route operator is not C^(x)m ({meth})")
    return meth


# ----------------------------------------------------------------------------------------------- driver
def validate(obj, method: str = "auto") -> ValidationReport:
    """Run every check of SPEC §2.6 on a ``Network`` (compiled here) or a ``CompiledNetwork`` (its stored edges and
    prime are re-verified against the frames).  Raises ``NotAnInterface`` on the first failure."""
    if not isinstance(obj, CompiledNetwork):
        check_network_structure(obj)
    c = obj if isinstance(obj, CompiledNetwork) else compile_network(obj)
    net, m = c.net, c.net.m
    check_structure(c)
    aux = check_scalar_map(net)
    endpoint_method = None
    for w, es in enumerate(c.edges):
        for e in es:
            Ft, Fh = frame_at(net, w, e.tail), frame_at(net, w, e.head)
            if net.domain == "F2":
                check_bit_edge(e, Ft, Fh, m)
            else:
                check_phase_edge(e, Ft, Fh, m, method=method)
    pre = net.pre_zmask or (None,) * net.W
    post = net.post_zmask or (None,) * net.W
    ipow = net.post_ipow or (0,) * net.W
    for w in range(net.W):
        o = net.route[w]
        where = f"route {w} -> {o}"
        if net.domain == "F2":
            check_bit_endpoint(net.source[w], net.sink[o], m, where)
        else:
            endpoint_method = check_phase_route(net.source[w], net.sink[o], zmask_int(pre[w]), zmask_int(post[o]),
                                                ipow[o], m, where, method)
    s = sum(e.rank for es in c.edges for e in es)
    if s != c.s:
        _fail(f"stored s = {c.s} != sum of edge ranks {s}")
    if net.domain == "F2":
        frames = list(net.source) + list(net.sink) + [g.frame for g in net.gates]
        check_prime(c.q, frames, c.all_edges)
    elif c.q is not None:
        _fail("a complex network has no q_radix")
    saving = net.W * m - s
    return ValidationReport(domain=net.domain, W=net.W, m=m, s=s, saving=saving, saves=saving > 0, q_radix=c.q,
                            n_edges=len(c.all_edges), endpoint_method=endpoint_method, aux_roles=aux)


__all__ = ["ValidationReport", "validate", "check_structure", "check_network_structure", "check_compiled_structure",
           "check_scalar_map", "compose_scalar_map",
           "check_bit_edge", "check_bit_endpoint", "check_prime", "forbidden_violations", "check_label",
           "check_phase_edge", "check_phase_route", "SOURCE"]
