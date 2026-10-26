"""Exact reference executor for SMALL networks (tests only; not used by the multiplier).

Executes a compiled network literally on arrays indexed by a common address set Omega, following the frame invariant
(5) of SPEC §2.1 [Pr L762-809]: NO source frame is applied to the physical input; on every edge u -> v the array of
that role is changed by D_v D_u^{-1}; each gate acts pointwise (saved inputs) at every address.  The result is
compared with D_out S_Omega D_in^{-1} computed independently, and on valid interfaces with the promised end result:

* bit (F2): Omega = (H, D) in (Z/Q)^m x (Z/Q)^m, Q = q^b, D_v = Phi_{M_v} (move entry (H, D) to (H + M D, D)),
  payloads are bit vectors (ints, XOR); every role's output is the shear H <- H + D of the routed input (Prop 11
  proof [Pr L1485-1497]).  Edges can be applied directly (``mode='dense'``) or through the Lemma 9 factors by the
  Lemma 10 address map (``mode='factored'``) [Pr L1418-1428].
* complex (ZI2): Omega = (F2^m)^k (k columns), D_v = C_U^{(x)k}; edges applied as dense C_V C_U^{-1}
  (``'dense'``), as prod C_{v_j}^{eps_j} (``'factored'``, Prop 8) or as P_M (prod C_{e_j}^{eps_j}) P_M^{-1} with
  ``reduce_ops`` (``'coordinate'``, (16)); after the source/sink corrections, the route-sign correction and undoing
  the exchange, every role carries C^{(x)mk} of its input (Prop 8 [Pr L1275-1310]).
"""

from __future__ import annotations

from . import f2, phase
from .model import SOURCE, CompiledNetwork, zmask_int
from .qmatrix import neg, specialize_matrix
from .zi2 import A_COEF, B_COEF, ZERO, ZI2, i_pow


# ----------------------------------------------------------------------------------------------- bit networks
def _digits(idx: int, n: int, Q: int) -> list[int]:
    out = []
    for _ in range(n):
        idx, r = divmod(idx, Q)
        out.append(r)
    return out


def _index(digits, Q: int) -> int:
    idx = 0
    for d in reversed(digits):
        idx = idx * Q + d
    return idx


def shear_permutation(Mq, m: int, Q: int) -> list[int]:
    """perm[idx(H, D)] = idx(H + M D mod Q, D) for an integer matrix Mq mod Q (Phi_M, SPEC §2.2)."""
    perm = []
    for idx in range(Q ** (2 * m)):
        d = _digits(idx, 2 * m, Q)
        H, D = d[:m], d[m:]
        H2 = [(H[i] + sum(Mq[i][j] * D[j] for j in range(m))) % Q for i in range(m)]
        perm.append(_index(H2 + D, Q))
    return perm


def shear_via_factors(edge, H, D, Q: int):
    """Lemma 10 address map: D <- E2 D, H <- E1^{-1} H, H <- H + Pi D, H <- E1 H, D <- E2^{-1} D (mod Q), which
    equals (H + A D, D) for A = E1 Pi E2 [Pr L1418-1428]."""
    m = len(H)
    E1, E2, E1i, E2i = (specialize_matrix(X, Q) for X in (edge.E1, edge.E2, edge.E1inv, edge.E2inv))
    mv = lambda M, v: [sum(M[i][j] * v[j] for j in range(m)) % Q for i in range(m)]  # noqa: E731
    D1 = mv(E2, D)
    H1 = mv(E1i, H)
    for i, j in edge.pivots:
        H1[i] = (H1[i] + D1[j]) % Q
    return mv(E1, H1), mv(E2i, D1)


def _apply_perm(arr, perm):
    out = [0] * len(arr)
    for i, p in enumerate(perm):
        out[p] = arr[i]
    return out


def _edge_perm_bit(edge, m: int, Q: int, mode: str) -> list[int]:
    if mode == "dense":
        return shear_permutation(specialize_matrix(edge.A, Q), m, Q)
    perm = []
    for idx in range(Q ** (2 * m)):
        d = _digits(idx, 2 * m, Q)
        H2, D2 = shear_via_factors(edge, d[:m], d[m:], Q)
        perm.append(_index(list(H2) + list(D2), Q))
    return perm


def run_bit(c: CompiledNetwork, inputs, b: int = 1, mode: str = "dense"):
    """Execute a bit network on physical arrays ``inputs[w]`` (lists of payload ints over Omega, |Omega| = Q^(2m),
    Q = q^b); returns the physical output array of every role (at its sink)."""
    m, Q = c.m, c.q ** b
    arrs = [list(a) for a in inputs]
    cur = [SOURCE] * c.W
    cache: dict = {}

    def move(w, v):
        e = c.edge(w, cur[w], v)
        if e.rank:
            key = (w, e.tail, e.head)
            if key not in cache:
                cache[key] = _edge_perm_bit(e, m, Q, mode)
            arrs[w] = _apply_perm(arrs[w], cache[key])
        cur[w] = v

    for g, gate in enumerate(c.gates):
        for w in gate.roles:
            move(w, g)
        old = [arrs[w] for w in gate.roles]
        for k, w in enumerate(gate.roles):
            row = gate.matrix[k]
            new = [0] * len(old[0])
            for l, a in enumerate(old):
                if row[l] & 1:
                    new = [x ^ y for x, y in zip(new, a)]
            arrs[w] = new
    for w in range(c.W):
        move(w, c.SINK)
    return arrs


def bit_frame_invariant_outputs(c: CompiledNetwork, inputs, b: int = 1):
    """D_out S_Omega D_in^{-1} computed directly: logical g_w = Phi_{-M_source(w)} f_w, routed to rho(w), then
    Phi_{M_sink(rho(w))} (equation (5) with Phi frames)."""
    m, Q = c.m, c.q ** b
    out = [None] * c.W
    for w in range(c.W):
        o = c.route[w]
        g = _apply_perm(inputs[w], shear_permutation(specialize_matrix(neg(c.net.source[w]), Q), m, Q))
        out[o] = _apply_perm(g, shear_permutation(specialize_matrix(c.net.sink[o], Q), m, Q))
    return out


def bit_interface_outputs(c: CompiledNetwork, inputs, b: int = 1):
    """The promised result of a bit interface: output role rho(w) carries Phi_I f_w (H <- H + D) [Pr L1490-1497]."""
    m, Q = c.m, c.q ** b
    I = tuple(tuple(1 if i == j else 0 for j in range(m)) for i in range(m))
    perm = shear_permutation(I, m, Q)
    out = [None] * c.W
    for w in range(c.W):
        out[c.route[w]] = _apply_perm(inputs[w], perm)
    return out


# ----------------------------------------------------------------------------------------------- complex networks
def _column_slices(m: int, k: int, j: int):
    n = 1 << (m * k)
    mask = ((1 << m) - 1) << (m * j)
    for base in range(n):
        if not base & mask:
            yield base


def apply_column_dense(arr, op, m: int, k: int, j: int):
    """Apply a one-column 2^m x 2^m operator ``op`` to column j of a k-column array."""
    out = list(arr)
    sh = m * j
    n1 = 1 << m
    for base in _column_slices(m, k, j):
        vals = [arr[base | (x << sh)] for x in range(n1)]
        for a in range(n1):
            acc = ZERO
            for bb, cf in enumerate(op[a]):
                if not cf.is_zero() and not vals[bb].is_zero():
                    acc = acc + cf * vals[bb]
            out[base | (a << sh)] = acc
    return out


def apply_Cv(arr, v: int, sign: int, m: int, k: int):
    """(C_v^{sign})^{(x)k}: on every column, f -> a f + b X_v f (sign +1) or b f + a X_v f (sign -1) (R3)."""
    a, b = (A_COEF, B_COEF) if sign == 1 else (B_COEF, A_COEF)
    for j in range(k):
        sh = v << (m * j)
        arr = [a * arr[x] + b * arr[x ^ sh] for x in range(len(arr))]
    return arr


def apply_row_ops(arr, ops, m: int, k: int):
    """P_E for the row additions ``ops`` in order on every column: the value at x moves to E x (SPEC §4.3)."""
    n = len(arr)
    out = [ZERO] * n
    for x in range(n):
        y = 0
        for j in range(k):
            col = (x >> (m * j)) & ((1 << m) - 1)
            y |= f2.apply_row_ops_to_address(col, ops) << (m * j)
        out[y] = arr[x]
    return out


def apply_zmask(arr, mask: int, m: int, k: int):
    """Z on the coordinates of ``mask`` in every column: multiply by (-1)^{sum_j wt(mask & x^(j))}."""
    if not mask:
        return list(arr)
    full = sum(mask << (m * j) for j in range(k))
    return [-v if (x & full).bit_count() & 1 else v for x, v in enumerate(arr)]


def _apply_phase_edge(arr, e, Ut, Uh, m: int, k: int, mode: str, cache: dict):
    if not e.basis:
        return arr
    if mode == "dense":
        key = (Ut, Uh)
        if key not in cache:
            cache[key] = phase.matmul(phase.dense_C(Uh, m), phase.dense_C_inverse(Ut, m))
        for j in range(k):
            arr = apply_column_dense(arr, cache[key], m, k, j)
        return arr
    if mode == "factored":
        for v, s in zip(e.basis, e.eps):
            arr = apply_Cv(arr, v, s, m, k)
        return arr
    if mode == "coordinate":
        arr = apply_row_ops(arr, e.reduce_ops, m, k)                    # P_{M^{-1}}
        for h, s in enumerate(e.eps):
            arr = apply_Cv(arr, 1 << h, s, m, k)                         # C_{e_h}^{eps_h}
        return apply_row_ops(arr, tuple(reversed(e.reduce_ops)), m, k)   # P_M
    raise ValueError(mode)


def run_phase(c: CompiledNetwork, inputs, k: int = 1, mode: str = "dense"):
    """Execute a complex network on physical arrays ``inputs[w]`` (lists of ZI2 over (F2^m)^k) WITHOUT endpoint
    corrections; returns the physical output array of every role (at its sink)."""
    m = c.m
    arrs = [list(a) for a in inputs]
    cur = [SOURCE] * c.W
    cache: dict = {}

    def move(w, v):
        e = c.edge(w, cur[w], v)
        arrs[w] = _apply_phase_edge(arrs[w], e, c.frame(w, cur[w]), c.frame(w, v), m, k, mode, cache)
        cur[w] = v

    for g, gate in enumerate(c.gates):
        for w in gate.roles:
            move(w, g)
        old = [arrs[w] for w in gate.roles]
        n = len(old[0])
        for kk, w in enumerate(gate.roles):
            row = [ZI2.of(x) for x in gate.matrix[kk]]
            new = [ZERO] * n
            for l, a in enumerate(old):
                if not row[l].is_zero():
                    new = [x + row[l] * y for x, y in zip(new, a)]
            arrs[w] = new
    for w in range(c.W):
        move(w, c.SINK)
    return arrs


def corrected_phase(c: CompiledNetwork, inputs, k: int = 1, mode: str = "dense"):
    """Pre Z-masks at the inputs, the network, post Z-masks and i^(post_ipow * k) at the outputs, the route sign
    undone once per role, and the exchange undone: returns the array that ends up in each INPUT role's place
    (SPEC §2.3 endpoint corrections; §4.5 lines after the network)."""
    m, W = c.m, c.W
    pre = c.pre_zmask or (None,) * W
    post = c.post_zmask or (None,) * W
    ipow = c.post_ipow or (0,) * W
    phys = [apply_zmask(inputs[w], zmask_int(pre[w]), m, k) for w in range(W)]
    outs = run_phase(c, phys, k, mode)
    res = [None] * W
    for w in range(W):
        o = c.route[w]
        a = apply_zmask(outs[o], zmask_int(post[o]), m, k)
        z = i_pow(ipow[o] * k) * c.route_sign[w]
        res[w] = [z * v for v in a]
    return res


def phase_frame_invariant_outputs(c: CompiledNetwork, inputs, k: int = 1):
    """D_out S_Omega D_in^{-1} directly: output rho(w) = eps_w (C_sink(rho(w)) C_source(w)^{-1})^{(x)k} f_w (5)."""
    m = c.m
    out = [None] * c.W
    for w in range(c.W):
        o = c.route[w]
        op = phase.matmul(phase.dense_C(c.net.sink[o], m), phase.dense_C_inverse(c.net.source[w], m))
        a = list(inputs[w])
        for j in range(k):
            a = apply_column_dense(a, op, m, k, j)
        out[o] = [c.route_sign[w] * v for v in a]
    return out


def C_tensor_apply(arr, m: int, k: int):
    """(C^{(x)m})^{(x)k} arr: the forward kernel C on every one of the m*k coordinates."""
    for coord in range(m * k):
        sh = 1 << coord
        arr = [A_COEF * arr[x] + B_COEF * arr[x ^ sh] for x in range(len(arr))]
    return arr
