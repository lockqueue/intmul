"""M6 acceptance suite (SPEC §4.11; component shapes of SPEC §6.3): the FULL network engine -- complex
network C^{te}, Lemma 13 basis changes (make_engine, basis_change="lemma13"), Lemma 12 swaps through the bit
network -- against EXACT dense references: dense 2^m x 2^m Gaussian-dyadic operators of net/phase.py, a dense
re-implementation of the whole network operator, individual exact kernels, and the independent tensor H0
(hadamard_direct) followed by one Q_p.  Every comparison is exact equality of integers.

Sources: SPEC §4.3-§4.7, §4.11, §6.3; Pr (13)-(18), (25), L1799-1887 (Prop 8, phase edges), L1928-2165
(Lemma 13, basis changes), L2183-2595 (C^{te}, batching, Prop 14).

Not run (DEVIATIONS D11): e = 27 / D = 27 (2^27 records), and Prop 14 at D = 9, K = 2 (hours in Python). The
stand-in for the latter is test_lemma13_bit_network_swaps_inside_the_engine (C^{t6} at K = 2: Lemma 13 slots of
L = f K = 4 bits, so its swaps are Lemma 12 calls through the bit network B1) plus the phase edges on L = 4 slots.
"""

import random
from collections import Counter
from dataclasses import replace

import pytest

import path_model as PM
from subnlogn.instrument import COMPONENTS, Instrument
from subnlogn.m6.cnet import CCtx, _phase_edge, c_power_exact, c_single
from subnlogn.m6.engine import compiled_fixture, make_engine
from subnlogn.m6.policy import LAYER_TEST, LayerPolicy, compiled_delta
from subnlogn.m6.prop14 import hadamard_direct, simultaneous_H0, simultaneous_H0_base
from subnlogn.net.phase import dense_C, dense_C_inverse, dense_Cv, dense_identity, matmul
from subnlogn.net.zi2 import ZI2

_CACHE: dict = {}
NETS = {name: compiled_fixture(name, _CACHE) for name in ("C1", "C2")}
B1 = compiled_fixture("B1", _CACHE)


def engine(net, d=2, policy=LAYER_TEST, inst=None):
    """The faithful engine: every P_M row addition is one Lemma 13 call, its swaps Lemma 12 on B1."""
    return make_engine(net, d, policy, net_bit=B1, inst=inst)


def rand_recs(rng, n, r, lim, shift=0):
    return [([rng.randint(-lim, lim) << shift for _ in range(r)], [rng.randint(-lim, lim) << shift for _ in range(r)])
            for _ in range(n)]


# ------------------------------------------------------------------------------------ dense references
def int_matrix(D):
    """A dense ZI2 matrix as (k, rows of (re, im) ints) with D = num / 2^k (exact, common denominator)."""
    k = max(z.k for row in D for z in row)
    return k, [[(z.re << (k - z.k), z.im << (k - z.k)) for z in row] for row in D]


def _exact_shift(v: int, k: int) -> int:
    if v & ((1 << k) - 1):
        raise AssertionError("dense reference left the Gaussian integers: guard too small")
    return v >> k


def apply_dense_columns(arr, D, slots, f):
    """The f-th tensor power of the 2^m x 2^m matrix D on the f columns of the slots (column j = the bits
    slots[0][j], ..., slots[m-1][j]; dense coordinate h <-> slot h), every other address bit fixed; exact."""
    m = len(slots)
    k, num = int_matrix(D)
    out = list(arr)
    for j in range(f):
        bits = [slots[h][j] for h in range(m)]
        mask = sum(1 << b for b in bits)
        offs = [sum(1 << bits[h] for h in range(m) if (a >> h) & 1) for a in range(1 << m)]
        new = list(out)
        for x in range(len(out)):
            if x & mask:
                continue
            vals = [out[x | o] for o in offs]
            r = len(vals[0][0])
            for a in range(1 << m):
                re, im = [0] * r, [0] * r
                for b, (dr, di) in enumerate(num[a]):
                    if dr or di:
                        vr, vi = vals[b]
                        for c in range(r):
                            re[c] += dr * vr[c] - di * vi[c]
                            im[c] += dr * vi[c] + di * vr[c]
                new[x | offs[a]] = ([_exact_shift(v, k) for v in re], [_exact_shift(v, k) for v in im])
        out = new
    return out


def dense_edge(net, e):
    """C_V C_U^{-1} of the phase edge e (U = frame at the tail, V = frame at the head), dense (SPEC §4.4)."""
    return matmul(dense_C(net.frame(e.role, e.head), net.m), dense_C_inverse(net.frame(e.role, e.tail), net.m))


def _zmask_records(recs, bits):
    return [([-v for v in re], [-v for v in im]) if sum((x >> b) & 1 for b in bits) & 1 else (re, im)
            for x, (re, im) in enumerate(recs)]


def _ipow(rec, k):
    re, im = rec
    for _ in range(k % 4):
        re, im = [-v for v in im], list(re)
    return re, im


def network_dense(arr, rows, nb, sel, net, ipow_times=1):
    """Dense re-implementation of the whole network operator of c_power_exact on e = m f selected bits:
    endpoint Z masks, every phase edge as the dense C_V C_U^{-1} on f columns (no P_M, no Lemma 13), the gate
    matrices in exact ZI2 arithmetic, post masks, the post i-power (applied ``ipow_times`` times; 1 is the
    network's rule: once per role), route signs and routing (SPEC §2.1, §4.5)."""
    m, W = net.m, net.W
    f = len(sel) // m
    slots = [sel[h * f:(h + 1) * f] for h in range(m)]
    A, g_rows = 1 << nb, rows // W
    roles = [[arr[(W * g + w) * A + a] for g in range(g_rows) for a in range(A)] for w in range(W)]
    if net.pre_zmask is not None:
        for w in range(W):
            roles[w] = _zmask_records(roles[w], [b for h in net.pre_zmask[w] for b in slots[h]])
    vertex = [-1] * W
    for gidx, gate in enumerate(net.gates):
        for w in gate.roles:
            D = matmul(dense_C(net.frame(w, gidx), m), dense_C_inverse(net.frame(w, vertex[w]), m))
            roles[w] = apply_dense_columns(roles[w], D, slots, f)
            vertex[w] = gidx
        rs = gate.roles
        saved = [roles[w] for w in rs]
        for kk, w in enumerate(rs):
            new = []
            for i in range(len(saved[0])):
                r = len(saved[0][i][0])
                acc = [ZI2(0)] * r
                for l, z in enumerate(gate.matrix[kk]):
                    if not z.is_zero():
                        acc = [a + z * ZI2(saved[l][i][0][c], saved[l][i][1][c]) for c, a in enumerate(acc)]
                assert all(a.k == 0 for a in acc)
                new.append(([a.re for a in acc], [a.im for a in acc]))
            roles[w] = new
    for w in range(W):
        D = matmul(dense_C(net.frame(w, net.SINK), m), dense_C_inverse(net.frame(w, vertex[w]), m))
        roles[w] = apply_dense_columns(roles[w], D, slots, f)
    for o in range(W):
        if net.post_zmask is not None and net.post_zmask[o]:
            roles[o] = _zmask_records(roles[o], [b for h in net.post_zmask[o] for b in slots[h]])
        if net.post_ipow is not None and net.post_ipow[o]:
            roles[o] = [_ipow(rec, ipow_times * net.post_ipow[o] * f) for rec in roles[o]]
    for w in range(W):
        if net.route_sign[w] == -1:
            o = net.route[w]
            roles[o] = [([-v for v in re], [-v for v in im]) for re, im in roles[o]]
    out = [None] * len(arr)
    for w in range(W):
        src = roles[net.route[w]]
        for g in range(g_rows):
            for a in range(A):
                out[(W * g + w) * A + a] = src[g * A + a]
    return out


def kernels(arr, sel):
    out = list(arr)
    for b in sel:
        c_single(out, b)
    return out


# ------------------------------------------------------------------------------------ 1. phase edges
LAYOUTS = [  # (f, K, rho, nb, rows, slots in physical order (MSB first)); spectator bits around and inside
    (1, 1, 0, 6, 2, [[4], [2], [0]]),
    (1, 1, 0, 5, 3, [[3], [2], [0]]),
    (1, 2, 1, 7, 2, [[6], [4], [2]]),
    (2, 1, 0, 9, 2, [[7, 6], [4, 3], [1, 0]]),
    (3, 1, 0, 10, 3, [[9, 8, 7], [5, 4, 3], [2, 1, 0]]),     # kernels C^{t3} on a slot run the network
    (2, 2, 1, 12, 1, [[11, 9], [7, 5], [3, 1]]),             # L = f K = 4: Lemma 12 through the bit network
]


def _phase_cases():
    """(name, layout, mode): "direct" = address-permutation oracle (row_add None); "lemma13" = make_engine with
    the bit network B1 (Lemma 12 swaps once L = f K >= 4: slow); "lemma13_bitwise" = make_engine without a bit
    network (Lemma 13 with bitwise swaps, the fast stand-in for the L = 4 layout)."""
    out = []
    for name in ("C1", "C2"):
        for lay in LAYOUTS:
            big = lay[0] * lay[1] >= 4
            tag = f"{name}-f{lay[0]}K{lay[1]}rho{lay[2]}nb{lay[3]}"
            out.append(pytest.param(name, lay, "direct", id=tag + "-direct"))
            out.append(pytest.param(name, lay, "lemma13", id=tag + "-lemma13",
                                    marks=[pytest.mark.slow] if big else []))
            if big:
                out.append(pytest.param(name, lay, "lemma13_bitwise", id=tag + "-lemma13_bitwise"))
    return out


PATH_ZERO = ("m6.row_add.direct", "m6.row_add.lemma13", "lemma13.call", "lemma13.swap", "lemma13.rotation",
             "interchange.lemma12_network_call", "m6.c_power.network")


@pytest.mark.parametrize("name,layout,mode", _phase_cases())
def test_phase_edges_against_dense(name, layout, mode):
    """Every compiled phase edge with a nonzero basis: _phase_edge (P_{M^-1}, kernels C^{eps}, P_M; the row
    additions as address permutations or as Lemma 13 calls) equals the dense C_V C_U^{-1}, coordinatewise on f
    columns (its f-th tensor power), exactly; includes inverse kernels (eps = -1) with odd and even f
    (SPEC §4.4; Pr L1799-1852, L2152-2165)."""
    net = NETS[name]
    f, K, rho, nb, rows, slots = layout
    rng = random.Random(f"{name}/{f}/{K}/{rho}/{nb}")                 # str seeds are process-independent
    inst = Instrument()
    if mode == "direct":
        ctx = CCtx(net=net, d=2, inst=inst)
    else:
        ctx = make_engine(net, 2, LAYER_TEST, net_bit=B1 if mode == "lemma13" else None, inst=inst)
    ctx = replace(ctx, K=K, rho=rho, nb=nb)
    edges = [e for e in net.all_edges if e.basis]
    assert any(-1 in e.eps for e in edges) and any(e.reduce_ops for e in edges)
    for e in edges:
        D = dense_edge(net, e)
        prop8 = dense_identity(net.m)
        for v, s in zip(e.basis, e.eps):
            prop8 = matmul(prop8, dense_Cv(v, net.m, s))
        assert D == prop8                                           # Prop 8 on the reference itself
        arr = rand_recs(rng, rows << nb, 2 if nb < 12 else 1, 1 << 12, 4 * net.m * f + 8)
        got = _phase_edge(list(arr), rows, e, slots, f, ctx)
        assert got == apply_dense_columns(arr, D, slots, f), (name, e.role, e.tail, e.head)
    c = inst.counts
    nk = sum(len(e.basis) for e in edges) if f == net.m else 0      # f = m: each kernel is one network call
    assert c.get("m6.c_power.network", 0) == nk
    assert c["m6.phase_edge.nonzero"] == len(edges) * (1 + nk)
    ops = sum(2 * len(e.reduce_ops) for e in edges) * (1 + nk)
    if mode == "direct":
        assert c["m6.row_add.direct"] == ops and c.get("lemma13.call", 0) == 0
    else:
        assert c["m6.row_add.lemma13"] == c["lemma13.call"] == ops
    # exact counts of everything else (exact count; path_model): inverse kernels, Lemma 13 exchanges and
    # rotations, repairs, Lemma 12 network calls (B1, u = f K) -- one closed form per phase edge
    eng = PM.Eng(net, 2, LAYER_TEST, K, B1 if mode == "lemma13" else None, "direct" if mode == "direct" else "lemma13")
    exp = sum((PM.phase_edge(eng, e, slots, f, rows, nb) for e in edges), Counter())
    PM.assert_exact(c, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["m6.phase_edge.inverse_kernel"] > 0
    assert (exp["interchange.lemma12_network_call"] > 0) == (mode == "lemma13" and f * K >= 4)


@pytest.mark.parametrize("rows_mult", [1, 2])
@pytest.mark.parametrize("f,K,rho,lo,extra", [(1, 1, 0, 1, 0), (2, 1, 0, 0, 1), (1, 2, 1, 0, 0)])
@pytest.mark.parametrize("name", ["C1", "C2"])
def test_network_operator_dense_reference(name, f, K, rho, lo, extra, rows_mult):
    """c_power_exact through the network with the Lemma 13 engine equals the dense re-implementation of the
    whole network operator (endpoint masks, post i-power applied ONCE per role with exponent post_ipow * f,
    route signs, routing) and the individual kernels I (x) C^{te}; applying the i-power zero or two times
    gives a different operator on C1 (SPEC §4.5; Pr L1853-1887, L2213-2285)."""
    net = NETS[name]
    m, W = net.m, net.W
    e = m * f
    nb = lo + e * K + extra
    sel = [lo + rho + i * K for i in range(e)][::-1]
    rows = W * rows_mult
    rng = random.Random(e * 31 + nb + rows)
    arr = rand_recs(rng, rows << nb, 1, 1 << 10, compiled_delta(net, e, 2, K, LAYER_TEST) + 8)
    inst = Instrument()
    got = list(arr)
    c_power_exact(got, rows, sel, replace(engine(net, inst=inst), K=K, rho=rho, nb=nb))
    assert got == network_dense(arr, rows, nb, sel, net)
    assert got == kernels(arr, sel)
    c = inst.counts
    assert c["m6.c_power.network"] == 1 and c["m6.gate"] == len(net.gates)
    if name == "C1":
        assert c["m6.ipow.post"] == 1 and c["m6.zmask.pre"] == 1 and c["m6.zmask.post"] == 1
        assert c["m6.route_sign"] == 1
        assert network_dense(arr, rows, nb, sel, net, ipow_times=0) != got
        assert network_dense(arr, rows, nb, sel, net, ipow_times=2) != got


# ------------------------------------------------------------------------------------ 2. C^{te}
@pytest.mark.parametrize("e,K,rho,lo,extra,rows,name", [
    (3, 1, 0, 1, 1, 3, "C1"), (3, 1, 0, 1, 1, 6, "C2"), (3, 2, 0, 1, 0, 3, "C1"), (3, 2, 1, 0, 1, 3, "C2"),
    (6, 1, 0, 0, 1, 3, "C1"), (9, 1, 0, 1, 0, 9, "C1")])
def test_c_power_against_individual_kernels(e, K, rho, lo, extra, rows, name):
    """C^{te} for e = 3, 9 (K = 1) and e = 3 (K = 2), plus e = 6 (two-chunk slots, so Lemma 13 runs its
    rotations and repair), through the Lemma 13 engine, against e individual exact kernels, with random
    NONZERO data in every row including the scratch roles' rows; e = 9 needs rows divisible by W^2 for its
    network children (SPEC §4.5, §4.6; Pr L2213-2285).  e = 27 (2^27 records) is not run (DEVIATIONS)."""
    net = NETS[name]
    nb = lo + e * K + extra
    sel = [lo + rho + i * K for i in range(e)][::-1]
    rng = random.Random(e * 100 + K * 10 + rho + rows)
    arr = rand_recs(rng, rows << nb, 1, 1 << 10, compiled_delta(net, e, 2, K, LAYER_TEST) + 8)
    assert all(any(re) or any(im) for re, im in arr[(rows - 1) << nb:])     # the last rows are nonzero too
    inst = Instrument()
    got = list(arr)
    c_power_exact(got, rows, sel, replace(engine(net, inst=inst), K=K, rho=rho, nb=nb))
    assert got == kernels(arr, sel)
    c = inst.counts
    assert c["m6.c_power.network"] == (1 + net.s if e == 9 else 1)
    # exact counts (exact count; path_model): Lemma 13 calls, exchanges, rotations, repairs (every record of
    # the role array is exceptional for K <= 5), Lemma 12 network calls, phase edges, gates, leaves
    exp = PM.c_power(PM.Eng(net, 2, LAYER_TEST, K, B1), sel, rows, nb)
    PM.assert_exact(c, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["lemma13.call"] > 0 and (exp["lemma13.rotation"] > 0) == (e > net.m)   # f >= 2: rotations


# ------------------------------------------------------------------------------------ 3. Prop 14
def prop14_case(D, K, rho, r, pre, suf, policy=LAYER_TEST, name="C1", p=12, seed=0, inst=None):
    net = NETS[name]
    n = pre + D * K + suf
    rng = random.Random(seed)
    recs = rand_recs(rng, 1 << n, r, (1 << p) * 7 // 10)
    sel = [suf + rho + i * K for i in range(D)][::-1]
    inst = Instrument() if inst is None else inst
    got = simultaneous_H0(recs, sel, p, p, engine(net, d=max(2, D), policy=policy, inst=inst), K=K, rho=rho)
    ref = hadamard_direct(recs, sel, p, p)
    assert got == ref                                                # independent tensor H0, one Q_p
    assert got == simultaneous_H0_base(recs, sel, p, p)
    return inst


@pytest.mark.parametrize("bad_set", ["eq23", "safe_segments"])
@pytest.mark.parametrize("D,K,r", [(3, 1, 1), (3, 1, 2), (3, 2, 1), (3, 2, 2)])
def test_prop14_D3_all_offsets(D, K, r, bad_set):
    """Prop 14 standalone (SPEC §6.3 component shapes) through simultaneous_H0 with the Lemma 13 engine:
    bit-exact against hadamard_direct + one Q_p and against the base case; every rho < K, prefix and
    suffix bits present, both exceptional-set modes (SPEC §4.7, §4.11; Pr L2440-2595)."""
    pol = replace(LAYER_TEST, bad_set=bad_set)
    for rho in range(K):
        inst = prop14_case(D, K, rho, r, 1, 2, policy=pol, seed=100 * D + 10 * K + rho + r)
        exp = PM.prop14_layer(PM.Eng(NETS["C1"], max(2, D), pol, K, B1), D, 1 + D * K + 2)   # exact
        PM.assert_exact(inst.counts, exp, sorted(set(exp) | set(PATH_ZERO)))
        assert exp["m6.layer.network"] == exp["m6.c_power.network"] == 1 and exp["m6.rows.padded"] > 0


def test_prop14_D9_K1():
    """D = 9, K = 1 (2^11 records with prefix and suffix): two network levels, Lemma 13 slots of f = 3
    chunks (L = 3: bitwise swaps, rotations, repair) inside the top node."""
    inst = prop14_case(9, 1, 0, 1, 1, 1, seed=9)
    exp = PM.prop14_layer(PM.Eng(NETS["C1"], 9, LAYER_TEST, 1, B1), 9, 11)      # exact counts
    PM.assert_exact(inst.counts, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["m6.c_power.network"] == 1 + NETS["C1"].s and exp["lemma13.rotation"] > 0


# ------------------------------------------------------------------------------------ 4. policies
def test_theorem_batching_forced_q0_through_lemma13():
    """Theorem batching with forced_q0 = 4 (Dev-11) at D = d = 13 (2^13 records, r = 1) through the full
    Lemma 13 engine: four chunks preprocessed and joined into 16 rows padded to 18 (W^2), one 9-piece over two
    network levels; equals the base case; padded rows added and removed (SPEC §4.6, §4.10)."""
    pol = LayerPolicy(mode="test", leaf="count", guard="compiled", forced_q0=4)
    D, p = 13, 12
    rng = random.Random(13)
    recs = rand_recs(rng, 1 << D, 1, (1 << p) * 7 // 10)
    sel = list(range(D))[::-1]
    inst = Instrument()
    got = simultaneous_H0(recs, sel, p, p, engine(NETS["C1"], d=13, policy=pol, inst=inst))
    assert got == simultaneous_H0_base(recs, sel, p, p)
    c = inst.counts
    assert c["m6.rows.padded"] == c["m6.rows.removed"] == (18 - 16) * (1 << 9)
    exp = PM.prop14_layer(PM.Eng(NETS["C1"], 13, pol, 1, B1), D, D)             # exact counts
    PM.assert_exact(c, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["m6.batch.preprocessed_chunks"] == 4 and exp["lemma13.call"] > 0


# ------------------------------------------------------------------------------------ 5. coverage
M6_COMPONENTS = sorted(k for k in COMPONENTS if k.startswith(("m6.", "lemma13.")))


def coverage_runs(inst):
    """A small union of engine runs that together reach every M6 / Lemma 13 component."""
    prop14_case(3, 1, 0, 1, 1, 1, inst=inst, seed=1)                         # layer, padding, removal
    net = NETS["C1"]
    e, K, nb = 6, 1, 7
    sel = list(range(e))[::-1]
    rng = random.Random(6)
    arr = rand_recs(rng, 3 << nb, 1, 1 << 8, compiled_delta(net, e, 2, K, LAYER_TEST) + 8)
    got = list(arr)
    c_power_exact(got, 3, sel, replace(engine(net, inst=inst), K=K, rho=0, nb=nb))
    assert got == kernels(arr, sel)
    got = list(arr)                                  # Dev-5 bad set: a non-total B (lemma13.repair_partial)
    pol = replace(LAYER_TEST, bad_set="safe_segments")
    c_power_exact(got, 3, sel, replace(engine(net, policy=pol, inst=inst), K=K, rho=0, nb=nb))
    assert got == kernels(arr, sel)


def test_coverage_of_m6_components():
    """Every registered M6 / Lemma 13 component (prefixes "m6.", "lemma13.") is reached (SPEC §4.11 last
    bullet); interchange.lemma12_network_call is covered by the slow suite."""
    inst = Instrument()
    coverage_runs(inst)
    missing = [k for k in M6_COMPONENTS if inst.counts.get(k, 0) <= 0]
    assert not missing, missing


# ------------------------------------------------------------------------------------ slow part
@pytest.mark.slow
def test_lemma13_bit_network_swaps_inside_the_engine():
    """Lemma 13 slots of L = f K = 4 bits (e = 6, f = 2, K = 2) make its swaps run Lemma 12 through the
    bit network B1 (u = 4); the network C^{te} still equals the individual kernels.  This is the feasible
    stand-in for Prop 14 at D = 9, K = 2, whose top node would run ~60 Lemma 13 calls on role arrays of
    3 * 2^18 records (hours in the RAM backend)."""
    net = NETS["C1"]
    e, K, rho, nb, rows = 6, 2, 1, 12, 3
    sel = [rho + i * K for i in range(e)][::-1]
    rng = random.Random(62)
    arr = rand_recs(rng, rows << nb, 1, 1 << 8, compiled_delta(net, e, 2, K, LAYER_TEST) + 8)
    inst = Instrument()
    got = list(arr)
    c_power_exact(got, rows, sel, replace(engine(net, inst=inst), K=K, rho=rho, nb=nb))
    assert got == kernels(arr, sel)
    c = inst.counts
    assert c["interchange.lemma12_network_call"] == c["lemma13.swap"]
    exp = PM.c_power(PM.Eng(net, 2, LAYER_TEST, K, B1), sel, rows, nb)             # exact counts
    PM.assert_exact(c, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["interchange.lemma12_network_call"] > 0 and exp["lemma13.call"] > 0


@pytest.mark.slow
def test_coverage_including_bit_network():
    """The coverage union of the fast part plus one phase edge on L = f K = 4 slots (C1, the nonzero edge with
    the fewest row additions): every M6 / Lemma 13 component and interchange.lemma12_network_call (Lemma 12
    through the bit network inside Lemma 13) are reached (SPEC §4.11 last bullet)."""
    inst = Instrument()
    coverage_runs(inst)
    net = NETS["C1"]
    f, K, rho, nb, rows, slots = LAYOUTS[-1]
    assert f * K >= 4
    e = min((x for x in net.all_edges if x.reduce_ops), key=lambda x: len(x.reduce_ops))
    rng = random.Random(64)
    arr = rand_recs(rng, rows << nb, 1, 1 << 12, 4 * net.m * f + 8)
    ctx = replace(engine(net, inst=inst), K=K, rho=rho, nb=nb)
    assert _phase_edge(list(arr), rows, e, slots, f, ctx) == apply_dense_columns(arr, dense_edge(net, e), slots, f)
    missing = [k for k in M6_COMPONENTS + ["interchange.lemma12_network_call"] if inst.counts.get(k, 0) <= 0]
    assert not missing, missing


@pytest.mark.slow
@pytest.mark.parametrize("name,r", [("C2", 1), ("C1", 2)])
def test_prop14_D9_K1_more(name, r):
    """Prop 14 at D = 9, K = 1 on the other fixture and with r = 2 coefficients per record (SPEC §6.3)."""
    c = prop14_case(9, 1, 0, r, 1, 1, name=name, seed=90 + r).counts
    exp = PM.prop14_layer(PM.Eng(NETS[name], 9, LAYER_TEST, 1, B1), 9, 11)       # exact counts
    PM.assert_exact(c, exp, sorted(set(exp) | set(PATH_ZERO)))
    assert exp["m6.c_power.network"] == 1 + NETS[name].s and exp["lemma13.rotation"] > 0


@pytest.mark.slow
def test_c_power_e9_C2():
    """C^{t9} (two network levels) on fixture C2 against the individual kernels (SPEC §4.11)."""
    net = NETS["C2"]
    e, K, nb, rows = 9, 1, 9, 9
    sel = list(range(e))[::-1]
    rng = random.Random(99)
    arr = rand_recs(rng, rows << nb, 1, 1 << 8, compiled_delta(net, e, 2, K, LAYER_TEST) + 8)
    got = list(arr)
    c_power_exact(got, rows, sel, replace(engine(net), K=K, rho=0, nb=nb))
    assert got == kernels(arr, sel)
