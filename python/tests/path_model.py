"""Independent expected path counts for the exact path assertions.

Every count is derived from the schedule, the geometry and the network DEFINITIONS by a closed form or a short
recurrence transcribed from the specification -- never from the engine's own counters.  The inputs are plain
parameters (operand bit lengths, (K, d), chunk widths, the compiled fixture's edges with their ``reduce_ops`` and
residual bases, its m, W, s, q), so a silent partial fallback (one layer, middle call, row addition or BasicMul
call taking a shortcut) changes the measured counters but not these numbers.

Transcribed rules: the listing's root parameters (MS L708-711, Dev-9); the balanced geometry (r2 Thm 3, SPEC
§7.1) and the bridge dimension clamp; the bridge's movements (SPEC §7.2); Lemma 16's layout and
chunk rounds (SPEC §5.2-§5.3); Prop 18 (SPEC §5.7); the Prop 14 layer and the C^{te} recursion (SPEC §4.4-§4.7,
v1.1 §4.0); Lemma 13 (SPEC §4.1-§4.3); Lemma 12 / Prop 11 (SPEC §3.6-§3.8, Dev-6); the Walsh middle
(SPEC_WALSH §4-§5); BasicMul (SPEC §6.5, MS Lemma 6.5).  Counter names are the engine's ("m6." prefix for the
network engine's mirrored counters; :func:`unprefixed` converts for a bare ``CCtx.counts``).
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

__all__ = ["PATH_KEYS", "BASIC_ZERO_KEYS", "nets", "bit_lengths", "assert_exact", "unprefixed", "root_K0",
           "balanced", "bridge_dim", "l12_calls", "l12_counts", "q_chunk_calls", "prop11_nodes", "Eng",
           "lemma13_row_add", "phase_edge", "c_power", "prop14_layer", "layout_exchanges", "bluestein_middle",
           "positional_map", "walsh_middle", "bridge_transform", "solver_word_calls", "fastdft_counts",
           "multiply_counts", "basic_mul_counts"]


def assert_exact(measured, expected, keys=None) -> None:
    """Assert measured == expected for every key of ``expected`` (or ``keys``; absent = 0); the message names
    the key (the must-fail mutant tests match on "exact path count")."""
    for k in (sorted(expected) if keys is None else keys):
        got, want = measured.get(k, 0), expected.get(k, 0)
        assert got == want, f"exact path count {k}: measured {got}, expected {want}"


def unprefixed(c: Counter) -> Counter:
    """The "m6.*" counters without the prefix (a bare ``CCtx.counts`` dict uses the short names)."""
    return Counter({k[3:]: v for k, v in c.items() if k.startswith("m6.")})


def _ceil_log(x: int, base: int) -> int:
    """Least j >= 0 with base**j >= x."""
    j, v = 0, 1
    while v < x:
        v *= base
        j += 1
    return j


def _prod(xs) -> int:
    out = 1
    for x in xs:
        out *= x
    return out


# ------------------------------------------------------------------------------------------ schedule, geometry
def root_K0(n: int, min_K: int = 0) -> int:
    """K0 of the two-call root (MS L708-711): b = max(4, floor(lg n)), N = ceil(n/b), K0 = bitlength(2N - 1);
    Dev-9 enlarges it to min_K."""
    b = max(4, n.bit_length() - 1)
    N = -(-n // b)
    return max((2 * N - 1).bit_length(), min_K)


def balanced(K: int, d: int) -> tuple[int, ...]:
    """Balanced axes (r2 Thm 3, SPEC §7.1): e = ceil(K/d), d e - K short axes 2^(e-1) first, then 2^e."""
    e = -(-K // d)
    n_short = d * e - K
    return (1 << (e - 1),) * n_short + (1 << e,) * (d - n_short)


def bridge_dim(sched, K: int):
    """Bridge dimension for R = 2^K under schedule.bridge_d: the largest d' <= min(d, K),
    d' >= 2, admissible for the middle (direct: any; Bluestein/Walsh: ell = ceil(K/d') >= 2 and
    1 <= chunk_bits <= ell - 1); None -> the 2D FastDFT."""
    for dd in range(min(sched.bridge_d, K), 1, -1):
        if sched.bridge_middle == "direct":
            return dd
        ell = -(-K // dd)
        if ell >= 2 and 1 <= sched.chunk_bits <= ell - 1:
            return dd
    return None


# ------------------------------------------------------------------------------------------ Lemma 12, Prop 11
def _l12_pieces(u: int, net, min_e: int, min_u: int) -> list[int]:
    """Levels j of the Prop 11 calls made by ONE Lemma 12 exchange of two binary chunks of u bits (SPEC §3.7-§3.8,
    Dev-6): bitwise if u < min_u; else e = ceil(log_q 2^u) radix-q digits, digitwise if e < min_e; else
    k = ceil(log_m e), rho = least with q^(2 rho) >= W^k, digitwise if rho >= e or rho = 0; else one Prop 11 call
    per base-m piece of e - rho (width m^j, a_j of each)."""
    if u == 0 or u < min_u:
        return []
    return _q_pieces(_ceil_log(1 << u, net.q), net, min_e)


def _q_pieces(e: int, net, min_e: int = 2) -> list[int]:
    """Levels of the Prop 11 calls of Lemma 12 for two radix-q chunks of e digits (SPEC §3.7; see above)."""
    q, m, W = net.q, net.m, net.W
    if e == 0 or e < min_e:
        return []
    k = _ceil_log(e, m)
    rho = 0
    while q ** (2 * rho) < W ** k:
        rho += 1
    if rho >= e or rho == 0:
        return []
    return [j for j in range(k, -1, -1) for _ in range(((e - rho) // m ** j) % m)]


def l12_calls(u: int, net, min_e: int = 2, min_u: int = 1) -> int:
    """"interchange.lemma12_network_call" of one Lemma 12 exchange of u-bit chunks: its Prop 11 calls with j >= 1."""
    return sum(1 for j in _l12_pieces(u, net, min_e, min_u) if j)


def l12_counts(u: int, net, min_e: int = 2, min_u: int = 1) -> Counter:
    """Interchange counters of ONE Lemma 12 exchange of u-bit chunks (SPEC §3.6-§3.8): its network calls (Prop 11
    calls with j >= 1), their Prop 11 nodes and child calls (s per node, asserted by the engine)."""
    nodes = prop11_nodes(u, net, min_e, min_u)
    return Counter({"interchange.lemma12_network_call": l12_calls(u, net, min_e, min_u),
                    "interchange.prop11_node": nodes, "interchange.child_call": net.s * nodes})


def _times(c: Counter, k: int) -> Counter:
    return Counter({key: k * v for key, v in c.items()})


def q_chunk_calls(e: int, net, min_e: int = 2) -> int:
    """"interchange.lemma12_network_call" of one swap_q_chunks on two radix-q chunks of e digits (SPEC §3.7)."""
    return sum(1 for j in _q_pieces(e, net, min_e) if j)


def prop11_nodes(u: int, net, min_e: int = 2, min_u: int = 1) -> int:
    """Prop 11 nodes (k >= 1) of one exchange: a level-k call has s children at level k - 1 (SPEC §3.6), so
    nodes(k) = 1 + s nodes(k - 1), nodes(0) = 0."""
    def nodes(k):
        return 0 if k == 0 else 1 + net.s * nodes(k - 1)
    return sum(nodes(j) for j in _l12_pieces(u, net, min_e, min_u))


# ------------------------------------------------------------------------------------------ the Prop 14 engine
@dataclass(frozen=True)
class Eng:
    """The engine parameters (SPEC v1.1 §4.0): complex network, dimension d, LayerPolicy, chunk width K, the
    basis-change mode ("lemma13" = one Lemma 13 call per row addition, its exchanges Lemma 12 on ``bitnet`` or
    bitwise if None; "direct" = the address-permutation oracle) and the Lemma 12 cutoffs."""

    net: object
    d: int
    pol: object
    K: int = 1
    bitnet: object = None
    row_add: str = "lemma13"
    min_e: int = 2
    min_u: int = 1


def lemma13_row_add(eng: Eng, slot_min: dict, dst: int, src: int, z: int, f: int, volume=None) -> Counter:
    """One row addition dst <- dst xor src (SPEC §4.3) = ONE Lemma 13 call, x = src, y = dst (SPEC §4.1-§4.2).
    For f > 1 the eight lines (20) each bring their target (y: lines 1, 3, 6, 8; z: lines 2, 4, 5, 7) to the
    physically rightmost of the three chunk fields by one exchange and undo it: 8 [y not rightmost] +
    8 [z not rightmost] exchanges, each one Lemma 12 call on L = f K bits; then the repair -- with (23) and
    K <= 5 EVERY address is exceptional ("Small K (settled)"): all ``volume`` records are banked, one sort, one
    reinsertion -- and the top XOR.  f = 1: the top XOR only.  ``slot_min`` = lowest address bit of each slot."""
    if eng.row_add == "direct":
        return Counter({"m6.row_add.direct": 1})
    c = Counter({"m6.row_add.lemma13": 1, "lemma13.call": 1, "lemma13.top_xor": 1})
    if f > 1:
        right = min((dst, src, z), key=lambda h: slot_min[h])
        swaps = 8 * (dst != right) + 8 * (z != right)
        c["lemma13.rotation"] += 8
        c["lemma13.swap"] += swaps
        if eng.bitnet is not None:
            c.update(_times(l12_counts(f * eng.K, eng.bitnet, eng.min_e, eng.min_u), swaps))
        if eng.pol.bad_set == "eq23" and eng.K <= 5:
            c["lemma13.sort"] += 1
            c["lemma13.reinsert"] += 1
            if volume is not None:
                c["lemma13.bad_records"] += volume
    return c


def phase_edge(eng: Eng, edge, slots: list, f: int, rows=None, nb=None) -> Counter:
    """One phase edge C_V C_U^-1 on f columns (SPEC §4.4): zero edges do nothing; a nonzero edge makes the
    |reduce_ops| row additions of P_{M^-1} and again of P_M (z = the first slot not in (dst, src)) and applies
    C^{tf} (eps = +1) or the inverse kernel (eps = -1) on its rank slots (Prop 8, (16))."""
    if not edge.basis:
        return Counter({"m6.phase_edge.zero": 1})
    m = len(slots)
    smin = {h: min(s) for h, s in enumerate(slots)}
    vol = None if rows is None or nb is None else rows << nb
    c = Counter({"m6.phase_edge.nonzero": 1})
    for dst, src in edge.reduce_ops:
        z = next(h for h in range(m) if h not in (dst, src))
        add = lemma13_row_add(eng, smin, dst, src, z, f, vol)
        for _ in range(2):
            c.update(add)
    for h, eps in enumerate(edge.eps):
        c.update(c_power(eng, slots[h], rows, nb))
        if eps != 1:
            c["m6.phase_edge.inverse_kernel"] += 1
    return c


def _is_leaf(e: int, d: int, pol) -> bool:
    """SPEC v1.1 §4.0 leaf rule: e = 1, or e <= C_leaf_e ("count"), or e^b < d^a for beta = a/b ("beta")."""
    if e == 1:
        return True
    if pol.leaf == "count":
        return e <= pol.C_leaf_e
    a, b = pol.beta.numerator, pol.beta.denominator
    return e ** b < d ** a


def c_power(eng: Eng, sel: list, rows=None, nb=None) -> Counter:
    """C^{te} on the selected bits ``sel`` (SPEC §4.5): a leaf (e individual kernels) if the leaf rule holds or
    m does not divide e; else a network node: every role is split off (rows / W rows each), every edge of every
    role (SOURCE -> its gates -> SINK, SPEC §2.1) is traversed once as a phase edge on f = e/m columns, every
    gate runs once."""
    net, e = eng.net, len(sel)
    if _is_leaf(e, eng.d, eng.pol) or e % net.m:
        return Counter({"m6.c_power.leaf": 1, "m6.c_single": e})
    c = Counter({"m6.c_power.network": 1, "m6.gate": len(net.gates)})
    f = e // net.m
    slots = [sel[h * f:(h + 1) * f] for h in range(net.m)]
    sub_rows = None if rows is None else rows // net.W
    for edge in net.all_edges:
        c.update(phase_edge(eng, edge, slots, f, sub_rows, nb))
    return c


def prop14_layer(eng: Eng, D: int, n=None) -> Counter:
    """One Prop 14 network layer on D selected chunks of an n-bit record address (SPEC §4.6-§4.7): the plan --
    theorem batching: q0 = ceil(lg W) ceil(log_m 2d) (Dev-11: forced_q0) leading chunks one kernel each, only
    individual kernels if D <= q0, k0 = ceil(log_m d) (Dev-11: the deepest piece); forced batching (Dev-4): q0 = 0,
    a unit row field, k0 = the deepest piece -- then C^{te} on each base-m piece of the D - q0 remaining chunks
    (most significant first) on the padded rows: 2^(q0 K) genuine rows per prefix padded to a multiple of W^k0,
    i.e. (row_pad - row_len) 2^(n - q0 K) zero records added and removed."""
    net, pol, K = eng.net, eng.pol, eng.K
    m, W = net.m, net.W
    c = Counter({"m6.layer.network": 1})
    if pol.batching == "theorem":
        q0 = _ceil_log(W, 2) * _ceil_log(2 * eng.d, m) if pol.forced_q0 is None else pol.forced_q0
        if D <= q0:
            c["m6.batch.individual"] += 1
            c["m6.c_single"] += D
            return c
    else:
        q0 = 0
    pieces, v, j = [], D - q0, 0
    while v:
        pieces = [m ** j] * (v % m) + pieces
        v //= m
        j += 1
    level = max((_ceil_log(p, m) for p in pieces), default=0)
    if pol.batching == "theorem" and pol.forced_q0 is None:
        level = _ceil_log(eng.d, m)
    row_len = 1 << (q0 * K) if pol.batching == "theorem" else 1
    row_pad = -(-row_len // W ** level) * W ** level
    c["m6.c_single"] += q0
    if q0:
        c["m6.batch.preprocessed_chunks"] += q0
    if row_pad != row_len and n is not None:
        c["m6.rows.padded"] += (row_pad - row_len) << (n - q0 * K)
        c["m6.rows.removed"] += (row_pad - row_len) << (n - q0 * K)
    rows = None if n is None else (row_pad << (n - D * K))   # prefixes x padded rows
    nb = None if n is None else (D - q0) * K                  # per-row address bits (suffix ignored: 2^lo folds in)
    pos = list(range(D - q0 - 1, -1, -1))
    for size in pieces:
        c.update(c_power(eng, [K * x for x in pos[:size]], rows, nb))
        pos = pos[size:]
    return c


# ------------------------------------------------------------------------------------------ Lemma 16, Bluestein
def layout_exchanges(D: int, ell: int, K: int) -> int:
    """Chunk exchanges of Lemma 16's layout L (SPEC §5.2): the q = floor((ell - 1)/K) chunks of each of the D
    record axes, physical order (1,1)..(1,q),(2,1)..(D,q), are rearranged to (1,1),(2,1)..(D,1),(1,2)..(D,q) by
    scanning the target positions left to right and exchanging whenever they differ."""
    q = (ell - 1) // K
    cur = [(i, j) for i in range(D) for j in range(q)]
    tgt = [(i, j) for j in range(q) for i in range(D)]
    n = 0
    for k in range(len(tgt) - 1):
        if cur[k] != tgt[k]:
            m = cur.index(tgt[k])
            cur[k], cur[m] = cur[m], cur[k]
            n += 1
    return n


def bluestein_middle(t, K: int, eng: Eng | None = None, movement: bool = True, bitnet=None,
                     min_e: int = 2, min_u: int = 1) -> Counter:
    """One Bluestein middle call (SPEC §5.7-§5.9): one chirp convolution = Prop 18 = forward(f), forward(g),
    opposite(z), i.e. 3 Lemma 16 procedures, each with q K chunk rounds (b <= h <= ell - 2; all D = d - 1 record
    axes participate since a_i >= ell - 1 > h) through Prop 14 (``eng`` = the network engine; None = the M3
    base case), and (``movement``) one executed layout L or L^-1 whose chunk exchanges are Lemma 12 calls on
    K-bit chunks of ``bitnet``; M = R/r Lemma 17 ring products."""
    d, ell = len(t), t[-1].bit_length() - 1
    rounds = 3 * ((ell - 1) // K) * K
    n = sum(ti.bit_length() - 1 for ti in t[:-1])
    R = _prod(t)
    c = Counter({"bluestein.tensor_dft": 1, "bluestein.complex_convolution": 1, "bridge.middle": 1,
                 "prop18.ring_product": _prod(t[:-1]),
                 # word products: 5 R truncated complex products (trunc_cmul, 4 each) -- the input and output chirps
                 # (SPEC §5.9) and the two twists and the untwist of the convolution (SPEC §5.8)
                 "word.call": 5 * 4 * R})
    if eng is not None:
        c["prop14.network_layer"] += rounds
        for k, v in prop14_layer(eng, d - 1, n).items():
            c[k] += rounds * v
    if movement:
        c["layout.executed"] += 3
        if bitnet is not None:
            c.update(_times(l12_counts(K, bitnet, min_e, min_u), 3 * layout_exchanges(d - 1, ell, K)))
    return c


# ------------------------------------------------------------------------------------------ Walsh middle
def _walsh_layout(widths, ell: int, h: int):
    """L and U = (LB)^-1 of SPEC_WALSH §4.4 (positions from the MSB; dest[p] = destination of the bit at p)."""
    original = [(i, v) for i, a in enumerate(widths) for v in range(a - 1, -1, -1)]
    old = {s: k for k, s in enumerate(original)}
    b, q = (ell - 1) % h, (ell - 1) // h
    prefix = [(i, ell - 1) for i, a in enumerate(widths) if a == ell]
    prefix += [(i, v) for v in range(b - 1, -1, -1) for i in range(len(widths))]
    rest = [(i, v) for j in range(q) for i in range(len(widths))
            for v in range(ell - 2 - j * h, ell - 2 - (j + 1) * h, -1)]
    new = {s: k for k, s in enumerate(prefix + rest)}
    L = [new[s] for s in original]
    B = [old[(i, widths[i] - 1 - v)] for (i, v) in original]
    LB = [L[x] for x in B]
    U = [0] * len(LB)
    for j, x in enumerate(LB):
        U[x] = j
    return L, U


def _two_involutions(dest):
    """dest = I1 o I0 with I0: i_j -> i_-j, I1: i_j -> i_(1-j) on every cycle (R5 §7.2; SPEC_WALSH §4.3)."""
    n = len(dest)
    I0, I1, seen = list(range(n)), list(range(n)), set()
    for s in range(n):
        if s in seen:
            continue
        cyc, x = [], s
        while x not in seen:
            seen.add(x)
            cyc.append(x)
            x = dest[x]
        for j, pos in enumerate(cyc):
            I0[pos], I1[pos] = cyc[(-j) % len(cyc)], cyc[(1 - j) % len(cyc)]
    return I0, I1


def positional_map(dest, h: int, d: int, eng: Eng | None = None) -> Counter:
    """One positional map (SPEC_WALSH §4.2-§4.3): unless the identity, two involutions x three CNOT stages; the
    pairs of a stage are grouped by the slice of their target (J = floor(m0/h) h-bit chunks from the MSB, groups
    of <= d chunks, one slice per (group, offset)); each nonempty slice group is one CNOT batch = two selective
    Walsh operations = 6 full Prop 14 layers on the slice's D chunks; leftover targets are elementary CNOTs."""
    m0 = len(dest)
    c = Counter({"walsh.positional_map": 1})
    if list(dest) == list(range(m0)):
        return c
    J = m0 // h
    slice_of, slice_D = {}, []
    for g in range(-(-J // d)):
        start, D = g * d * h, min(d, J - g * d)
        for rho in range(h):
            for j in range(D):
                slice_of[start + j * h + (h - 1 - rho)] = len(slice_D)
            slice_D.append(D)
    for inv in _two_involutions(dest):
        swaps = [(a, inv[a]) for a in range(m0) if a < inv[a]]
        for stage in ([(y, x) for x, y in swaps], swaps, [(y, x) for x, y in swaps]):
            groups: dict = {}
            for ctl, tgt in stage:
                groups.setdefault(slice_of.get(tgt), []).append(ctl)
            for sl, batch in groups.items():
                if sl is None:
                    c["walsh.leftover_cnot"] += len(batch)
                    continue
                c["walsh.slice_batch"] += 1
                c["walsh.gadget"] += 2
                c["walsh.exact_boundary"] += 6
                if eng is not None:
                    for k, v in prop14_layer(eng, slice_D[sl], m0).items():
                        c[k] += 6 * v
    return c


def walsh_middle(t, h: int, eng: Eng | None = None) -> Counter:
    """One Walsh middle call (SPEC_WALSH §5.1, §5.3): the positional maps L and U = (LB)^-1 (§4.4), and the
    record-axis rounds h0 = ell-1..0 with participating axes a_i > h0: chunk rounds b <= h0 <= ell - 2 (one
    Prop 14 layer on the d - 1 participating chunks), the others prefix rounds."""
    d, ell = len(t), t[-1].bit_length() - 1
    widths = [ti.bit_length() - 1 for ti in t[:-1]]
    m0, b = sum(widths), (ell - 1) % h
    L, U = _walsh_layout(widths, ell, h)
    R = _prod(t)
    # word products (_phase: 4 per coefficient): the last-axis FFT, one phase per butterfly (ell r/2 per record)
    c = Counter({"bridge.middle": 1, "word.call": 4 * ell * (R // 2)})
    c.update(positional_map(L, h, d, eng))
    c.update(positional_map(U, h, d, eng))
    for h0 in range(ell - 1, -1, -1):
        axes = [i for i, a in enumerate(widths) if h0 < a]
        if not axes:
            continue
        if b <= h0 <= ell - 2:
            c["walsh.chunk_round"] += 1
            if eng is not None:
                c.update(prop14_layer(eng, len(axes), m0))
        else:
            c["walsh.prefix_round"] += 1
        c["word.call"] += 4 * R                # one combined twiddle per record per round (R5 (7.8)): r coefficients
    return c


# ------------------------------------------------------------------------------------------ the bridge
def bridge_transform(K: int, d: int, middle: str, chunk_bits: int = 1, movement: bool = True,
                     eng: Eng | None = None, bitnet=None, min_e: int = 2, min_u: int = 1) -> Counter:
    """One bridge DFT of length 2^K in dimension d (SPEC §7.2; br_r2 §5): spreading S_d..S_2 (R/t_h lines, a
    filter of t_h taps since W = 2P + 1 > t_h: one block = 4 packed products per line), the middle, the
    storage -> frequency reversal, deconvolution.  Movements (``movement``): every spreading S_h exposes axis h
    by one Lemma 12 exchange with the innermost axis 1 and back; the direct middle does the same for its axis
    DFTs h = 2..d; the Bluestein/Walsh middles reverse storage <-> tensor order (d//2 exchanges each way); step 4
    reverses once more.  An exchange of axes a, b runs Lemma 12 on min(lg t_a, lg t_b) bits."""
    t = balanced(K, d)
    R = 1 << K
    a = [ti.bit_length() - 1 for ti in t]
    assert all(ti < 2 * 256 + 1 for ti in t), "model assumes W = 2P + 1 > t_h (one overlap-add block per line)"
    c = Counter({"bridge.dft": 1, "bridge.spread_axis": d - 1,
                 "kron.product": sum(4 * R // t[h - 1] for h in range(2, d + 1))})
    A = 1                                    # deconvolution B_h^-1, h = 2..d: R / A_h cycles of length A_h
    for h in range(2, d + 1):
        A *= t[h - 2]
        c["word.call"] += (R // A) * solver_word_calls(A)
    if middle == "bluestein":
        c.update(bluestein_middle(t, chunk_bits, eng, movement, bitnet, min_e, min_u))
    elif middle == "walsh":
        c.update(walsh_middle(t, chunk_bits, eng))
    else:                                    # direct middle: radix-2 FFT of every line of every axis, 4 per butterfly
        c["bridge.middle"] += 1
        c["word.call"] += sum(4 * (R // ti) * (ti // 2) * (ti.bit_length() - 1) for ti in t)
    if movement:
        direct = middle == "direct"
        c["bridge.axis_swap"] += 2 * (d - 1) + (2 * (d - 1) if direct else 2 * (d // 2)) + d // 2
        c["bridge.axis_expose"] += (d - 1) * (2 if direct else 1)
        c["bridge.axis_reverse"] += 1 if direct else 3
        if bitnet is not None:                                       # axis h <-> axis 1 (a_1 is the smallest)
            c.update(_times(l12_counts(a[0], bitnet, min_e, min_u), 2 * (d - 1) * (2 if direct else 1)))
            for k in range(d // 2):                                    # reversal pairs (k + 1, d - k)
                c.update(_times(l12_counts(a[k], bitnet, min_e, min_u), 1 if direct else 3))
    return c


# ------------------------------------------------------------------------------------------ word products
def solver_word_calls(L: int) -> int:
    """Word products (Ctx.word_mul calls) of one cyclic solve of length L (MS §5.2 CyclicSolve, drop-in r2 §8;
    solver.cyclic_solve, both cases): B_i = RM(mu, Y_i) for both components (2L), the prefix sweep (2(L - 1)), the
    closure RM(gamma, P) (2) and the second pass (2(L - 1)): 6L - 2."""
    return 6 * L - 2


# ------------------------------------------------------------------------------------------ the 2D FastDFT
def fastdft_counts(sched, R: int, p: int, depth: int = 0) -> Counter:
    """One 2D FastDFT of length R at precision p (MS listing, Lemma 6.5; eq. (cert-sched)): a leaf is one base
    radix-2 FFT (K R/2 butterflies); a node (t1 = 2^floor(K/2) rows of r = 2^ceil(K/2)) spreads every row with
    ceil(r / W~) overlap-add blocks of 4 packed products (W~ = min(2 p_child + 1, r), Thm 6.3) and recurses into
    t1 children of length r at p_child = p + 6K + 32.  The leaf rule is the schedule's (SPEC §6.3 test thresholds or
    R <= 4 p^2)."""
    K = R.bit_length() - 1
    leaf = R <= 2 or (sched.max_depth is not None and depth >= sched.max_depth) or \
        (R <= sched.base_threshold if sched.base_threshold is not None else
         (sched.leaf_quadratic and R <= 4 * p * p))
    if leaf:                      # word products: 4 per butterfly (W = RM(w, B), basefft index and tape variants)
        return Counter({"fastdft.leaf": 1, "basefft.butterfly": K * (R // 2), "word.call": 4 * K * (R // 2)})
    t1, r = 1 << (K // 2), 1 << ((K + 1) // 2)
    p_child = p + sched.child_K * K + sched.child_c
    Wt = min(2 * p_child + 1, r)
    c = Counter({"fastdft.node": 1, "spread.row": t1, "kron.product": 4 * t1 * (-(-r // Wt)),
                 # word products: pre- and post-twist, 4 per entry of the t1 x r array (synthetic.twist_rows), and
                 # one cyclic solve of length t1 per column (r of them, solver_word_calls)
                 "word.call": 2 * 4 * t1 * r + r * solver_word_calls(t1)})
    c.update(_times(fastdft_counts(sched, r, p_child, depth + 1), t1))
    return c


# ------------------------------------------------------------------------------------------ the multiplier
def multiply_counts(sched, ns, nets: dict | None = None) -> Counter:
    """Expected counters of one ``multiply(a, b, ctx)`` per entry n = max(bits(a), bits(b), 1) of ``ns`` under a
    forced-bridge schedule (SPEC §6.3; MS Thm 7.1): n <= mul_direct_bits -> the listing's direct product; else
    one two-call root of length 2^K0 = two transforms, each the bridge in dimension ``bridge_dim`` (clamped:
    "bridge.d_clamped") with the schedule's middle, Prop 14 engine and movements, or the 2D FastDFT when no
    dimension is admissible ("bridge.fallback_2d"); a schedule without bridge_d runs the faithful dispatcher's 2D
    fallback ("multiply.fallback_2d", SPEC §6.2) with Dev-9's root.  ``nets`` maps fixture
    names to compiled networks (the schedule's net_cx / net_bit); without them the m6 / Lemma 12 counters
    are not modelled."""
    nets = nets or {}
    bitnet = nets.get(sched.net_bit)
    eng = None
    if sched.prop14_layer == "network" and sched.net_cx in nets:
        eng = Eng(nets[sched.net_cx], 0, sched.layer, sched.chunk_bits, bitnet, "lemma13",
                  sched.lemma12_min_e, sched.lemma12_min_u)
    movement = sched.bridge_movement == "lemma12"
    c = Counter()
    for n in ns:
        if n <= sched.mul_direct_bits:
            c["multiply.direct"] += 1
            continue
        c["multiply.call"] += 1
        K0 = root_K0(n, sched.min_root_exponent)
        b = max(4, n.bit_length() - 1)
        p0 = 2 * b + 2 * K0 + 6                                # listing L712
        c["word.call"] += 3 << K0                              # the R0 pointwise squares: csquare, 3 products each
        if sched.bridge_d is None:                             # faithful dispatcher: no theorem shape (SPEC §6.2)
            c["multiply.fallback_2d"] += 2
            c.update(_times(fastdft_counts(sched, 1 << K0, p0), 2))
            continue
        dd = bridge_dim(sched, K0)
        for _ in range(2):
            if dd is None:
                c["bridge.fallback_2d"] += 1
                c.update(fastdft_counts(sched, 1 << K0, p0))
                continue
            if dd < sched.bridge_d:
                c["bridge.d_clamped"] += 1
            e = None if eng is None else Eng(eng.net, dd, eng.pol, eng.K, eng.bitnet, eng.row_add, eng.min_e,
                                             eng.min_u)
            c.update(bridge_transform(K0, dd, sched.bridge_middle, sched.chunk_bits, movement, e, bitnet,
                                      sched.lemma12_min_e, sched.lemma12_min_u))
    return c


def basic_mul_counts(a: int, b: int) -> Counter:
    """One BasicMul call (SPEC §6.5; MS Lemma 6.5 part 2, §2.2 (d)): the faithful schedule with max_depth = 0,
    so n = max(bits, 1) <= 64 is the listing's direct product (L706); otherwise the two-call root makes two
    transforms of length R0 = 2^K0, each ONE base radix-2 FFT (a leaf at depth 0) with K0 stages of R0/2
    butterflies, K0 bit-reversal passes and K0 stage splits on the tape, both through the faithful dispatcher's
    2D fallback; one safety-net residue check; no FastDFT node, no packed product, no lower stage."""
    n = max(abs(a).bit_length(), abs(b).bit_length(), 1)
    if n <= 64:
        return Counter({"hierarchy.basic": 1, "multiply.direct": 1})
    K0 = root_K0(n)
    return Counter({"hierarchy.basic": 1, "multiply.call": 1, "multiply.fallback_2d": 2, "fastdft.leaf": 2,
                    "basefft.butterfly": K0 << K0, "routing.leaf_bitrev_pass": 2 * K0,
                    "routing.leaf_stage_split": 2 * K0, "safety.residue_check": 1,
                    # word products (schoolbook inside BasicMul): 4 per butterfly, 3 per pointwise square
                    "word.call": 4 * (K0 << K0) + 3 * (1 << K0)})


#: Counters a BasicMul call must leave at 0 besides those of :func:`basic_mul_counts` (SPEC §6.5: no node, no
#: packed product, no call to a lower stage, no Python big product).
BASIC_ZERO_KEYS = ("fastdft.node", "kron.product", "spread.row", "hierarchy.multiply1", "hierarchy.multiply2",
                   "hierarchy.word_product", "python.big_product", "python.word_product_over_64", "bridge.dft")


#: The counters every exact end-to-end check compares (absent = 0), so that a path that must NOT run (direct
#: row additions, a clamp, a fallback) is pinned as well.
PATH_KEYS = (
    "multiply.call", "multiply.direct", "word.call", "bridge.dft", "bridge.middle", "bridge.d_clamped",
    "bridge.fallback_2d", "bridge.spread_axis", "kron.product", "bridge.axis_swap", "bridge.axis_expose",
    "bridge.axis_reverse",
    "interchange.lemma12_network_call", "layout.executed", "prop14.network_layer", "prop18.ring_product",
    "bluestein.tensor_dft", "bluestein.complex_convolution", "walsh.positional_map", "walsh.slice_batch",
    "walsh.leftover_cnot", "walsh.chunk_round", "walsh.prefix_round", "walsh.gadget", "walsh.exact_boundary",
    "m6.layer.network", "m6.c_power.network", "m6.c_power.leaf", "m6.c_single", "m6.gate", "m6.phase_edge.nonzero",
    "m6.phase_edge.zero", "m6.phase_edge.inverse_kernel", "m6.row_add.lemma13", "m6.row_add.direct",
    "lemma13.call", "lemma13.top_xor", "lemma13.rotation", "lemma13.swap", "lemma13.sort", "lemma13.reinsert",
    "lemma13.bad_records", "m6.batch.individual", "m6.batch.preprocessed_chunks", "m6.rows.padded",
    "m6.rows.removed")

_NETS: dict = {}


def nets() -> dict:
    """The compiled SPEC §2.5 fixtures (network definitions; validated at registration)."""
    if not _NETS:
        from subnlogn.m6.engine import compiled_fixture
        for name in ("C1", "C2", "B1", "B2", "B2q5"):
            _NETS[name] = compiled_fixture(name)
    return _NETS


def bit_lengths(pairs) -> list[int]:
    """n = max(bits(a), bits(b), 1) of each multiply(a, b) call (MS Thm 7.1: signs handled outside)."""
    return [max(abs(a).bit_length(), abs(b).bit_length(), 1) for a, b in pairs]
