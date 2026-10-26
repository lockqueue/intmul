"""Tests for subnlogn.interchange (SPEC §3.4-§3.8, acceptance §3.11; Pr L1375-1692): every completed
interchange is checked with the oracle new[f(addr)] = old[addr] on unique record ids (and on random
one-bit payloads), with nonempty prefix / gap / suffix fields, fixtures B1 (primary) and B2, a q = 5
variant of B2 that forces row padding, exact child-call counts and every compiled factorization."""

import random
from fractions import Fraction

import pytest
from hypothesis import given, settings, strategies as st

import path_model as PM
from subnlogn.instrument import Instrument
from subnlogn.interchange import (
    InterchangePolicy, lower_change, matrix_shear, power_swap, swap_bit_chunks, swap_q_chunks, theorem_policy,
)
from subnlogn.net import compile_network
from subnlogn.net.fixtures import fixture_B1, fixture_B2, fixture_B2q5
from subnlogn.net.qmatrix import specialize
from subnlogn.stream import Field, Shape, address_of, index_of

POL = InterchangePolicy()


NETS = {"B1": compile_network(fixture_B1()), "B2": compile_network(fixture_B2()),
        "B2q5": compile_network(fixture_B2q5())}     # B2 with gate frame J2/3: q_radix = 5 (net.fixtures)


def ids(shape):
    return list(range(shape.volume))


def check(old_shape, new_shape, out, f, payload=None):
    """out[index(new, f(addr))] == payload[index(old, addr)] (payload defaults to the record ids)."""
    payload = payload if payload is not None else ids(old_shape)
    assert len(out) == new_shape.volume
    for i in range(old_shape.volume):
        a = address_of(old_shape, i)
        assert out[index_of(new_shape, f(dict(a)))] == payload[i]


def swapped(H, D):
    def f(a):
        a[H], a[D] = a[D], a[H]
        return a
    return f


# ----------------------------------------------------------------------------------------------
# lower_change and matrix_shear (Lemma 10)
# ----------------------------------------------------------------------------------------------


@settings(max_examples=40)
@given(st.integers(1, 3), st.integers(1, 2), st.data())
def test_lower_change_random(m, b, data):
    q = 3
    Q = q ** b
    nums = st.integers(-5, 5)
    den = st.sampled_from([1, 2, 4, 5, 7])
    E = [[Fraction(0)] * m for _ in range(m)]
    for i in range(m):
        E[i][i] = Fraction(data.draw(st.sampled_from([1, -1, 2, -2, 4, 5])), data.draw(den))
        for j in range(i):
            E[i][j] = Fraction(data.draw(nums), data.draw(den))
    fields = [Field(("f", i), Q, q) for i in range(m)]
    spec = [Field(("s", i), data.draw(st.integers(1, 2))) for i in range(m + 1)]
    sh = Shape(tuple(x for pair in zip(spec, fields + [None]) for x in pair if x is not None))
    names = [f.name for f in fields]
    out, sh2 = lower_change(ids(sh), sh, names, E, Q)
    Es = [[specialize(x, Q) for x in row] for row in E]
    check(sh, sh2, out, lambda a: {**a, **{names[i]: sum(Es[i][j] * a[names[j]] for j in range(m)) % Q
                                           for i in range(m)}})


@pytest.mark.parametrize("name", ["B1", "B2", "B2q5"])
def test_every_factorization_and_edge(name):
    """matrix_shear realizes (H, D) -> (H + A D, D) for every edge (rank 0..2) with exactly rank child
    interchanges; lower_change applies every compiled factor E1, E2, E1inv, E2inv (Lemma 9 / 10)."""
    net = NETS[name]
    q, m = net.q, net.m
    sh = Shape((Field("P", 2), Field("H0", q, q), Field("H1", q, q), Field("g", 2),
                Field("D0", q, q), Field("D1", q, q), Field("z", 1 if q > 3 else 2)))
    H, D = ["H0", "H1"], ["D0", "D1"]
    for edge in net.all_edges:
        A = [[specialize(x, q) for x in row] for row in edge.A]
        out, sh2, n = matrix_shear(ids(sh), sh, H, D, edge, net, "P", 0, POL)
        assert n == edge.rank and sh2 == sh
        check(sh, sh2, out, lambda a: {**a, **{H[i]: (a[H[i]] + sum(A[i][j] * a[D[j]] for j in range(m))) % q
                                               for i in range(m)}})
        for E in (edge.E1, edge.E2, edge.E1inv, edge.E2inv):
            Es = [[specialize(x, q) for x in row] for row in E]
            out, _ = lower_change(ids(sh), sh, D, E, q)
            check(sh, sh, out, lambda a: {**a, **{D[i]: sum(Es[i][j] * a[D[j]] for j in range(m)) % q
                                                  for i in range(m)}})


def test_matrix_shear_with_network_children():
    """b = 2 digits per field: each pivot's interchange is a Prop 11 call at k = 1 (row field divisible
    by W) -- a shear whose children use the network."""
    net = NETS["B1"]
    edge = next(e for e in net.all_edges if e.rank == 2)
    sh = Shape((Field("R", 3), Field("H0", 9, 3), Field("H1", 9, 3), Field("D0", 9, 3), Field("D1", 9, 3)))
    inst = Instrument()
    out, sh2, n = matrix_shear(ids(sh), sh, ["H0", "H1"], ["D0", "D1"], edge, net, "R", 1, POL, inst)
    A = [[specialize(x, 9) for x in row] for row in edge.A]
    check(sh, sh2, out, lambda a: {**a, "H0": (a["H0"] + A[0][0] * a["D0"] + A[0][1] * a["D1"]) % 9,
                                   "H1": (a["H1"] + A[1][0] * a["D0"] + A[1][1] * a["D1"]) % 9})
    assert n == 2 and inst.counts["interchange.prop11_node"] == 2
    assert inst.counts["interchange.child_call"] == 2 * net.s


# ----------------------------------------------------------------------------------------------
# Proposition 11
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("name,k,rows", [(n, k, r) for n in ("B1", "B2", "B2q5") for k, r in ((1, 3), (1, 6))]
                         + [("B1", 2, 9), ("B2", 2, 9), pytest.param("B2q5", 2, 9, marks=pytest.mark.slow)])
def test_power_swap_direct(name, k, rows):
    net = NETS[name]
    q, e = net.q, net.m ** k
    small = k == 2
    sh = Shape((Field("P", 1 if small else 2), Field("R", rows), Field("H", q ** e, q), Field("g", 1 if small else 2),
                Field("D", q ** e, q), Field("z", 1 if small else 2)))
    inst = Instrument()
    out, sh2 = power_swap(ids(sh), sh, "H", "D", net, "R", k, POL, inst)
    assert sh2 == sh
    check(sh, sh2, out, swapped("H", "D"))
    nodes = sum((net.s ** j for j in range(k)))  # 1 node at level k, s at level k-1, ...
    assert inst.counts["interchange.prop11_node"] == nodes
    assert inst.counts["interchange.child_call"] == net.s * nodes
    assert all(c == s for _, c, s in (v for key, v in inst.notes if key == "interchange.node"))


def test_power_swap_one_bit_payloads_and_scratch_rows():
    """Payloads of one random bit (no ids), and rows assigned to the scratch role carry arbitrary data."""
    net = NETS["B1"]
    sh = Shape((Field("R", 6), Field("H", 9, 3), Field("g", 2), Field("D", 9, 3)), payload_bits=1)
    rng = random.Random(7)
    bits = [rng.randrange(2) for _ in range(sh.volume)]
    out, sh2 = power_swap(bits, sh, "H", "D", net, "R", 1, POL)
    check(sh, sh2, out, swapped("H", "D"), payload=bits)


def test_power_swap_rejects_bad_rows_and_order():
    net = NETS["B1"]
    sh = Shape((Field("R", 4), Field("H", 9, 3), Field("D", 9, 3)))
    with pytest.raises(ValueError):
        power_swap(ids(sh), sh, "H", "D", net, "R", 1, POL)  # 4 rows not divisible by W = 3
    sh = Shape((Field("H", 9, 3), Field("R", 3), Field("D", 9, 3)))
    with pytest.raises(ValueError):
        power_swap(ids(sh), sh, "H", "D", net, "R", 1, POL)  # row field must precede both chunks


# ----------------------------------------------------------------------------------------------
# Lemma 12
# ----------------------------------------------------------------------------------------------


@pytest.mark.parametrize("e", [1, 2, 3, 4, 5])
@pytest.mark.parametrize("min_e", [0, 2, 10])
def test_swap_q_chunks(e, min_e):
    net = NETS["B1"]
    big = e >= 5
    sh = Shape((Field("P", 1 if big else 2), Field("H", 3 ** e, 3), Field("g", 1 if big else 2),
                Field("D", 3 ** e, 3), Field("z", 1 if big else 2)))
    inst = Instrument()
    out, sh2 = swap_q_chunks(ids(sh), sh, "H", "D", net, InterchangePolicy(lemma12_min_e=min_e), inst)
    assert sh2 == sh
    check(sh, sh2, out, swapped("H", "D"))
    if e < max(min_e, 1) or e <= 2:
        assert inst.counts["interchange.prop11_node"] == 0
    # exact: one Prop 11 call per base-m piece of e - rho with j >= 1 (SPEC §3.7; path_model)
    calls = PM.q_chunk_calls(e, net, min_e)
    assert inst.counts.get("interchange.lemma12_network_call", 0) == calls
    assert calls == (1 if e >= max(min_e, 3) else 0)


#: SPEC §3.10 table for q = W = 3, m = 2: network levels per binary width u.
LEVELS = {1: 0, 2: 0, 3: 0, 4: 1, 5: 1, 6: 1, 7: 1, 8: 2, 9: 2}


@pytest.mark.parametrize("name", ["B1", "B2"])
@pytest.mark.parametrize("u", [1, 2, 3, 4, 5, 6, 7])
def test_swap_bit_chunks_equal(name, u):
    net = NETS[name]
    big = u >= 6
    sh = Shape((Field("P", 1 if big else 2), Field("H", 2 ** u, 2), Field("g", 1 if big else 3),
                Field("D", 2 ** u, 2), Field("z", 1 if big else 2)))
    inst = Instrument()
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", net, POL, inst)
    assert sh2 == sh
    check(sh, sh2, out, swapped("H", "D"))
    nodes = inst.counts["interchange.prop11_node"]
    assert nodes == (0 if LEVELS[u] == 0 else sum(net.s ** j for j in range(LEVELS[u])))
    assert inst.counts["interchange.child_call"] == net.s * nodes
    assert inst.counts.get("interchange.lemma12_network_call", 0) == PM.l12_calls(u, net) == (1 if u >= 4 else 0)
    assert nodes == PM.prop11_nodes(u, net)                               # exact (path_model)
    assert inst.counts["interchange.range_pad"] == inst.counts["interchange.range_unpad"] == (1 if u >= 1 else 0)


@pytest.mark.slow
@pytest.mark.parametrize("u", [8, 9])
def test_swap_bit_chunks_two_levels(u):
    net = NETS["B1"]
    sh = Shape((Field("H", 2 ** u, 2), Field("D", 2 ** u, 2)))
    inst = Instrument()
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", net, POL, inst)
    check(sh, sh2, out, swapped("H", "D"))
    assert inst.counts["interchange.prop11_node"] == 1 + net.s
    assert inst.counts["interchange.child_call"] == net.s * (1 + net.s)


@pytest.mark.parametrize("u", [4, 5, 6])
def test_row_padding_with_q5(u):
    """q_radix = 5 != W = 3: Lemma 12 pads its row field (q^(2 rho) -> W^k ceil(...)), the padded rows
    are zero at every completed boundary (asserted inside) and are deleted."""
    net = NETS["B2q5"]
    sh = Shape((Field("P", 2), Field("H", 2 ** u, 2), Field("g", 2), Field("D", 2 ** u, 2)))
    inst = Instrument()
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", net, POL, inst)
    check(sh, sh2, out, swapped("H", "D"))
    assert inst.counts["interchange.row_pad"] == inst.counts["interchange.row_unpad"] == 1
    assert inst.counts["interchange.prop11_node"] == (1 if u >= 5 else 0)


@pytest.mark.parametrize("uH,uD", [(1, 0), (0, 1), (2, 1), (1, 2), (3, 4), (4, 3), (5, 4), (4, 5), (0, 0), (2, 2)])
def test_swap_bit_chunks_unequal_and_zero_width(uH, uD):
    net = NETS["B1"]
    sh = Shape((Field("P", 2), Field("H", 2 ** uH, 2), Field("g", 3), Field("D", 2 ** uD, 2), Field("z", 2)))
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", net, POL)
    assert sh2.names == sh.names and sh2.length("H") == 2 ** uD and sh2.length("D") == 2 ** uH
    check(sh, sh2, out, swapped("H", "D"))


def test_one_bit_payload_lemma12():
    net = NETS["B1"]
    sh = Shape((Field("H", 16, 2), Field("g", 2), Field("D", 32, 2)), payload_bits=1)
    rng = random.Random(3)
    bits = [rng.randrange(2) for _ in range(sh.volume)]
    inst = Instrument()
    out, sh2 = swap_bit_chunks(bits, sh, "H", "D", net, POL, inst)
    check(sh, sh2, out, swapped("H", "D"), payload=bits)
    assert inst.counts["interchange.lemma12_network_call"] == 1      # 4 vs 5 bits: through the bit network


def test_theorem_policy_never_touches_the_network():
    """Real networks: every call goes to base cases; here the 'network' is None, so any access fails."""
    sh = Shape((Field("H", 2 ** 5, 2), Field("g", 2), Field("D", 2 ** 6, 2)))
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", None, theorem_policy())
    check(sh, sh2, out, swapped("H", "D"))
    sq = Shape((Field("H", 3 ** 4, 3), Field("D", 3 ** 4, 3)))
    out, sq2 = swap_q_chunks(ids(sq), sq, "H", "D", None, theorem_policy())
    check(sq, sq2, out, swapped("H", "D"))


@settings(max_examples=12)
@given(st.sampled_from(["B1", "B2"]), st.integers(1, 5), st.integers(-1, 1), st.integers(1, 2),
       st.integers(1, 3), st.integers(1, 2), st.integers(0, 3))
def test_swap_bit_chunks_random_layouts(name, u, du, P, G, Z, min_u):
    """Random prefix / gap / suffix lengths, widths u and u + du, and bitwise cutoffs."""
    uD = max(0, u + du)
    sh = Shape((Field("P", P), Field("H", 2 ** u, 2), Field("g", G), Field("D", 2 ** uD, 2), Field("z", Z)))
    out, sh2 = swap_bit_chunks(ids(sh), sh, "H", "D", NETS[name], InterchangePolicy(lemma12_min_u=min_u))
    check(sh, sh2, out, swapped("H", "D"))
