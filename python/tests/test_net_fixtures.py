"""Tests for the network data model and the SPEC §2.5 fixtures (compile, counts, edges)."""

from subnlogn.net.fixtures import EXPECTED, FIXTURES, fixture_B1, fixture_C1, SCALAR_STEPS
from subnlogn.net.model import SOURCE, compile_network, role_vertices
from subnlogn.net.qmatrix import identity, qmat, sub


def test_counts_match_spec():
    for name, make in FIXTURES.items():
        c = compile_network(make())
        assert (c.W, c.m, c.s, c.q) == EXPECTED[name], name


def test_role_touch_lists():
    net = fixture_B1()
    vs = role_vertices(net)
    assert vs[0] == (SOURCE, 1, 3, 5, 7, 9, 11, 12)
    assert vs[1] == (SOURCE, 0, 2, 4, 6, 8, 10, 12)
    assert vs[2] == (SOURCE,) + tuple(range(12)) + (12,)
    assert len(SCALAR_STEPS) == 12


def test_B1_edges():
    c = compile_network(fixture_B1())
    J2 = qmat([[1, 1], [1, 1]])
    P0 = qmat([[1, 0], [0, 0]])
    nz = {(e.role, e.tail, e.head): (e.A, e.rank) for e in c.all_edges if e.rank}
    assert nz == {(0, -1, 1): (P0, 1), (0, 11, 12): (identity(2), 2),
                  (1, -1, 0): (J2, 1), (1, 0, 2): (sub(qmat([[0, 0], [0, 0]]), J2), 1),
                  (1, 10, 12): (sub(identity(2), P0), 1),
                  (2, -1, 0): (J2, 1), (2, 0, 1): (sub(qmat([[0, 0], [0, 0]]), J2), 1), (2, 11, 12): (identity(2), 2)}
    e = c.edge(1, -1, 0)
    assert e.E1 == qmat([[1, 0], [1, 1]]) and e.pivots == ((0, 1),)


def test_C1_edges():
    c = compile_network(fixture_C1())
    got = {(e.role, e.tail, e.head): (e.direction, e.basis, e.eps) for e in c.all_edges if e.basis}
    assert got == {(0, -1, 1): (-1, (1,), (-1,)), (0, 11, 12): (1, (1, 2, 4), (1, 1, 1)),
                   (1, -1, 0): (1, (7,), (-1,)), (1, 0, 2): (-1, (7,), (1,)), (1, 10, 12): (1, (2, 4), (1, 1)),
                   (2, -1, 0): (1, (7,), (-1,)), (2, 0, 1): (-1, (7,), (1,)), (2, 11, 12): (1, (1, 2, 4), (1, 1, 1))}
    assert c.edge(1, -1, 0).M_cols == (7, 1, 2)    # M = [v, e0, e1] (SPEC §2.5)


# ----------------------------------------------------------------------------------------------- validate
import random  # noqa: E402
from dataclasses import replace  # noqa: E402
from fractions import Fraction  # noqa: E402

import pytest  # noqa: E402

from subnlogn.net.errors import NotAnInterface  # noqa: E402
from subnlogn.net.execute import (C_tensor_apply, bit_frame_invariant_outputs, bit_interface_outputs,  # noqa: E402
                                  corrected_phase, phase_frame_invariant_outputs, run_bit, run_phase)
from subnlogn.net.fixtures import fixture_B2, fixture_C2, scalar_gates, scalar_network_map, ROLES, ROUTE  # noqa
from subnlogn.net.model import Gate, Network  # noqa: E402
from subnlogn.net.validate import validate  # noqa: E402
from subnlogn.net.zi2 import ZI2  # noqa: E402


@pytest.mark.parametrize("name", sorted(FIXTURES))
def test_fixtures_validate(name):
    rep = validate(FIXTURES[name]())
    W, m, s, q = EXPECTED[name]
    assert (rep.W, rep.m, rep.s, rep.q_radix) == (W, m, s, q)
    assert rep.saving == W * m - s < 0 and not rep.saves       # no saving, intended (Dev-1)
    assert rep.aux_roles == (2,)
    for method in ("exhaustive", "quadratic"):
        if rep.domain == "ZI2":
            assert validate(FIXTURES[name](), method=method).endpoint_method == method


def test_scalar_circuit_map():
    T = scalar_network_map("ZI2")
    assert T == [[0, -1, 0], [1, 0, 0], [0, 0, 1]]
    assert scalar_network_map("F2") == [[0, 1, 0], [1, 0, 0], [0, 0, 1]]


def _gate_frame(net, g, frame):
    gates = list(net.gates)
    gates[g] = replace(gates[g], frame=frame)
    return replace(net, gates=tuple(gates))


BROKEN_NETWORKS = {
    "B1 wrong sink frame": lambda: replace(fixture_B1(), sink=(identity(2), identity(2), identity(2))),
    "B1 wrong route": lambda: replace(fixture_B1(), route=(0, 1, 2)),
    "B1 sign over F2": lambda: replace(fixture_B1(), route_sign=(1, -1, 1)),
    "B1 non-rational frame": lambda: _gate_frame(fixture_B1(), 3, ((0.5, 0), (0, 0))),
    "B1 corrections on a bit net": lambda: replace(fixture_B1(), pre_zmask=((0,), (), ())),
    "C1 wrong route sign": lambda: replace(fixture_C1(), route_sign=(1, 1, 1)),
    "C1 missing pre-Z mask": lambda: replace(fixture_C1(), pre_zmask=None),
    "C1 missing post-Z mask": lambda: replace(fixture_C1(), post_zmask=None),
    "C1 missing post phase": lambda: replace(fixture_C1(), post_ipow=(0, 0, 0)),
    "C1 wrong sink label": lambda: replace(fixture_C1(), sink=((1, 2, 4), (2, 4), (1, 2))),
    "C1 non-nested labels": lambda: _gate_frame(fixture_C1(), 2, (1,)),
    "C1 degenerate label": lambda: _gate_frame(fixture_C1(), 4, (0b011,)),
    "C1 dependent label basis": lambda: _gate_frame(fixture_C1(), 4, (1, 1)),
    "C2 duplicate gate roles": lambda: replace(fixture_C2(), gates=(Gate((0, 0), ((1, 0), (0, 1)), ()),)
                                               + fixture_C2().gates[1:]),
    "C2 gate entry not dyadic": lambda: replace(fixture_C2(), gates=(Gate((1, 2), ((1, Fraction(1, 3)), (0, 1)), ()),)
                                                + fixture_C2().gates[1:]),
}


@pytest.mark.parametrize("name", sorted(BROKEN_NETWORKS))
def test_broken_networks_fail(name):
    with pytest.raises(NotAnInterface):
        validate(BROKEN_NETWORKS[name]())


def test_alternating_residual_is_rejected():
    """A nondegenerate alternating label (Gram [[0,1],[1,0]]) reached from 0 has no orthonormal residual basis."""
    net = fixture_C2()
    full4 = (1, 2, 4, 8)
    net = replace(net, m=4, gates=tuple(replace(g, frame=()) for g in net.gates), source=((), (), ()),
                  sink=(full4,) * 3)
    net = _gate_frame(net, 1, (0b0011, 0b0110))
    with pytest.raises(NotAnInterface, match="alternating"):
        validate(net)


def _tamper_edge(c, w, idx, **kw):
    edges = [list(es) for es in c.edges]
    edges[w][idx] = replace(edges[w][idx], **kw)
    return replace(c, edges=tuple(map(tuple, edges)))


def test_tampered_compiled_networks_fail():
    cb = compile_network(fixture_B1())
    e = cb.edge(1, -1, 0)                                  # J2 edge, index 0 of role Y
    bad = {
        "rank": _tamper_edge(cb, 1, 0, rank=2),
        "pivots": _tamper_edge(cb, 1, 0, pivots=((1, 1),)),
        "E1 not lower": _tamper_edge(cb, 1, 0, E1=qmat([[1, 1], [0, 1]])),
        "E1inv": _tamper_edge(cb, 1, 0, E1inv=identity(2)),
        "A": _tamper_edge(cb, 1, 0, A=identity(2)),
        "prime 2": replace(cb, q=2),
        "prime 9": replace(cb, q=9),
        "s": replace(cb, s=11),
    }
    assert e.rank == 1
    for name, c in bad.items():
        with pytest.raises(NotAnInterface):
            validate(c)
    cc = compile_network(fixture_C1())                     # role Y edge 0: 0 -> <v>
    bad = {
        "eps": _tamper_edge(cc, 1, 0, eps=(1,)),
        "basis": _tamper_edge(cc, 1, 0, basis=(1,), M_cols=(1, 2, 4)),
        "direction": _tamper_edge(cc, 1, 0, direction=-1),
        "M_cols": _tamper_edge(cc, 1, 0, M_cols=(7, 1, 6)),
        "reduce_ops": _tamper_edge(cc, 1, 0, reduce_ops=((1, 0),)),
        "prime on complex": replace(cc, q=3),
    }
    for name, c in bad.items():
        with pytest.raises(NotAnInterface):
            validate(c)


def test_bad_prime_detected():
    """A frame with denominator 3 forbids q = 3: compile picks 5, and forcing 3 fails validation."""
    net = _gate_frame(fixture_B2(), 1, qmat([[Fraction(1, 3), 0], [0, 0]]))
    c = compile_network(net)
    assert c.q == 5
    assert validate(c).q_radix == 5
    with pytest.raises(NotAnInterface, match="denominator"):
        validate(replace(c, q=3))


# ----------------------------------------------------------------------------------------------- executor
@pytest.mark.parametrize("name", ["B1", "B2"])
@pytest.mark.parametrize("b", [1, 2])
@pytest.mark.parametrize("mode", ["dense", "factored"])
def test_bit_executor(name, b, mode):
    c = compile_network(FIXTURES[name]())
    rng = random.Random(hash((name, b, mode)) & 0xffff)
    n = (c.q ** b) ** (2 * c.m)
    inp = [[rng.getrandbits(5) for _ in range(n)] for _ in range(c.W)]
    out = run_bit(c, inp, b, mode)
    assert out == bit_frame_invariant_outputs(c, inp, b)       # (5)
    assert out == bit_interface_outputs(c, inp, b)             # H <- H + D on every routed role


def test_bit_executor_frame_invariant_without_interface():
    c = compile_network(BROKEN_NETWORKS["B1 wrong sink frame"]())
    rng = random.Random(5)
    inp = [[rng.getrandbits(4) for _ in range(81)] for _ in range(3)]
    out = run_bit(c, inp)
    assert out == bit_frame_invariant_outputs(c, inp)
    assert out != bit_interface_outputs(c, inp)


@pytest.mark.parametrize("name", ["C1", "C2"])
@pytest.mark.parametrize("k", [1, 2])
@pytest.mark.parametrize("mode", ["dense", "factored", "coordinate"])
def test_phase_executor(name, k, mode):
    c = compile_network(FIXTURES[name]())
    rng = random.Random(hash((name, k, mode)) & 0xffff)
    n = 1 << (c.m * k)
    inp = [[ZI2(rng.randint(-8, 8), rng.randint(-8, 8), rng.randint(0, 3)) for _ in range(n)] for _ in range(c.W)]
    assert run_phase(c, inp, k, mode) == phase_frame_invariant_outputs(c, inp, k)
    cor = corrected_phase(c, inp, k, mode)
    assert all(cor[w] == C_tensor_apply(inp[w], c.m, k) for w in range(c.W))


def test_phase_executor_detects_missing_corrections():
    c = compile_network(BROKEN_NETWORKS["C1 missing pre-Z mask"]())
    rng = random.Random(9)
    inp = [[ZI2(rng.randint(-8, 8), rng.randint(-8, 8)) for _ in range(8)] for _ in range(3)]
    cor = corrected_phase(c, inp, 1)
    assert cor[0] != C_tensor_apply(inp[0], 3, 1) and cor[1] == C_tensor_apply(inp[1], 3, 1)


# ----------------------------------------------------------------------------------------------- random bit networks
from hypothesis import HealthCheck, given, settings, strategies as st  # noqa: E402

_rat = st.sampled_from([Fraction(0), Fraction(1), Fraction(-1), Fraction(1, 2), Fraction(-1, 2), Fraction(2)])


@settings(max_examples=12, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(st.lists(st.lists(st.lists(_rat, min_size=2, max_size=2), min_size=2, max_size=2), min_size=15, max_size=15),
       st.integers(0, 2 ** 32))
def test_random_bit_interfaces(mats, seed):
    """Any rational gate frames, any sources S_w and sinks S_w + I at rho(w), give a valid bit interface (11); the
    executor (edges applied through their Lemma 9 factors mod q) realizes H <- H + D on every role (Prop 11 proof)."""
    frames = [qmat(M) for M in mats]
    src = tuple(frames[12:15])
    sink = [None] * 3
    for w in range(3):
        sink[ROUTE[w]] = qmat([[src[w][i][j] + (i == j) for j in range(2)] for i in range(2)])
    net = Network(domain="F2", m=2, roles=ROLES, gates=scalar_gates("F2", frames[:12]), source=src,
                  sink=tuple(sink), route=ROUTE, route_sign=(1, 1, 1))
    c = compile_network(net)
    rep = validate(c)
    assert rep.s == sum(e.rank for e in c.all_edges)
    if c.q > 7:                                   # keep the executor's address space small (q^4 addresses)
        return
    rng = random.Random(seed)
    n = c.q ** 4
    inp = [[rng.getrandbits(3) for _ in range(n)] for _ in range(3)]
    out = run_bit(c, inp, 1, "factored")
    assert out == bit_interface_outputs(c, inp) == bit_frame_invariant_outputs(c, inp)


def test_B2q5_fixture():
    """B2 with gate frame J2/3: q_radix = 5 (3 is a denominator and a diagonal numerator of E1^{-1}); used by the
    M5 interchange tests to exercise q != W row padding (SPEC §3.7)."""
    from subnlogn.net.fixtures import fixture_B2q5
    c = compile_network(fixture_B2q5())
    rep = validate(c)
    assert (rep.W, rep.m, rep.s, rep.q_radix) == (3, 2, 10, 5)
    e = c.edge(0, -1, 1)
    assert e.rank == 1 and 3 in {x.denominator for r in e.E1 for x in r}
    rng = random.Random(3)
    inp = [[rng.getrandbits(3) for _ in range(5 ** 4)] for _ in range(3)]
    assert run_bit(c, inp, 1, "factored") == bit_interface_outputs(c, inp)
