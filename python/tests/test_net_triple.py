"""Tests for the lazy triple-network descriptor (SPEC §2.4) and its dense small-h materialization (h = 7, 8, 10)."""

import random
from itertools import combinations

import pytest

from subnlogn.net.errors import NotAdmissible, NotAnInterface
from subnlogn.net.model import SOURCE
from subnlogn.net.symbolic import CellSystem, edge_calculus
from subnlogn.net.triple import BANK, FORWARD, INVERSE, TripleNetwork, rank_comb, triple_params, unrank_comb
from subnlogn.net.triple_dense import (DenseTriple, dense_spot_check, run_full_scalar, run_invocation, sample_roles,
                                       validate_sample)
from subnlogn.net.certify import _dense_invocation

KINDS = ("bit", "complex")


def test_admissibility():
    for h in (3, 6):
        with pytest.raises(NotAdmissible):
            TripleNetwork(h, "bit")
    with pytest.raises(NotAdmissible):
        TripleNetwork(9, "bit")
    assert TripleNetwork(9, "complex").m == 729
    with pytest.raises(NotAdmissible):
        TripleNetwork(10, "real")


def test_schedule_constants():
    """Schedule (2), its inverse at stage 2 (row 7 - r, negated) and reading R1's physical order."""
    assert FORWARD == ("-J", "-R", "+V", "+G", "+R", "+J", "-G", "-V")
    assert INVERSE == ("+V", "+G", "-J", "-R", "-G", "-V", "+R", "+J")
    assert BANK == ("Y", "Y", "X", "X", "Y", "Y", "X", "X")
    for ops, src, tgt in ((FORWARD, "X", "Y"), (INVERSE, "Y", "X")):
        banks = tuple(src if op[1] in "VG" else tgt for op in ops)
        assert banks == BANK


@pytest.mark.parametrize("n,k", [(7, 3), (10, 3), (12, 2), (9, 1)])
def test_comb_ranking(n, k):
    for i, c in enumerate(combinations(range(n), k)):
        assert rank_comb(c, n) == i and unrank_comb(i, n, k) == c


@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("h", [7, 8, 10])
def test_neighbors_and_roles(kind, h):
    tn = TripleNetwork(h, kind)
    rng = random.Random(h)
    for _ in range(4):
        S = tn.triple(rng.randrange(tn.v))
        nb = [T for T in combinations(range(h), 3) if tn.is_neighbor(S, T)]
        assert len(nb) == tn.z
        assert sorted(tn.nbr_rank(S, T) for T in nb) == list(range(tn.z))
        assert all(tn.nbr_unrank(S, tn.nbr_rank(S, T)) == T for T in nb)
    for _ in range(1500):
        r = rng.randrange(tn.W)
        assert tn.role_id(tn.role_name(r)) == r
    assert sum(mult for _, mult, _ in tn.representatives()) == tn.W
    for g in rng.sample(range(tn.n_gates), 200):
        info = tn.gate_info(g)
        assert tn.gate_id(info.stage, dict(info.fixed), info.time, info.idx) == g


@pytest.mark.parametrize("kind", KINDS)
def test_vertices_are_the_touching_gates(kind):
    """For sampled roles, the vertex list is exactly the set of gates (in the role's invocations) touching it, in time
    order; data wires have 12 gates, scratch wires 4 (gates per wire <= 12) [Pr L2380-2382]."""
    tn = TripleNetwork(7, kind)
    for rid in sample_roles(tn, 1, seed=11):
        vs = tn.vertices(rid)
        assert vs[0] == SOURCE and vs[-1] == tn.SINK and list(vs[1:-1]) == sorted(vs[1:-1])
        assert len(vs) - 2 == (12 if rid < 2 * tn.N else 4)
        invs = {tn.gate_info(g).inv for g in vs[1:-1]}
        touching = [g for inv in sorted(invs) for g in range(inv * tn.gates_per_inv, (inv + 1) * tn.gates_per_inv)
                    if rid in tn.gate_roles(g)]
        assert touching == list(vs[1:-1])


@pytest.mark.parametrize("kind", KINDS)
def test_terminal_labels_and_stage_boundaries(kind):
    """At stage 1 the first X gate label is U_a; the last X / Y labels are F / U_a^perp (SPEC §2.4) [Pr L907-909]."""
    tn = TripleNetwork(8, kind)
    a = ((0, 3, 5), (1, 2, 7), (2, 4, 6))
    for bank in ("X", "Y"):
        rid = tn.role_id((bank, a))
        vs = tn.vertices(rid)
        first, last = tn.frame_at(rid, vs[1]).label, tn.frame_at(rid, vs[-2]).label
        cs = CellSystem(8, kind, [first, last, tn.source_frame(rid).label, tn.sink_frame(rid).label])
        if bank == "X":
            assert cs.cells(first) == cs.cells(tn.source_frame(rid).label)
        assert cs.cells(last) == cs.cells(tn.sink_frame(rid).label)


@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("h", [7, 8, 10])
def test_JV_plus_RG_is_identity_dense(kind, h):
    """One full invocation: JV + RG = I_v, every entry from the gate rows [Pr L715-723]."""
    _dense_invocation(TripleNetwork(h, kind))


@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("h", [7, 8])
def test_lemma5_invocations(kind, h):
    """Executing each stage's invocation on random scalars (random scratch) gives y += x / x -= y, scratch restored."""
    tn = TripleNetwork(h, kind)
    rng = random.Random(h)
    for j in (1, 2, 3):
        fixed = {k: tn.triple(rng.randrange(tn.v)) for k in (1, 2, 3) if k != j}
        run_invocation(tn, j, fixed, seed=j)


def test_lemma5_invocation_detects_tampering():
    class Broken(TripleNetwork):
        def gate_row(self, gid, out_role):
            row = super().gate_row(gid, out_role)
            if self.gate_info(gid).op == "+J" and out_role < 2 * self.N and len(row) > 1:
                row.pop(max(row))                     # drop one side term
            return row
    with pytest.raises(NotAnInterface):
        run_invocation(Broken(7, "bit"), 1, {2: (0, 1, 2), 3: (0, 1, 2)})


@pytest.mark.parametrize("kind", KINDS)
def test_dense_spot_check_h7(kind):
    """Dense frames for random roles; exact ranks of every edge equal the cell calculus (SPEC §2.7 step 10)."""
    rows = dense_spot_check(TripleNetwork(7, kind), 1, seed=3)
    assert rows and all(r.dense == r.symbolic for r in rows)
    if kind == "bit":
        assert {"idempotent-trace"} <= {r.method for r in rows}


def test_validate_sample_complex_h7():
    """§2.6 phase checks (labels, residual bases, eps, M, reduce_ops, Prop 8 by the quadratic test) and corrected
    routes on the dense edges of an X wire, a Y wire and the scratch wires of one stage-2 invocation."""
    tn = TripleNetwork(7, "complex")
    a = ((0, 3, 5), (1, 2, 6), (2, 4, 5))
    fixed = ((1, (0, 2, 4)), (3, (1, 3, 5)))
    roles = [tn.role_id(("X", a)), tn.role_id(("Y", a)), tn.role_id(("C", 2, fixed, 0)),
             tn.role_id(("Cstar", 2, fixed)), tn.role_id(("A", 2, fixed, (0, 1, 2), (3, 4, 5))),
             tn.role_id(("A", 2, fixed, (0, 1, 2), (0, 1, 3)))]
    counts = validate_sample(tn, seed=4, roles=roles)
    assert counts["edges"] == 2 * 13 + 4 * 5 and counts["routes"] == 6


def test_validate_sample_bit_h7_low_rank():
    """Lemma 9 factorizations of dense 343 x 343 edge matrices (rank <= 1) on one center and one side wire, and the
    exact ranks plus endpoint identity (11) of one X data wire."""
    tn = TripleNetwork(7, "bit")
    fixed = ((2, (0, 2, 4)), (3, (1, 3, 5)))
    roles = [tn.role_id(("C", 1, fixed, 3)), tn.role_id(("A", 1, fixed, (0, 1, 2), (2, 3, 4)))]
    counts = validate_sample(tn, seed=4, lemma9_max_rank=1, roles=roles)
    assert counts["lemma9"] == 4 and counts["edges"] == 10 and counts["routes"] == 2
    counts = validate_sample(tn, seed=4, lemma9_max_rank=0, roles=[tn.role_id(("X", ((0, 1, 2),) * 3))])
    assert counts["edges"] == 13 and counts["routes"] == 1


def test_symbolic_label_dims_match_dense_h7():
    tn = TripleNetwork(7, "complex")
    dt = DenseTriple(tn)
    for rid in sample_roles(tn, 1, seed=2)[:4]:
        for v in tn.vertices(rid):
            assert len(dt.frame(rid, v)) == tn.frame_at(rid, v).label.dim(7)


def test_physical_order_misreading_breaks_nesting():
    """Reading R1: with the plain-text order (times 3 and 4 exchanged) the labels are not an interface."""
    class Misread(TripleNetwork):
        def stage_label(self, j, fixed, time, t=None):
            time = {3: 4, 4: 3}.get(time, time)
            return super().stage_label(j, fixed, time, t)
    from subnlogn.net.certify import certify_triple
    for kind in KINDS:
        tn = Misread(8, kind)
        dec = set()
        for rid, _, _ in tn.representatives():
            for _, _, ft, fh, cls in tn.sym_edges(rid):
                if edge_calculus(8, kind, ft, fh).direction < 0:
                    dec.add(cls[1:])
        assert ("X", "2->3") in dec and ("Y", "4->5") in dec and ("center", "3->4") not in dec
        with pytest.raises(NotAnInterface):
            certify_triple(8, kind, network=tn)


def test_params_closed_forms():
    p = triple_params(100, "complex")
    assert (p.v, p.N, p.m, p.I, p.z) == (161700, 4227952113000000, 10 ** 6, 78440670000, 147731)
    assert p.W == 1873807244643542670000 and p.s == 1873807244636671267308000000


@pytest.mark.slow
@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("h", [8, 10])
def test_dense_spot_check_slow(kind, h):
    assert all(r.dense == r.symbolic for r in dense_spot_check(TripleNetwork(h, kind), 1, seed=h))


@pytest.mark.slow
@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("h", [7, 8, 10])
def test_validate_sample_slow(kind, h):
    cap = 2 * h if h <= 8 else 1
    counts = validate_sample(TripleNetwork(h, kind), 1, seed=h, lemma9_max_rank=cap)
    assert counts["routes"] >= 7


@pytest.mark.slow
@pytest.mark.parametrize("kind", KINDS)
def test_full_scalar_execution_h7(kind):
    """Every gate of the h = 7 network on random scalars: (X_a, Y_a) -> (-Y_a, X_a), scratch restored (Lemma 5)."""
    run_full_scalar(TripleNetwork(7, kind), seed=1)
