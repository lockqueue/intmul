"""Tests for subnlogn.net.f2, zi2 and phase: F2 linear algebra, P_U/q_U, Lemma 6 bases, reduce_ops, C_U, Prop 8
(SPEC §2.3, R3)."""

import pytest
from hypothesis import assume, given, strategies as st

from subnlogn.net import f2, phase
from subnlogn.net.errors import NotAnInterface
from subnlogn.net.zi2 import A_COEF, B_COEF, ONE, ZI2, i_pow


@st.composite
def subspace(draw, m=None, max_m=6):
    m = draw(st.integers(1, max_m)) if m is None else m
    k = draw(st.integers(0, m))
    vs = draw(st.lists(st.integers(1, (1 << m) - 1), min_size=k, max_size=k))
    return m, f2.echelon(vs)


def test_zi2_arithmetic():
    a, b = A_COEF, B_COEF
    assert a * b == ZI2(1, 0, 1) and a * a + b * b == 0 and a + b == ONE
    assert ZI2(2, 4, 3) == ZI2(1, 2, 2) and hash(ZI2(2, 4, 3)) == hash(ZI2(1, 2, 2))
    assert ZI2.of(__import__("fractions").Fraction(3, 8)) == ZI2(3, 0, 3)
    with pytest.raises(ValueError):
        ZI2.of(__import__("fractions").Fraction(1, 3))
    assert [i_pow(e) for e in range(4)] == [ONE, ZI2(0, 1), ZI2(-1), ZI2(0, -1)]
    assert ZI2(1, 2).times_i() == ZI2(-2, 1) and ZI2(3, 1).conj() == ZI2(3, -1)


def test_reading_R3_identities():
    """C = HSH = aI + bX, C^{-1} = bI + aX = -iZCZ, C^2 = X, H0 = bSCS (R3) [Pr L1180-1204, L1298]."""
    H, S, Z, X, C = phase.H2_UNNORM, phase.S2, phase.Z2, phase.X2, phase.C2
    mm, sc = phase.matmul, phase.scalar_times
    assert sc(ZI2(1, 0, 1), mm(H, mm(S, H))) == C
    Cinv = [[B_COEF, A_COEF], [A_COEF, B_COEF]]
    assert mm(C, Cinv) == phase.dense_identity(1)
    assert sc(ZI2(0, -1), mm(Z, mm(C, Z))) == Cinv
    assert sc(ZI2(0, 1), mm(Z, mm(Cinv, Z))) == C
    assert mm(C, C) == X
    H0 = sc(B_COEF, mm(S, mm(C, S)))
    assert H0 == sc(ZI2(1, 0, 1), H)   # H0 = bSCS = (1/2)[[1, 1], [1, -1]], the normalized butterfly


@given(subspace())
def test_perp_intersection_projection(ms):
    m, U = ms
    P = f2.perp(U, m)
    assert len(P) + len(U) == m
    assert all(f2.dot(u, p) == 0 for u in U for p in P)
    assert f2.intersection(U, U, m) == () or f2.span_equal(f2.intersection(U, U, m), U)
    if f2.is_nondegenerate(U):
        proj = f2.Projector(U)
        for x in range(1 << m):
            px = proj(x)
            assert f2.in_span(px, U) and proj(px) == px
            assert all(f2.dot(x ^ px, u) == 0 for u in U)     # kernel is U^perp
        Up = f2.perp(U, m)
        assert f2.is_nondegenerate(Up)
        qu, qp = f2.q_form(U), f2.q_form(Up)
        assert all((qu(x) + qp(x) - x.bit_count()) % 4 == 0 for x in range(1 << m))  # orthogonal additivity


@given(subspace(max_m=7))
def test_orthonormal_basis(ms):
    m, E = ms
    if not f2.is_nondegenerate(E):
        with pytest.raises(NotAnInterface):
            f2.orthonormal_basis(E)
        return
    if E and f2.first_odd_weight_vector(E) is None:
        with pytest.raises(NotAnInterface, match="alternating"):
            f2.orthonormal_basis(E)
        return
    B = f2.orthonormal_basis(E)
    assert f2.gram(B) == f2.identity_rows(len(B)) and f2.span_equal(B, E)


def test_orthonormal_basis_absorbs_planes():
    E = (0b1000, 0b0011, 0b0101)        # a unit plus an alternating plane (Lemma 6 absorption)
    B = f2.orthonormal_basis(E)
    assert f2.gram(B) == f2.identity_rows(3) and f2.span_equal(B, E)
    with pytest.raises(NotAnInterface):
        f2.orthonormal_basis((0b0011, 0b0101))   # alternating, no unit vector


@given(st.integers(1, 7).flatmap(lambda m: st.tuples(st.just(m), st.lists(st.integers(1, (1 << m) - 1), max_size=m))))
def test_extend_and_reduce(arg):
    m, vs = arg
    basis = f2.echelon(vs)
    M = f2.extend_basis(basis, m)
    assert M[:len(basis)] == basis and f2.rank(M) == m
    ops = f2.reduce_ops(M, m)
    assert f2.replay_reduce_ops(M, ops, m) == f2.identity_rows(m)
    assert len(ops) <= m * (m - 1) + 3 * m
    for x in range(1 << m):     # reversed ops implement x -> Mx, ops implement x -> M^{-1}x (SPEC §4.3)
        assert f2.apply_row_ops_to_address(x, reversed(ops)) == f2.mat_vec_cols(M, x)
        assert f2.apply_row_ops_to_address(f2.mat_vec_cols(M, x), ops) == x


def test_eps_rule():
    assert f2.eps_signs((0b111,), 1) == (-1,) and f2.eps_signs((0b111,), -1) == (1,)
    assert f2.eps_signs((0b1,), 1) == (1,) and f2.eps_signs((0b1,), -1) == (-1,)


def test_C_full_and_zero():
    for m in (1, 2, 3):
        full = tuple(1 << i for i in range(m))
        assert phase.dense_C(full, m) == phase.C_tensor(m)
        assert phase.dense_C((), m) == phase.dense_identity(m)
        assert phase.matmul(phase.dense_C(full, m), phase.dense_C_inverse(full, m)) == phase.dense_identity(m)


@given(st.data())
def test_prop8_random_nested_labels(data):
    """C_V C_U^{-1} = prod C_{v_j}^{eps_j} for random nested nondegenerate labels, dense vs exhaustive vs quadratic
    (Prop 8) [Pr L1221-1256]."""
    m = data.draw(st.integers(2, 4))
    _, V = data.draw(subspace(m=m))
    assume(f2.is_nondegenerate(V))
    sub_vs = data.draw(st.lists(st.sampled_from(V), max_size=len(V))) if V else []
    U = f2.echelon(sub_vs)
    assume(f2.is_nondegenerate(U))
    E = f2.perp_within(U, V)
    assume(not E or f2.first_odd_weight_vector(E) is not None)
    B = f2.orthonormal_basis(E)
    for tail, head, d in ((U, V, 1 if E else 0), (V, U, -1 if E else 0)):
        eps = f2.eps_signs(B, d) if B else ()
        assert phase.edge_identity_dense(tail, head, B, eps, m)
        assert phase.edge_identity_exhaustive(tail, head, B, eps, m)
        assert phase.edge_identity_quadratic(tail, head, B, eps, m)
        if B:
            bad = (-eps[0],) + eps[1:]
            assert not phase.edge_identity_dense(tail, head, B, bad, m)
            assert not phase.edge_identity_exhaustive(tail, head, B, bad, m)
            assert not phase.edge_identity_quadratic(tail, head, B, bad, m)


def test_route_corrections_C1_X_route():
    """C_<e1,e2> C_<e0>^{-1} = C^{-1} (x) C (x) C, corrected by Z on coordinate 0 and i^1 (SPEC §2.5)."""
    for method in (phase.corrected_route_dense, phase.corrected_route_exhaustive, phase.corrected_route_quadratic):
        assert method((1,), (2, 4), 1, 1, 1, 3)
        assert not method((1,), (2, 4), 0, 0, 1, 3)
        assert not method((1,), (2, 4), 1, 1, 0, 3)
        assert not method((1,), (2, 4), 1, 0, 1, 3)


@given(subspace(max_m=5), subspace(max_m=5), st.integers(0, 31), st.integers(0, 3))
def test_route_methods_agree(a, b, z, theta):
    (m1, U), (m2, V) = a, b
    m = min(m1, m2)
    U = tuple(u for u in U if u < (1 << m))
    V = tuple(v for v in V if v < (1 << m))
    assume(f2.is_nondegenerate(U) and f2.is_nondegenerate(V))
    z &= (1 << m) - 1
    d = phase.corrected_route_dense(U, V, z, z, theta, m)
    assert d == phase.corrected_route_exhaustive(U, V, z, z, theta, m) == phase.corrected_route_quadratic(U, V, z, z,
                                                                                                         theta, m)
