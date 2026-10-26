"""Tests for subnlogn.net.qmatrix: exact rational matrices, Lemma 9 (SPEC §3.1) and q_radix (SPEC §3.2)."""

from fractions import Fraction as F

import pytest
from hypothesis import given, strategies as st

from subnlogn.net.qmatrix import (bruhat_product, choose_prime, identity, inverse, is_invertible_lower, is_lower,
                                  kron, least_odd_prime_avoiding, lower_bruhat, lower_bruhat_factors, mul, neg,
                                  nullspace, partial_permutation, qmat, rank_Q, specialize, specialize_matrix, sub,
                                  zeros, is_odd_prime, mat_vec)

rat = st.fractions(min_value=-4, max_value=4, max_denominator=6)


@st.composite
def matrix_of_rank(draw, max_m=6):
    m = draw(st.integers(1, max_m))
    r = draw(st.integers(0, m))
    U = [[draw(rat) for _ in range(r)] for _ in range(m)]
    V = [[draw(rat) for _ in range(m)] for _ in range(r)]
    return qmat([[sum((U[i][k] * V[k][j] for k in range(r)), F(0)) for j in range(m)] for i in range(m)])


def test_fixture_factorizations_match_spec():
    """SPEC §2.5 B1/B2 Lemma 9 factors."""
    J2 = qmat([[1, 1], [1, 1]])
    E1, piv, E2 = lower_bruhat(J2)
    assert (E1, piv, E2) == (qmat([[1, 0], [1, 1]]), ((0, 1),), qmat([[1, 0], [1, 1]]))
    E1, piv, E2 = lower_bruhat(neg(J2))
    assert (E1, piv, E2) == (qmat([[-1, 0], [-1, 1]]), ((0, 1),), qmat([[1, 0], [1, 1]]))
    assert lower_bruhat(qmat([[1, 0], [0, 0]]))[1] == ((0, 0),)
    assert lower_bruhat(qmat([[0, 0], [0, 1]]))[1] == ((1, 1),)
    assert lower_bruhat(identity(2))[1] == ((0, 0), (1, 1))
    f = lower_bruhat_factors(qmat([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]))
    assert f.E1 == qmat([[F(1, 2), 0], [F(1, 2), 1]]) and f.E1inv == qmat([[2, 0], [-1, 1]])


def test_zero_matrix():
    E1, piv, E2 = lower_bruhat(zeros(3))
    assert E1 == identity(3) and E2 == identity(3) and piv == ()


@given(matrix_of_rank())
def test_lower_bruhat_properties(A):
    """A = E1 Pi E2, E1/E2 invertible lower triangular, rank(A) pivots, at most one per row/column, and the first
    pivot is the rightmost nonzero entry of the topmost nonzero row (SPEC §3.1)."""
    f = lower_bruhat_factors(A)
    m = len(A)
    assert bruhat_product(f.E1, f.pivots, f.E2) == A
    assert mul(mul(f.E1, partial_permutation(f.pivots, m)), f.E2) == A
    assert all(map(is_invertible_lower, (f.E1, f.E2, f.E1inv, f.E2inv)))
    assert mul(f.E1, f.E1inv) == identity(m) and mul(f.E2, f.E2inv) == identity(m)
    assert len(f.pivots) == rank_Q(A)
    assert len({i for i, _ in f.pivots}) == len({j for _, j in f.pivots}) == len(f.pivots)
    if f.pivots:
        i0 = min(i for i in range(m) if any(A[i]))
        j0 = max(j for j in range(m) if A[i0][j])
        assert f.pivots[0] == (i0, j0)


@given(matrix_of_rank())
def test_rank_inverse_nullspace(A):
    m = len(A)
    r = rank_Q(A)
    ns = nullspace(A)
    assert len(ns) == m - r
    assert all(all(x == 0 for x in mat_vec(A, v)) for v in ns)
    if r == m:
        assert mul(A, inverse(A)) == identity(m)
    else:
        with pytest.raises(ValueError):
            inverse(A)


def test_basic_algebra():
    A = qmat([[1, 2], [3, 4]])
    assert sub(A, A) == zeros(2)
    assert kron(identity(1), A) == A
    assert len(kron(A, identity(3))) == 6 and is_lower(identity(4))
    assert not is_lower(A)


def test_primes():
    assert least_odd_prime_avoiding([1, -1]) == 3
    assert least_odd_prime_avoiding([3, 2, 5 * 7]) == 11
    assert least_odd_prime_avoiding([9, 25]) == 7
    assert [is_odd_prime(n) for n in (2, 3, 9, 11)] == [False, True, False, True]
    with pytest.raises(ValueError):
        least_odd_prime_avoiding([0])


def test_choose_prime_fixtures():
    from subnlogn.net.fixtures import fixture_B1, fixture_B2
    assert choose_prime(fixture_B1()) == 3
    assert choose_prime(fixture_B2()) == 3


def test_choose_prime_avoids_denominators_and_diagonals():
    from subnlogn.net.fixtures import fixture_B2
    from dataclasses import replace
    net = fixture_B2()
    g = list(net.gates)
    g[1] = replace(g[1], frame=qmat([[F(1, 3), 0], [0, F(5, 1)]]))
    assert choose_prime(replace(net, gates=tuple(g))) == 7   # 3: denominator, 5: diagonal numerator


def test_specialize():
    assert specialize(F(1, 2), 9) == 5 and specialize(F(-1, 2), 3) == 1
    assert specialize_matrix(qmat([[F(1, 2), -1]]), 27) == ((14, 26),)
