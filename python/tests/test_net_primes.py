"""The primes of the Lemma 9 factors of the bit triple network are
{2, 3}, q_radix = 5.  9a prime alphabet, 9b edge grammar per stage and class (h in {7, 21, 100}), 9c exhaustive
ordered primitives and gadgets with the literal lower_bruhat (h = 7, 8 fast; h = 10, 11, 12 slow), 9d one dense
edge per class at h = 7 (slow), plus full edge matrices of random roles and mixed edges."""

from fractions import Fraction

import pytest

from subnlogn.net.certify import certify_triple
from subnlogn.net.primes import (brute_force_primitives, certify_prime_alphabet, edge_grammar, factor_primes,
                                 full_edge_primes, grammar_certificate, prime_factors, smooth23, unit23)
from subnlogn.net.qmatrix import qmat
from subnlogn.net.triple import TripleNetwork


def test_helpers():
    assert prime_factors(360) == {2, 3, 5} and prime_factors(1) == set() and prime_factors(-49) == {7}
    assert smooth23(216) and not smooth23(10) and not smooth23(0)
    assert unit23(Fraction(-1, 216)) and not unit23(Fraction(5, 12)) and not unit23(0)


def test_factor_primes_detects_other_primes():
    """A matrix whose Lemma 9 factors need 5 is reported (the check is not vacuous)."""
    pr, r = factor_primes(qmat([[2, 1], [1, 3]]), mod_exps=())
    assert 5 in pr and r == 2
    with pytest.raises((AssertionError, ValueError)):             # a factor needs 1/5: no specialization mod 5
        factor_primes(qmat([[2, 1], [1, 3]]), mod_exps=(1,))


PARTS = {7: 1, 8: 4, 10: 4, 11: 8, 12: 8}
EXPECT = {7: (35, 630), 8: (56, 1680), 10: (120, 7560), 11: (165, 13860), 12: (220, 23760)}


def _check_part(h, part):
    rep = brute_force_primitives(h, part=part, parts=PARTS[h])      # mod 5^b, b in {1, 2, 3}
    assert rep.primes <= {2, 3}, rep.primes
    return rep


@pytest.mark.parametrize("h,part", [(7, 0)] + [(8, k) for k in range(4)])
def test_9c_brute_force_fast(h, part):
    """SPEC v1.2 §2.7 step 9c (fast part): literal lower_bruhat on every L_T, I - L_T (all triples) and every
    I - L_S - L_T and gadget [[L_S, -K], [0, I - L_T]] (all ordered neighboring pairs); denominators and diagonal
    numerators {2, 3}-smooth; identities hold mod 5, 25, 125 (certificate steps 1-5)."""
    rep = _check_part(h, part)
    if PARTS[h] == 1:
        v, n = EXPECT[h]
        assert rep.counts == {"L_T": v, "I-L_T": v, "I-L_S-L_T": n, "gadget": n} and rep.primes == {2, 3}


@pytest.mark.slow
@pytest.mark.parametrize("h,part", [(h, k) for h in (10, 11, 12) for k in range(PARTS[h])])
def test_9c_brute_force_slow(h, part):
    """Step 9c (slow part): h = 10, 11, 12, exhaustive, split into parts."""
    _check_part(h, part)


def test_mixed_edges_sample_h7():
    """The two-factor mixed edge I (x) D0 - P0 (x) K (49 x 49), a random sample of 40 at h = 7."""
    rep = brute_force_primitives(7, mixed=40, primitives=False, mod_exps=(3,))
    assert rep.counts == {"mixed": 40} and rep.primes <= {2, 3} and rep.max_dim == 49


@pytest.mark.parametrize("h", [7, 8, 10, 21, 100])
def test_prime_alphabet_certificate(h):
    assert certify_prime_alphabet(h) == {"forbidden_primes": {2, 3}, "smallest_odd_prime": 5}


@pytest.mark.parametrize("h", [7, 21, 100])
def test_9b_edge_grammar_per_stage_and_class(h):
    """Step 9b: one symbolic instance of every (stage, edge class) of the bit network rewrites (up to sign) to the
    proved edge grammar: tensor products of P, I - P, L_t, I - L_t, I - L_S - L_T, I; the mixed edge
    I (x) D0 - P0 (x) K (side 0->2 at stages 2, 3); the source edge 2 P_{U_a} (not zero)."""
    g = grammar_certificate(TripleNetwork(h, "bit"))
    terms = g["terms"]
    assert terms["2*P_U"] == 1 and sum(v for k, v in terms.items() if k.startswith("mixed")) == 2
    assert sum(terms.values()) == 2 * 13 + 3 * 2 * 5


def test_full_edges_h7_scratch_and_data():
    """Certificate step 6 at h = 7: literal factorizations of materialized 343 x 343 edge matrices of a center, a
    side and an X data wire; dense rank = symbolic rank; prime support {2, 3} (frames included)."""
    tn = TripleNetwork(7, "bit")
    fixed = ((2, (0, 2, 4)), (3, (1, 3, 5)))
    roles = [tn.role_id(("C", 1, fixed, 3)), tn.role_id(("A", 1, fixed, (0, 1, 2), (2, 3, 4))),
             tn.role_id(("X", ((0, 3, 6), (1, 2, 5), (2, 4, 6))))]
    primes = set()
    for rid in roles:
        for cls, sym, rank, pr in full_edge_primes(tn, rid):
            assert sym == rank, cls
            primes |= pr
    assert primes == {2, 3}


def test_certificate_records_q5():
    from subnlogn.net.qmatrix import choose_prime
    c = certify_triple(100, "bit", dense_scalar=False)
    assert c.q_radix == 5 and c.q_radix_provenance == ("certified: the two independent enumerations agree; "
                                                        "brute-force-confirmed at h <= 12")
    assert c.prime_grammar["9a"]["smallest_odd_prime"] == 5 and c.prime_grammar["9b"]["2*P_U"] == 1
    assert any(st.startswith("9a") for st in c.steps) and any(st.startswith("9b") for st in c.steps)
    assert certify_triple(100, "complex", dense_scalar=False).q_radix is None
    assert choose_prime(TripleNetwork(100, "bit")) == 5 and choose_prime(TripleNetwork(7, "bit")) == 5
    c7 = certify_triple(7, "bit", prime_brute_force=True)
    assert c7.prime_grammar["9c"]["primes"] == [2, 3]


@pytest.mark.slow
def test_tensor_lines_h7():
    """Two-coordinate tensor-line projections L_S (x) L_T and their complements (49 x 49), all ordered pairs."""
    rep = brute_force_primitives(7, tensor_lines=True, mod_exps=())
    assert rep.counts["P2"] == rep.counts["I-P2"] == 35 * 35 and rep.primes == {2, 3}


@pytest.mark.slow
def test_9d_one_dense_edge_per_class_h7():
    """SPEC v1.2 §2.7 step 9d: at h = 7 one materialized 343 x 343 edge matrix per (stage, edge class), literal
    lower_bruhat; dense rank = symbolic rank; prime support {2, 3}."""
    c = certify_triple(7, "bit", prime_dense=True)
    assert c.prime_grammar["9d"]["primes"] == [2, 3] and c.prime_grammar["9d"]["classes"] >= 3 * 9 + 6


@pytest.mark.slow
def test_full_edges_h7_all_classes():
    from subnlogn.net.triple_dense import sample_roles
    tn = TripleNetwork(7, "bit")
    classes, primes = set(), set()
    for rid in sample_roles(tn, 1, seed=11):
        for cls, sym, rank, pr in full_edge_primes(tn, rid):
            assert sym == rank
            classes.add(cls)
            primes |= pr
    assert primes == {2, 3} and len(classes) >= 3 * 9 + 6
