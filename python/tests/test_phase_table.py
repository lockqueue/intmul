"""Tests for the disk-preserving phase table and the chirp index (SPEC §5.9; Pr §9.4 L4308-4309,
§9.5 L4344-4360): disk property, error < 2 2^-p against mpmath at p + 200 bits (and the stronger
truncation property |component| <= |true component|), exact quarter turns, symmetries."""

from fractions import Fraction

import pytest
from hypothesis import given, settings, strategies as st
from mpmath import mp, mpf

from subnlogn import certified as C
from subnlogn.certified import chirp_index, phase_table
from subnlogn.ring import in_disk

HI = 200


@pytest.fixture(autouse=True)
def _no_fallback():
    yield
    assert C.fallback_events() == [], f"certified fallback taken: {C.fallback_events()}"


def check_entry(z, k, r, p):
    """Disk grid, error < 2 2^-p, and each component = trunc toward zero of the exact one."""
    assert in_disk(z[0], z[1], p)
    with mp.workprec(p + HI):
        c, s = mp.cospi(mpf(k) / r), mp.sinpi(mpf(k) / r)
        for n, x in zip(z, (c, s)):
            y = mp.ldexp(x, p)
            assert n == (int(mp.floor(y)) if y >= 0 else -int(mp.floor(-y)))  # Q_p truncation
            assert abs(n) <= abs(y)
        err = abs(mp.mpc(mp.ldexp(z[0], -p), mp.ldexp(z[1], -p)) - mp.mpc(c, s))
        assert err < mp.ldexp(2, -p)
        assert err < mp.sqrt(2) * mp.ldexp(1, -p)  # truncation of the exact value (26)


@pytest.mark.parametrize("r", [1, 2, 4, 8, 16, 64, 256])
@pytest.mark.parametrize("p", [1, 2, 10, 53, 200])
def test_phase_table_entries(r, p):
    th = phase_table(r, p)
    assert len(th) == 2 * r and all(type(a) is int and type(b) is int for a, b in th)
    one = 1 << p
    for k, z in enumerate(th):
        check_entry(z, k, r, p)
        assert th[(k + r) % (2 * r)] == (-z[0], -z[1])               # theta[k + r] = -theta[k]
        assert th[(2 * r - k) % (2 * r)] == (z[0], -z[1])             # theta^-_k = conj(theta_k)
        if (2 * k) % r == 0:                                          # multiples of r/2: exact
            assert z == [(one, 0), (0, one), (-one, 0), (0, -one)][(2 * k // r) % 4]


@settings(max_examples=60)
@given(st.integers(0, 11), st.integers(1, 400), st.data())
def test_phase_table_random_entries(l, p, data):
    r = 1 << l
    th = phase_table(r, p)
    for k in data.draw(st.lists(st.integers(0, 2 * r - 1), min_size=1, max_size=6)):
        check_entry(th[k], k, r, p)


def test_phase_table_validation_and_copy():
    with pytest.raises(ValueError):
        phase_table(3, 10)
    with pytest.raises(ValueError):
        phase_table(4, 0)
    t1 = phase_table(8, 30)
    t1[0] = (0, 0)  # the returned list is a copy of the cached table
    assert phase_table(8, 30)[0] == (1 << 30, 0)


@settings(max_examples=60)
@given(st.integers(1, 9), st.integers(1, 4), st.data())
def test_chirp_index(l, d, data):
    """a_j = exp(pi i sum_i j_i^2 / t_i) = zeta^{E_j} (SPEC §5.9, R2) with t_i in {r/2, r}; t-periodic
    in each j_i (t_i even); the phase-table entry approximates a_j within 2 2^-p."""
    r = 1 << l
    t = [data.draw(st.sampled_from([r // 2, r] if r >= 4 else [r])) for _ in range(d)]
    j = [data.draw(st.integers(-3 * ti, 3 * ti)) for ti in t]
    E = chirp_index(j, t, r)
    assert 0 <= E < 2 * r
    assert (E - sum(Fraction(ji * ji * r, ti) for ji, ti in zip(j, t))) % (2 * r) == 0
    assert chirp_index([ji % ti for ji, ti in zip(j, t)], t, r) == E
    p = 60
    z = phase_table(r, p)[E]
    with mp.workprec(p + HI):
        a = mp.expjpi(sum(mpf(ji * ji) / ti for ji, ti in zip(j, t)))
        assert abs(mp.mpc(mp.ldexp(z[0], -p), mp.ldexp(z[1], -p)) - a) < mp.ldexp(2, -p)
    with pytest.raises(ValueError):
        chirp_index([1], [3], 8)


def test_phase_table_forced_disk_round_fallback(monkeypatch):
    """With the Ziv cap forced down to p + 8, some truncations stay undecided; SPEC disk_round of the
    final enclosure is then used: still disk-preserving, |component| <= true, error < 2 2^-p, and
    every such event is recorded (then the caches and the record are cleared)."""
    r, p = 1024, 30
    C._disk_octant.cache_clear()
    C._phase_table_cached.cache_clear()
    monkeypatch.setattr(C, "prec_cap", lambda q: q + 8)
    try:
        with pytest.warns(C.CertifiedFallbackWarning):
            th = phase_table(r, p)
        assert C.fallback_events() and all(e[0] == "phase_table" for e in C.fallback_events())
        with mp.workprec(p + HI):
            for k, z in enumerate(th):
                assert in_disk(z[0], z[1], p)
                c, s = mp.cospi(mpf(k) / r), mp.sinpi(mpf(k) / r)
                assert abs(z[0]) <= abs(mp.ldexp(c, p)) and abs(z[1]) <= abs(mp.ldexp(s, p))
                err = abs(mp.mpc(mp.ldexp(z[0], -p), mp.ldexp(z[1], -p)) - mp.mpc(c, s))
                assert err < mp.ldexp(2, -p)
    finally:
        C.reset_fallback_events()
        C._disk_octant.cache_clear()
        C._phase_table_cached.cache_clear()
