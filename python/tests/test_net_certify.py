"""Tests for net.certify: the SPEC §2.7 expected-numbers table, thresholds, signed savings (h = 100
is the real network), tau test, guard constants, q_radix = 5,
and failure on broken descriptors."""

from fractions import Fraction

import pytest

from subnlogn.net.certify import certify_triple, first_saving_h, guard_constants, log_bound
from subnlogn.net.errors import NotAnInterface
from subnlogn.net.triple import TripleNetwork, triple_params

# SPEC §2.7 expected numbers (every integer of the table)
TABLE = {
    21: dict(v=1330, N=2352637000, m=9261, I=5306700, z_b=459, z_c=870, W_b=3244397863700, W_c=6145204591400,
             LbN=Fraction(189, 190), LcN=Fraction(99, 95), s_b=30046370943598100, s_c=56910739919072200,
             sav_b=-2327872400, sav_c=-198116800, eta_b=None, eta_c=None, nu=11, C1=20, C0_digits=87),
    27: dict(v=2925, N=25025203125, m=19683, I=25666875, z_b=828, z_c=2096, W_b=62213347974375,
             W_c=157409246328750, LbN=Fraction(243, 325), LcN=Fraction(252, 325), s_b=1224545340576723750,
             s_c=3098286184246695000, sav_b=-12397100625, sav_c=11242091250, eta_b=None,
             eta_c=Fraction(73, 20118578229), nu=11, C1=20, C0_digits=96),
    100: dict(v=161700, N=4227952113000000, m=1000000, I=78440670000, z_b=13968, z_c=147731,
              W_b=177176569091445000000, W_c=1873807244643542670000, LbN=Fraction(100, 539), LcN=Fraction(101, 539),
              s_b=177176569088785861287000000, s_c=1873807244636671267308000000, sav_b=2659138713000000,
              sav_c=6871402692000000, eta_b=Fraction(339, 22587335000000), eta_c=Fraction(73, 19906842167500),
              nu=11, C1=20, C0_digits=140),
}


@pytest.mark.parametrize("h", sorted(TABLE))
def test_expected_numbers_table(h):
    t = TABLE[h]
    cb = certify_triple(h, "bit", dense_scalar=False)
    cc = certify_triple(h, "complex", dense_scalar=False)
    for c in (cb, cc):
        p = c.params
        assert (p.v, p.N, p.m, p.I, c.z_b, c.z_c) == (t["v"], t["N"], t["m"], t["I"], t["z_b"], t["z_c"])
    assert (cb.params.W, cc.params.W) == (t["W_b"], t["W_c"])
    assert (cb.L_over_N, cc.L_over_N) == (t["LbN"], t["LcN"])
    assert (cb.params.s, cc.params.s) == (t["s_b"], t["s_c"])
    assert (cb.rank_sum, cc.rank_sum) == (t["s_b"], t["s_c"])          # certified class-by-class
    assert (cb.saving, cc.saving) == (t["sav_b"], t["sav_c"])
    for c, key in ((cb, "eta_b"), (cc, "eta_c")):
        if t[key] is None:
            assert c.eta < 0 and not c.saves
        else:
            assert c.eta == t[key] and c.saves
    g = cc.guard
    assert (g.nu, g.C1, g.C0_digits) == (t["nu"], t["C1"], t["C0_digits"])
    assert t["m"] ** 10 < g.B < t["m"] ** 11
    assert cb.guard is None and cb.q_radix == 5 and cc.q_radix is None and "brute-force-confirmed" in cb.q_radix_provenance
    assert cb.prime_grammar["9a"]["smallest_odd_prime"] == 5 and cc.prime_grammar is None
    assert len(cb.steps) == 10 and len(cc.steps) == 9


def test_h100_guard_C0_value():
    g = guard_constants(triple_params(100, "complex"))
    assert str(g.C0)[:4] == "2269" and g.E == 64 * (1873807244643542670000 + 10 ** 6 + 1) ** 3


def test_thresholds():
    """Bit first saves at h = 39 (eta_b = 1/236530063575), complex at h = 22 (eta_c = 1/1147871098) (SPEC §2.7)."""
    assert first_saving_h("bit") == 39 and first_saving_h("complex") == 22
    assert certify_triple(39, "bit", dense_scalar=False).eta == Fraction(1, 236530063575)
    assert certify_triple(22, "complex", dense_scalar=False).eta == Fraction(1, 1147871098)
    assert triple_params(38, "bit").saving < 0 and triple_params(21, "complex").saving < 0
    for h in range(7, 120):
        if h != 9:
            assert (triple_params(h, "bit").saving > 0) == (h * h - 39 * h + 2 > 0)
        assert (triple_params(h, "complex").saving > 0) == (h * h - 21 * h - 16 > 0)


@pytest.mark.parametrize("h", [21, 22, 27, 39, 40, 100])
def test_open1_signed_savings(h):
    """Certify the triple construction at these h and report savings with signs (h = 100 is the
    real network; the others are informational)."""
    cb, cc = certify_triple(h, "bit", dense_scalar=False), certify_triple(h, "complex", dense_scalar=False)
    assert cb.saves == (h >= 39) and cc.saves == (h >= 22)
    assert cb.saving == cb.params.W * cb.params.m - cb.params.s
    for c in (cb, cc):
        assert c.tau_ok == c.saves                       # with tau = 1 - 2^-50 every saving network passes
        assert all(r.direction >= 0 or (r.wire, r.edge) == ("center", "3->4") for r in c.classes)
        assert c.abs_dim_change == c.params.W * c.params.m - 2 * c.params.N + 2 * c.params.L


def test_tau_exponent_is_configurable():
    """tau = 1 - 2^-40 (retuned): the h = 100 networks fail the integer test, h = 40 bit passes."""
    assert log_bound(10 ** 6) == 20 and log_bound(9261) == 20 and log_bound(2 ** 30) == 31
    from subnlogn.net.certify import step7_savings
    assert not step7_savings(triple_params(100, "bit"), 40)["tau_ok"]
    assert not step7_savings(triple_params(100, "complex"), 40)["tau_ok"]
    assert step7_savings(triple_params(40, "bit"), 40)["tau_ok"]
    assert certify_triple(40, "bit", tau_exp=40, dense_scalar=False).tau_ok
    c = certify_triple(100, "bit")
    assert c.tau_ok and c.saving * 2 ** 50 >= 20 * c.params.W * c.params.m


@pytest.mark.parametrize("kind", ["bit", "complex"])
def test_certificate_rows_h21(kind):
    c = certify_triple(21, kind, dense_scalar=False)
    dec = {(r.stage, r.wire, r.edge, r.dim) for r in c.classes if r.direction < 0}
    assert dec == {(j, "center", "3->4", 21) for j in (1, 2, 3)}
    assert all(r.dim == r.expected_dim for r in c.classes)
    src = [r for r in c.classes if (r.stage, r.wire, r.edge) == (1, "X", "in->2")][0]
    assert src.dim == 0 and src.rank == (1 if kind == "bit" else 0)   # the 2 P_{U_a} edge [Pr L1160-1165]
    assert "omega" in c.endpoints if kind == "complex" else True


@pytest.mark.parametrize("kind", ["bit", "complex"])
@pytest.mark.parametrize("h", [7, 8, 10])
def test_small_h_with_dense_scalar(kind, h):
    c = certify_triple(h, kind)
    assert c.scalar["dense"] and c.rank_sum == c.params.s and not c.saves


@pytest.mark.parametrize("kind", ["bit", "complex"])
def test_step10_dense_spot_h7(kind):
    c = certify_triple(7, kind, dense_spot=1)
    assert c.dense["edges"] > 40 and "10 dense spot check" in c.steps


def test_no_dense_materialization_for_large_h(monkeypatch):
    import subnlogn.net.triple_dense as td

    def boom(*a, **k):
        raise AssertionError("dense materialization attempted")
    monkeypatch.setattr(td.DenseTriple, "__init__", boom)
    certify_triple(100, "complex", dense_scalar=False)
    with pytest.raises(ValueError):
        certify_triple(21, "bit", dense_scalar=False, dense_spot=1)


class _WrongSign(TripleNetwork):
    def route_sign(self, rid):
        return 1


class _WrongPhase(TripleNetwork):
    def post_ipow(self, rid):
        return 25 if self.N <= rid < 2 * self.N else 0


class _WrongSink(TripleNetwork):
    def sink_frame(self, rid):
        from subnlogn.net.symbolic import FULL_LABEL, SymFrame
        return SymFrame(1, FULL_LABEL)


class _WrongJ(TripleNetwork):
    def gate_row(self, gid, out_role):
        row = super().gate_row(gid, out_role)
        if self.gate_info(gid).op == "+J" and len(row) > 1:
            row = {k: (v if k == out_role else v * 2) for k, v in row.items()}
        return row


@pytest.mark.parametrize("cls,kind", [(_WrongSign, "complex"), (_WrongPhase, "complex"), (_WrongSink, "bit"),
                                      (_WrongSink, "complex"), (_WrongJ, "complex")])
def test_broken_descriptors_fail(cls, kind):
    with pytest.raises(NotAnInterface):
        certify_triple(8, kind, network=cls(8, kind))


@pytest.mark.slow
@pytest.mark.parametrize("kind", ["bit", "complex"])
@pytest.mark.parametrize("h", [21, 22])
def test_dense_invocation_check_default(kind, h):
    """SPEC §2.7 step 2: dense v x v invocation check by default when v <= 2024."""
    assert certify_triple(h, kind).scalar["dense"]


@pytest.mark.slow
@pytest.mark.parametrize("kind", ["bit", "complex"])
@pytest.mark.parametrize("h", [8, 10])
def test_step10_dense_spot_slow(kind, h):
    assert certify_triple(h, kind, dense_spot=1, seed=h).dense["edges"] > 40


# ----------------------------------------------------------------------------------------------- sharp log bound
from subnlogn.net.certify import ln_enclosure, tau_test  # noqa: E402

SHARP_PASS = {40: {(22, "complex"), (27, "complex"), (39, "complex"), (40, "bit"), (40, "complex"), (100, "bit")},
              42: {(22, "complex"), (27, "complex"), (39, "bit"), (39, "complex"), (40, "bit"), (40, "complex"),
                   (100, "bit"), (100, "complex")}}


def test_ln_enclosure_is_certified():
    """Outward rational enclosure of ln m (rigorous ln 2 + exact atanh series with tail bound); mpmath only as a
    non-authoritative cross-check."""
    import mpmath
    mpmath.mp.prec = 300
    for m in (1, 2, 3, 7, 9261, 10648, 19683, 59319, 64000, 10 ** 6, 2 ** 20, 2 ** 20 + 1, 3 ** 40, 10 ** 30):
        lo, hi = ln_enclosure(m)
        assert lo <= hi and hi - lo < Fraction(1, 2 ** 80)
        t = mpmath.log(m)
        assert mpmath.mpf(lo.numerator) / lo.denominator <= t <= mpmath.mpf(hi.numerator) / hi.denominator
    assert ln_enclosure(1) == (0, 0)
    L = log_bound(10 ** 6, "sharp")
    assert Fraction(138155105579, 10 ** 10) < L < Fraction(138155105580, 10 ** 10) < 14
    with pytest.raises(ValueError):
        log_bound(10, "fuzzy")


def test_spec_walsh_inequalities():
    """SPEC_WALSH §1.3: 339 2^40 > 14 * 22587335000000 and 73 2^42 > 14 * 19906842167500 (ln 10^6 < 14), i.e.
    tau = 1 - 2^-40 for the h = 100 bit network and sigma = 1 - 2^-42 for the complex one."""
    assert 339 * 2 ** 40 == 372734441816064 > 14 * 22587335000000 == 316222690000000
    assert 73 * 2 ** 42 == 321057395310592 > 14 * 19906842167500 == 278695790345000
    eb, ec = triple_params(100, "bit").eta, triple_params(100, "complex").eta
    assert (eb, ec) == (Fraction(339, 22587335000000), Fraction(73, 19906842167500))
    assert eb * 2 ** 40 > 14 > log_bound(10 ** 6, "sharp") and ec * 2 ** 42 > 14
    cb = certify_triple(100, "bit", tau_exp=40, log_bound="sharp", dense_scalar=False)
    cc = certify_triple(100, "complex", tau_exp=42, log_bound="sharp", dense_scalar=False)
    assert cb.tau_ok and cc.tau_ok and cb.log_mode == cc.log_mode == "sharp" and cb.tau_margin > 0
    assert not certify_triple(100, "complex", tau_exp=40, log_bound="sharp", dense_scalar=False).tau_ok


@pytest.mark.parametrize("h", [21, 22, 27, 39, 40, 100])
def test_sharp_tau_table(h):
    for kind in ("bit", "complex"):
        p = triple_params(h, kind)
        for e in (40, 42):
            ok, margin = tau_test(p, e, "sharp")
            assert ok == ((h, kind) in SHARP_PASS[e]) == (margin >= 0 and p.saving > 0)
        assert tau_test(p, 50, "crude")[0] == tau_test(p, 50, "sharp")[0] == (p.saving > 0)
