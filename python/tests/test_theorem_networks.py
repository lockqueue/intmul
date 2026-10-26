"""The theorem configuration references the REAL networks: every faithful schedule names the h = 100
triple networks of SPEC §2.4, which resolve lazily to ``TripleNetwork`` descriptors that agree with their
SPEC §2.7 certificates and are never executed; the SPEC §2.5 fixtures C1 / B1 remain the test policies' networks.
"""

import tracemalloc
from fractions import Fraction

import pytest

import subnlogn.bridge.bridge_dft as bridge_mod
import subnlogn.multiply as mm
import subnlogn.net as net_pkg
from conftest import make_ctx
from subnlogn.bridge.movement import mover_from_schedule
from subnlogn.context import Ctx
from subnlogn.m6.engine import (compiled_fixture, engine_from_schedule, movement_from_schedule, network_descriptor,
                                real_network_params, require_executable)
from subnlogn.net import CompiledNetwork, NotAdmissible, RealNetworkNotExecutable
from subnlogn.net.certify import certify_triple
from subnlogn.net.triple import TripleNetwork
from subnlogn.schedule import REAL_NET_BIT, REAL_NET_CX, Schedule, faithful_schedule, test_policy, test_schedule
from subnlogn.theorem import ROW_PRINTED, THEOREM_ROWS, theorem_shape

ROLE_KIND = (("net_cx", "complex"), ("net_bit", "bit"))
NOT_EXECUTABLE = r"real networks are not executable at feasible sizes \(m ≈ 10\^6\)"


def test_faithful_schedules_name_the_real_networks():
    """All three faithful rows (and the default context) name the h = 100 networks, net_cx complex and net_bit bit;
    the test policies and the Schedule defaults keep the SPEC §2.5 fixtures C1 / B1."""
    assert (REAL_NET_CX, REAL_NET_BIT) == ("triple:100:complex", "triple:100:bit")
    for row in THEOREM_ROWS:
        s = faithful_schedule(row)
        assert (s.net_cx, s.net_bit) == (REAL_NET_CX, REAL_NET_BIT)
        for role, kind in ROLE_KIND:
            assert real_network_params(getattr(s, role)) == (100, kind)
    assert (Ctx().schedule.net_cx, Ctx().schedule.net_bit) == (REAL_NET_CX, REAL_NET_BIT)
    for s in (test_policy(4), test_policy(3, middle="walsh"), test_schedule(), Schedule(name="x")):
        assert (s.net_cx, s.net_bit) == ("C1", "B1")
        assert real_network_params(s.net_cx) is None and real_network_params(s.net_bit) is None


def test_resolution_builds_only_the_lazy_descriptor(monkeypatch):
    """Resolving a real-network name builds the TripleNetwork descriptor and nothing else: no network compilation,
    a few hundred bytes (an object with m = 10^6 entries would take megabytes), cached by name.  Fixture names still
    resolve to compiled fixtures; malformed or inadmissible names fail loudly."""
    def boom(*a, **k):
        raise AssertionError("a network was compiled while resolving a real-network name")

    cache = {}
    with monkeypatch.context() as mp:
        mp.setattr(net_pkg, "compile_network", boom)
        tracemalloc.start()
        try:
            descs = {kind: network_descriptor(getattr(faithful_schedule(), role), cache) for role, kind in ROLE_KIND}
            peak = tracemalloc.get_traced_memory()[1]
        finally:
            tracemalloc.stop()
    assert peak < 64 * 1024
    for kind, d in descs.items():
        assert type(d) is TripleNetwork and (d.h, d.kind, d.m) == (100, kind, 10 ** 6)
        assert network_descriptor(f"triple:100:{kind}", cache) is d
    assert isinstance(network_descriptor("C1", cache), CompiledNetwork)
    with pytest.raises(ValueError, match="malformed"):
        network_descriptor("triple:x:bit")
    with pytest.raises(NotAdmissible):
        network_descriptor("triple:9:bit")


@pytest.mark.parametrize("kind", ["complex", "bit"])
def test_descriptor_agrees_with_certificate(kind):
    """The resolved descriptor's data is certify_triple(100, kind)'s (SPEC §2.7, computed independently): closed-form
    parameters, signed saving, eta, the saving at the printed tau = 1 - 2^-50, q_radix (5 for bit); for the
    complex network the guard's C1 = max(20, nu + 3) is the printed row's C1 = 20 (~1.9 s per kind)."""
    name = REAL_NET_CX if kind == "complex" else REAL_NET_BIT
    d = network_descriptor(name)
    cert = certify_triple(100, kind)
    assert d.params == cert.params and (d.m, d.W, d.s) == (cert.params.m, cert.params.W, cert.params.s)
    assert (d.params.saving, d.params.eta) == (cert.saving, cert.eta) and cert.saves and cert.saving > 0
    assert cert.tau_ok and 1 - Fraction(1, 2 ** cert.tau_exp) == ROW_PRINTED.tau
    assert (d.q_radix, d.q_radix_provenance) == (cert.q_radix, cert.q_radix_provenance)
    assert d.q_radix == (5 if kind == "bit" else None)
    if kind == "complex":
        assert cert.guard.C1 == ROW_PRINTED.C1 == 20
    else:
        assert cert.guard is None


def test_executing_resolvers_refuse_real_networks():
    """compiled_fixture, the Prop 14 engine, Lemma 16's movement and the bridge mover raise for real networks."""
    with pytest.raises(RealNetworkNotExecutable, match=NOT_EXECUTABLE):
        compiled_fixture(REAL_NET_BIT)
    with pytest.raises(RealNetworkNotExecutable, match="TripleNetwork\\(h=100, kind='complex'\\)"):
        require_executable(REAL_NET_CX)
    require_executable("C1")
    ctx = make_ctx(faithful_schedule().with_(prop14_layer="network", bridge_movement="lemma12"))
    for resolve in (lambda: engine_from_schedule(ctx, 2), lambda: movement_from_schedule(ctx),
                    lambda: mover_from_schedule(ctx)):
        with pytest.raises(RealNetworkNotExecutable, match=NOT_EXECUTABLE):
            resolve()


@pytest.mark.parametrize("row", list(THEOREM_ROWS))
def test_forced_theorem_branch_with_real_networks_raises(monkeypatch, row):
    """Force the (unreachable) theorem branch with an UNMODIFIED faithful schedule (the row's theorem-mode policy, the
    real networks): RealNetworkNotExecutable is raised before the bridge starts -- bridge_dft is never called and no
    transform counter moves.  With only net_cx replaced by a fixture, the bit network is refused the same way."""
    monkeypatch.setattr(mm, "theorem_mode_shape", lambda K, r: theorem_shape(K, eps=Fraction(1, 2),
                                                                              c=Fraction(1, 2)))

    def spy(*a, **k):
        raise AssertionError("bridge_dft ran with a real network")

    monkeypatch.setattr(bridge_mod, "bridge_dft", spy)
    for sched, refused in ((faithful_schedule(row), REAL_NET_CX),
                           (faithful_schedule(row).with_(net_cx="C1"), REAL_NET_BIT)):
        ctx = make_ctx(sched.with_(mul_direct_bits=0))
        with pytest.raises(RealNetworkNotExecutable, match=NOT_EXECUTABLE) as exc:
            mm.multiply((1 << 95) + 3, (1 << 94) + 5, ctx)
        assert repr(refused) in str(exc.value)
        c = ctx.inst.counts
        assert c.get("multiply.theorem_mode", 0) == 0 and c.get("multiply.fallback_2d", 0) == 0
        assert {k.split(".")[0] for k in c} <= {"multiply", "python"}


def test_schedule_checks_real_network_roles():
    """Schedule.__post_init__: a real-network name must match its role (complex in net_cx, bit in net_bit), be
    well formed and admissible (SPEC §2.4); also through with_ / replace.  Fixture names are not affected."""
    with pytest.raises(ValueError, match="net_cx needs a complex network"):
        Schedule(name="x", net_cx=REAL_NET_BIT)
    with pytest.raises(ValueError, match="net_bit needs a bit network"):
        Schedule(name="x", net_bit=REAL_NET_CX)
    with pytest.raises(ValueError, match="net_cx needs a complex network"):
        faithful_schedule("walsh46").with_(net_cx=REAL_NET_BIT, net_bit=REAL_NET_CX)
    for bad in ("triple:1e2:complex", "triple:100", "triple:100:complex:x"):
        with pytest.raises(ValueError, match="malformed"):
            Schedule(name="x", net_cx=bad)
    with pytest.raises(NotAdmissible):
        Schedule(name="x", net_bit="triple:9:bit")
    s = Schedule(name="x", net_cx="triple:21:complex", net_bit="triple:22:bit")
    assert (s.net_cx, s.net_bit) == ("triple:21:complex", "triple:22:bit")
    assert (test_policy(4, net_bit="B2q5", net_cx="C2").net_cx, faithful_schedule().with_(net_bit="B1").net_bit) == \
        ("C2", "B1")
