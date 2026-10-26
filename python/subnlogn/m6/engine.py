"""Construction of the Proposition 14 engine context (SPEC v1.1 §4.0: ``ctx`` carries d, net_cx,
net_bit, policy, the guard and the row field) with the faithful basis changes: every P_M row
addition is one Lemma 13 call (SPEC §4.3), whose chunk exchanges are Lemma 12 swaps through the bit
network (SPEC §3.8; M5 ``swap_bit_chunks`` with the Lemma 12 cutoffs, Dev-6).  Used by the
Bluestein route (Lemma 16 chunk rounds) and the Walsh route alike.

Network names (``Schedule.net_cx``, ``Schedule.net_bit``): a SPEC §2.5 fixture name ("C1", "B1", ...; the test
policies, SPEC §6.3) resolves to the compiled fixture; "triple:<h>:<kind>" names a real triple network (SPEC §2.4;
the faithful schedules name h = 100) and resolves lazily to the ``TripleNetwork(h, kind)`` descriptor
(:func:`network_descriptor`).  Real networks are certified (SPEC §2.7), never executed: every executing resolver
raises :class:`subnlogn.net.errors.RealNetworkNotExecutable` for them.
"""

from __future__ import annotations

from .cnet import CCtx
from .policy import LayerPolicy

__all__ = ["make_engine", "engine_from_schedule", "compiled_fixture", "movement_from_schedule", "REAL_PREFIX",
           "real_network_params", "network_descriptor", "require_executable"]

#: Name prefix of the real triple networks: "triple:<h>:<kind>" (SPEC §2.4).
REAL_PREFIX = "triple:"


def real_network_params(name: str) -> tuple[int, str] | None:
    """(h, kind) if ``name`` = "triple:<h>:<kind>" names a real triple network (SPEC §2.4), None for a SPEC §2.5
    fixture name.  Admissibility of (h, kind) is checked by ``TripleNetwork`` (NotAdmissible)."""
    if not name.startswith(REAL_PREFIX):
        return None
    parts = name.split(":")
    if len(parts) != 3 or not parts[1].isdigit():
        raise ValueError(f"malformed real-network name {name!r}; expected 'triple:<h>:<kind>'")
    return int(parts[1]), parts[2]


def network_descriptor(name: str, cache: dict | None = None):
    """The network a schedule names (SPEC v1.1 §4.0: ctx.net_cx, ctx.net_bit), without executing anything: the lazy
    ``TripleNetwork(h, kind)`` descriptor for "triple:<h>:<kind>" (SPEC §2.4: closed-form parameters only, nothing of
    size m or W is built; its certificate is ``net.certify.certify_triple(h, kind)``, SPEC §2.7), otherwise the
    compiled SPEC §2.5 fixture.  Cached in ``cache`` if given."""
    hk = real_network_params(name)
    if hk is None:
        return compiled_fixture(name, cache)
    key = ("triple", name)
    if cache is not None and key in cache:
        return cache[key]
    from ..net.triple import TripleNetwork
    net = TripleNetwork(*hk)
    if cache is not None:
        cache[key] = net
    return net


def require_executable(name: str) -> None:
    """Raise RealNetworkNotExecutable if ``name`` names a real triple network: those are certified
    (SPEC §2.7), never run; m = h^3 = 10^6 roles at h = 100.  Fixture names pass."""
    hk = real_network_params(name)
    if hk is None:
        return
    from ..net.errors import RealNetworkNotExecutable
    from ..net.triple import triple_params
    p = triple_params(*hk)
    raise RealNetworkNotExecutable(
        f"real networks are not executable at feasible sizes (m ≈ 10^6): {name!r} is the lazy descriptor "
        f"TripleNetwork(h={p.h}, kind={p.kind!r}) with m = h^3 = {p.m} roles and W = {p.W} wires (SPEC §2.4); it is "
        f"certified (net.certify.certify_triple, SPEC §2.7), never executed.  Executable networks are the SPEC §2.5 "
        f"fixtures, e.g. schedule.with_(net_cx='C1', net_bit='B1').")


def compiled_fixture(name: str, cache: dict | None = None):
    """The compiled test network ``fixture_<name>`` (SPEC §2.5), cached in ``cache`` if given.  This is the
    pipeline's only point where networks are registered for use (engine_from_schedule,
    movement_from_schedule, bridge.movement.mover_from_schedule): every network is checked by
    ``net.validate`` (all SPEC §2.6 interface checks, ≤ 12 ms per fixture) before it is cached or used, so
    a network that is not an interface raises ``NotAnInterface`` here.  A real-network
    name raises RealNetworkNotExecutable (:func:`require_executable`): the real triple networks
    (h = 100) are never executed, and their interface properties are certified by
    ``net.certify.certify_triple`` (SPEC §2.7)."""
    require_executable(name)
    from ..net import compile_network, fixtures
    from ..net.validate import validate
    key = ("net", name)
    if cache is not None and key in cache:
        return cache[key]
    net = compile_network(getattr(fixtures, "fixture_" + name)())
    validate(net)
    if cache is not None:
        cache[key] = net
    return net


def make_engine(net_cx, d: int, policy: LayerPolicy, *, net_bit=None, lemma12_min_e: int = 2,
                lemma12_min_u: int = 1, basis_change: str = "lemma13", inst=None) -> CCtx:
    """A network-engine context.  ``basis_change="lemma13"`` (faithful) wires
    :func:`subnlogn.m6.lemma13.row_add_lemma13` with the policy's bad set and Lemma 12 swaps on
    ``net_bit``; ``"direct"`` keeps the address-permutation oracle (unit tests only)."""
    if basis_change == "direct":
        return CCtx(net=net_cx, d=d, policy=policy, inst=inst)
    if basis_change != "lemma13":
        raise ValueError(basis_change)
    from ..interchange import InterchangePolicy
    from .lemma13 import row_add_lemma13, swap_via_lemma12
    swap = None if net_bit is None else \
        swap_via_lemma12(net_bit, InterchangePolicy(lemma12_min_e=lemma12_min_e,
                                                    lemma12_min_u=lemma12_min_u))

    def row_add(arr, rows, nb, dst, src, z, K, rho):
        return row_add_lemma13(arr, rows, nb, dst, src, z, K, rho, bad_set=policy.bad_set,
                               swap=swap, inst=inst)

    return CCtx(net=net_cx, d=d, policy=policy, row_add=row_add, inst=inst)


def engine_from_schedule(ctx, d: int) -> CCtx | None:
    """The engine selected by the schedule: None for M3 direct layers (``prop14_layer="base"``,
    SPEC §5.11), else the network engine with the schedule's networks, LayerPolicy and Lemma 12
    cutoffs; d = the tensor dimension (leaf rule, q0, k0, guard)."""
    sch = ctx.schedule
    if sch.prop14_layer == "base":
        return None
    if sch.prop14_layer != "network":
        raise ValueError(sch.prop14_layer)
    return make_engine(compiled_fixture(sch.net_cx, ctx.tables), d, sch.layer,
                       net_bit=compiled_fixture(sch.net_bit, ctx.tables),
                       lemma12_min_e=sch.lemma12_min_e, lemma12_min_u=sch.lemma12_min_u,
                       inst=ctx.inst)


def movement_from_schedule(ctx):
    """The chunk-exchange procedure for Lemma 16's layout L: Lemma 12 on the schedule's bit network
    with its cutoffs (SPEC §5.2, §3.8), run on record IDs (D12), when the schedule executes address
    movements by Lemma 12 (``bridge_movement="lemma12"``, the SPEC §6.3 test policies); None = the
    reference index maps (``"index"``, DEVIATIONS D9)."""
    sch = ctx.schedule
    if sch.bridge_movement != "lemma12":
        return None
    from ..interchange import InterchangePolicy
    from .lemma13 import swap_via_lemma12
    return swap_via_lemma12(compiled_fixture(sch.net_bit, ctx.tables),
                            InterchangePolicy(lemma12_min_e=sch.lemma12_min_e,
                                              lemma12_min_u=sch.lemma12_min_u))
