"""The pipeline validates every network when it is registered for use
(m6.engine.compiled_fixture, the only registration point: the Prop 14 engine, Lemma 16's chunk exchanges
and the bridge's axis movements all load networks through it).  A network that is not an interface is
rejected before any data passes through it."""

from dataclasses import replace

import pytest

import subnlogn.net.fixtures as fx
import subnlogn.net.validate as nv
from subnlogn.m6.engine import compiled_fixture
from subnlogn.net.errors import NotAnInterface


@pytest.mark.parametrize("name", ["B1", "B2", "C1", "C2"])
def test_fixtures_validated_once_per_cache(monkeypatch, name):
    calls = []
    orig = nv.validate
    monkeypatch.setattr(nv, "validate", lambda net, *a, **k: calls.append(net) or orig(net, *a, **k))
    cache: dict = {}
    a = compiled_fixture(name, cache)
    b = compiled_fixture(name, cache)
    assert a is b and len(calls) == 1


def test_broken_network_rejected_at_registration(monkeypatch):
    """C1 with a wrong route sign (a test_net_fixtures broken variant) never reaches the engine."""
    genuine = fx.fixture_C1
    monkeypatch.setattr(fx, "fixture_C1", lambda: replace(genuine(), route_sign=(1, 1, 1)))
    cache: dict = {}
    with pytest.raises(NotAnInterface):
        compiled_fixture("C1", cache)
    assert ("net", "C1") not in cache
