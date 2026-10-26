"""Exceptions of the finite-network package (SPEC §2.6: "Run at compile time; fail loudly")."""

from __future__ import annotations


class NotAnInterface(ValueError):
    """A supplied network (or a piece of it) violates the interface of SPEC §2.1-§2.3.

    Raised by ``net.validate`` and by the compile-time constructions (``orthonormal_basis``, edge compilation) when a
    check of SPEC §2.6 fails.  The message names the role / edge / check that failed.
    """


class NotAdmissible(ValueError):
    """Parameters outside the admissible range of the triple construction (SPEC §2.4: h >= 7, h != 9 for bit)."""


class RealNetworkNotExecutable(RuntimeError):
    """A schedule asked to RUN a real triple network.

    The real networks are ``TripleNetwork(h, kind)`` (SPEC §2.4; h = 100 is THE real network), with m = h^3
    roles (10^6 at h = 100) and W = 1.8e20 (bit) or 1.9e21 (complex) wires: they exist as lazy descriptors and are
    certified exactly (SPEC §2.7, ``net.certify.certify_triple``), never compiled or executed.  The faithful
    schedules name them (``schedule.faithful_schedule``: net_cx = "triple:100:complex", net_bit = "triple:100:bit");
    every attempt to execute them -- the theorem branch, or the engine / movement resolvers of
    :mod:`subnlogn.m6.engine` -- raises this error before any data moves.  Executable networks are the SPEC §2.5
    test fixtures (B1, B2, B2q5, C1, C2).
    """
