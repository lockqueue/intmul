"""Small test networks (SPEC §2.5; Completion, S1 §3 and S2 §3): the scalar 12-gate circuit and fixtures B1, B2
(bit, m = 2) and C1, C2 (complex, m = 3).  None of them has a rank saving; that is intended (SPEC Dev-1).

Roles X = 0, Y = 1, A = 2 (three roles: the minimum with an auxiliary whose restoration is non-vacuous).  The twelve
gates are two-role transvections ``target += c * control`` with gate matrix [[1, c], [0, 1]] on (target, control):

    stage 1 transparent_add(X->Y):            g0: Y -= A; g1: A += X; g2: Y += A; g3: A -= X
    stage 2 inverse transparent_add(Y->X):    g4: A += Y; g5: X -= A; g6: A -= Y; g7: X += A
    stage 3 transparent_add(X->Y):            g8: Y -= A; g9: A += X; g10: Y += A; g11: A -= X

Net map (x, y, a) -> (-y, x, a) for arbitrary a; over F2 every sign is +1 (XOR).  Route (X->Y, Y->X, A->A) with
signs (+1, -1, +1) over ZI2, all +1 over F2 [Pr L708-726 (Lemma 5 pattern)].
"""

from __future__ import annotations

from fractions import Fraction

from .model import Gate, Network
from .qmatrix import identity, qmat, scale, sub, zeros
from .zi2 import ZI2

X, Y, A = 0, 1, 2
ROLES = ("X", "Y", "A")
#: (target, control, c) for g0..g11 (SPEC §2.5 table).
SCALAR_STEPS = ((Y, A, -1), (A, X, 1), (Y, A, 1), (A, X, -1),
                (A, Y, 1), (X, A, -1), (A, Y, -1), (X, A, 1),
                (Y, A, -1), (A, X, 1), (Y, A, 1), (A, X, -1))
ROUTE = (Y, X, A)
SIGNS_ZI2 = (1, -1, 1)


def scalar_gates(domain: str, frames) -> tuple[Gate, ...]:
    """The 12 transvection gates of SPEC §2.5 with the given per-gate frames (F2: c mod 2; ZI2: exact c)."""
    out = []
    for (t, c, coef), fr in zip(SCALAR_STEPS, frames):
        if domain == "F2":
            mat = ((1, coef % 2), (0, 1))
        else:
            mat = ((ZI2(1), ZI2(coef)), (ZI2(0), ZI2(1)))
        out.append(Gate(roles=(t, c), matrix=mat, frame=fr))
    return tuple(out)


def scalar_network_map(domain: str):
    """The composite W x W scalar matrix of the 12 gates (out = T @ in); used in tests of the circuit itself."""
    from .validate import compose_scalar_map  # local import (validate imports this package lazily)
    return compose_scalar_map(Network(domain=domain, m=1, roles=ROLES, gates=scalar_gates(domain, [None] * 12),
                                      source=(None,) * 3, sink=(None,) * 3, route=ROUTE,
                                      route_sign=(1, 1, 1) if domain == "F2" else SIGNS_ZI2))


# ----------------------------------------------------------------------------------------------- bit fixtures
def fixture_B1() -> Network:
    """Bit fixture B1 (S2 §3.3; primary), m = 2: sources X = -P0, Y = A = 0; gate g0 frame J2, other gates 0;
    sinks X = A = I2, Y = I2 - P0.  s = 10, W = 3, q_radix = 3; exercises the negative source projection and
    nontrivial triangular factors (SPEC §2.5)."""
    P0 = qmat([[1, 0], [0, 0]])
    J2 = qmat([[1, 1], [1, 1]])
    I2, Z = identity(2), zeros(2)
    frames = [J2] + [Z] * 11
    return Network(domain="F2", m=2, roles=ROLES, gates=scalar_gates("F2", frames),
                   source=(scale(-1, P0), Z, Z), sink=(I2, sub(I2, P0), I2), route=ROUTE, route_sign=(1, 1, 1))


def fixture_B2() -> Network:
    """Bit fixture B2 (S1 §3.2; secondary), m = 2: all sources 0, all sinks I2, gate g1 (A += X) frame J2/2,
    other gates 0.  s = 10; q_radix = 3 (pivot 1/2: denominator 2) (SPEC §2.5)."""
    J2h = qmat([[Fraction(1, 2), Fraction(1, 2)], [Fraction(1, 2), Fraction(1, 2)]])
    I2, Z = identity(2), zeros(2)
    frames = [Z, J2h] + [Z] * 10
    return Network(domain="F2", m=2, roles=ROLES, gates=scalar_gates("F2", frames),
                   source=(Z, Z, Z), sink=(I2, I2, I2), route=ROUTE, route_sign=(1, 1, 1))


def fixture_B2q5() -> Network:
    """B2 with the gate frame J2/3 (moved here from the M5 tests): the denominator 3 is forbidden, so
    q_radix = 5 != W = 3 and Lemma 12 must pad its row field (SPEC §3.7, §3.10).  s = 10 (SPEC §2.5 B2 pattern)."""
    J3 = qmat([[Fraction(1, 3), Fraction(1, 3)], [Fraction(1, 3), Fraction(1, 3)]])
    I2, Z = identity(2), zeros(2)
    frames = [Z, J3] + [Z] * 10
    return Network(domain="F2", m=2, roles=ROLES, gates=scalar_gates("F2", frames),
                   source=(Z, Z, Z), sink=(I2, I2, I2), route=ROUTE, route_sign=(1, 1, 1))


# ----------------------------------------------------------------------------------------------- complex fixtures
E0, E1, E2 = 0b001, 0b010, 0b100   # e_i = bit i
V111 = 0b111                       # v = (1, 1, 1), wt 3, v.v = 1
FULL3 = (E0, E1, E2)


def fixture_C1() -> Network:
    """Complex fixture C1 (S2 §3.4; primary), m = 3, e0 = 100, v = 111: sources X = <e0>, Y = A = 0; gate g0 label
    <v>, other gates 0; sinks X = A = F, Y = <e1, e2>.  Corrections: pre Z-mask {0} at input X; post Z-mask {0}
    and post_ipow 1 at output Y.  s = 13 (SPEC §2.5; C = iZC^{-1}Z [Pr L1298])."""
    frames = [(V111,)] + [()] * 11
    return Network(domain="ZI2", m=3, roles=ROLES, gates=scalar_gates("ZI2", frames),
                   source=((E0,), (), ()), sink=(FULL3, (E1, E2), FULL3), route=ROUTE, route_sign=SIGNS_ZI2,
                   pre_zmask=((0,), (), ()), post_zmask=((), (0,), ()), post_ipow=(0, 1, 0))


def fixture_C2() -> Network:
    """Complex fixture C2 (S1 §3.3; secondary), m = 3: all sources 0, all sinks F; gate g1 (A += X) label <v>,
    others 0.  s = 13; no Z corrections, only the X-output negation (route sign) (SPEC §2.5)."""
    frames = [(), (V111,)] + [()] * 10
    return Network(domain="ZI2", m=3, roles=ROLES, gates=scalar_gates("ZI2", frames),
                   source=((), (), ()), sink=(FULL3, FULL3, FULL3), route=ROUTE, route_sign=SIGNS_ZI2)


FIXTURES = {"B1": fixture_B1, "B2": fixture_B2, "B2q5": fixture_B2q5, "C1": fixture_C1, "C2": fixture_C2}
#: Expected counts (SPEC §2.5): (W, m, s, q_radix or None).
EXPECTED = {"B1": (3, 2, 10, 3), "B2": (3, 2, 10, 3), "B2q5": (3, 2, 10, 5), "C1": (3, 3, 13, None),
            "C2": (3, 3, 13, None)}
