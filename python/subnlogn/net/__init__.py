"""subnlogn.net -- finite networks as data (milestone M4; SPEC §2, §3.1-3.2).

Modules:

* :mod:`subnlogn.net.qmatrix`  -- exact rational matrices, Lemma 9 ``lower_bruhat``, ``choose_prime`` (q_radix).
* :mod:`subnlogn.net.f2`       -- F2 linear algebra on m-bit ints, P_U, q_U, Lemma 6 orthonormal bases, reduce_ops.
* :mod:`subnlogn.net.zi2`      -- exact Gaussian dyadics Z[i, 1/2] (the complex network's scalar domain).
* :mod:`subnlogn.net.phase`    -- C_U, C_v as exact Gaussian-dyadic operators; endpoint / Prop 8 identities.
* :mod:`subnlogn.net.model`    -- ``Gate``, ``Network``, ``BitEdge``, ``PhaseEdge``, ``compile_network``.
* :mod:`subnlogn.net.fixtures` -- the scalar 12-gate circuit and fixtures B1, B2, C1, C2 (SPEC §2.5).
"""

from .errors import NotAdmissible, NotAnInterface, RealNetworkNotExecutable
from .model import SOURCE, BitEdge, CompiledNetwork, Edge, Gate, Network, PhaseEdge, compile_network
from .qmatrix import choose_prime, lower_bruhat, lower_bruhat_factors

__all__ = ["NotAdmissible", "NotAnInterface", "RealNetworkNotExecutable", "SOURCE", "BitEdge", "CompiledNetwork",
           "Edge", "Gate", "Network", "PhaseEdge", "compile_network", "choose_prime", "lower_bruhat",
           "lower_bruhat_factors"]
