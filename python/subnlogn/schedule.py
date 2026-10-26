"""Explicit parameter schedules.  There is no global state: a ``Schedule`` is an immutable object
passed explicitly (inside a :class:`subnlogn.context.Ctx`) to every algorithm entry point.

A schedule fixes the precision formulas, the leaf rule, the rounding mode, (for M2) the
bridge dimension and the routing of the 2D FastDFT (``routing``: "tape" = the passes of MS Lemma
2.4, of the proof of Lemma 2.5 and of the leaf paragraph (L693), the default; "index" = RAM index
maps, kept as the oracle).  Two constructors:

:func:`faithful_schedule`
    The manuscript's certified schedule (our_paper eq. (cert-sched), Lemma 6.5 ``lem:forward``)::

        p_work  = p + 2K + 16          (= w, the stopband cutoff parameter of Thm 5.1)
        p_child = p + 6K + 32          (= P, the child precision)
        q_child = p_child + 2          (working grid of Steps 1-3)
        m1      = p_child              (spatial half-width; W = 2 m1 + 1 taps)
        leaf iff R <= 4 p^2            (listing line 733; Lemma 6.5 part 2)
        q_b     = p + K + 16           (internal precision of BaseRadix2FFT, Lemma 6.5)

    plus 4 integer headroom bits for the drop-in's uniformly specified solver prefixes
    (r2 §8: "adding four is sufficient").  The bridge (M2) uses the Lemma C budget
    of r2 Theorem 2 (the authoritative contract; the paper's bridge precision contract):
    w = p + K + ceil(lg d) + 20, P = 2p + 12K + 32 ceil(lg(p+K+2)) + 256, m = P; the r3 profile
    (P = 2p + 6K + 128, w = m = P) remains selectable via ``bridge_constants="r3"``.

:func:`test_schedule`
    Identical precision formulas (so every proved error bound still applies) but forced base
    thresholds, forced recursion depth, and/or a forced bridge dimension d.  This is how every
    code path is exercised at small sizes (the "test schedule").
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from .fixedpoint import Rounding
from .m6.engine import real_network_params
from .m6.policy import LAYER_TEST, LAYER_THEOREM, LAYER_WALSH_46, LAYER_WALSH_47, LayerPolicy
from .theorem import THEOREM_ROWS

__all__ = ["Schedule", "Level2D", "faithful_schedule", "test_schedule", "split_2d"]


def split_2d(K: int) -> tuple[int, int]:
    """Return (k1, k2) with t1 = 2^k1, r = 2^k2, k1 = floor(K/2), k2 = ceil(K/2): the split of the
    listing (lines 737-738), so t1 | r and t1 in {r, r/2}."""
    return K // 2, (K + 1) // 2


@dataclass(frozen=True)
class Level2D:
    """All parameters of one FastDFT node of length R = 2^K at target precision p (2D, M1).

    Non-leaf fields follow eq. (cert-sched); ``B_slot`` is eq. (slot-width); ``W_tilde`` is
    min(W, r) (Thm 6.3, Remark 6.4 ``rem:folding``).  ``q_b`` is the leaf internal precision.
    """

    R: int
    K: int
    p: int
    depth: int
    leaf: bool
    # non-leaf (zero at leaves)
    k1: int = 0
    k2: int = 0
    t1: int = 0
    r: int = 0
    nu: int = 0
    p_work: int = 0
    p_child: int = 0
    q_child: int = 0
    m1: int = 0
    W: int = 0
    W_tilde: int = 0
    B_slot: int = 0
    # leaf
    q_b: int = 0

    @property
    def q(self) -> int:
        """Input/output grid scale p + 2 (C~_{p+2}, Def. 2.1)."""
        return self.p + 2


@dataclass(frozen=True)
class Schedule:
    """Immutable parameter schedule.  See the module docstring for the meaning of each field."""

    name: str
    # --- 2D FastDFT precision schedule (eq. cert-sched) ---
    work_K: int = 2
    work_c: int = 16
    child_K: int = 6
    child_c: int = 32
    # --- leaf rule ---
    leaf_quadratic: bool = True          # leaf iff R <= 4 p^2
    base_threshold: int | None = None    # test: leaf iff R <= base_threshold
    max_depth: int | None = None         # test: leaf iff depth >= max_depth
    base_guard: int = 16                 # q_b = p + K + base_guard
    # --- arithmetic ---
    rounding: Rounding = Rounding.HALF_EVEN
    solver_headroom_bits: int = 4        # drop-in integer headroom (r2 §8)
    # --- multiplier (Thm 7.1 / listing) ---
    mul_direct_bits: int = 64            # listing line 706: n <= 64 -> A * B
    # --- d-dimensional bridge (M2); None selects the 2D recursion of M1 ---
    bridge_d: int | None = None
    bridge_constants: str = "r2"         # faithful default (the paper's bridge precision contract):
                                         #   w = p+K+ceil(lg d)+20, P = 2p+12K+32 ceil(lg(p+K+2))+256,
                                         #   m = P  (r2 (2.8)-(2.9));
                                         # alternative profile "r3": P = 2p+6K+128, w = m = P (r3 (2.3))
    bridge_middle: str = "direct"        # middle tensor DFT backend (M2: direct; M3: Bluestein; M9: Walsh)
    bridge_movement: str = "index"       # bridge address movements (SPEC §7.2): "index" = RAM index maps (M2/M3
                                         #   reference, D2/D9/D13); "lemma12" = O(d) Lemma 12 exchanges on the
                                         #   bit network (axis exposures, storage <-> tensor reversal; bridge.movement)
    chunk_bits: int = 1                  # K = floor(d^c) of Pr §§5-7 (= 1 for every feasible d; SPEC §6.1)
    prop14_layer: str = "base"           # "base" (M3 direct layers, SPEC §5.11) | "network" (M6, §4.5-4.7)
    net_cx: str = "C1"                   # complex network: a SPEC §2.5 fixture (test policies, §6.3 TestPolicy.net_cx)
                                         #   or "triple:<h>:complex", a real network (lazy, never executed)
    layer: LayerPolicy = LAYER_THEOREM   # Prop 14 engine policy (SPEC v1.1 §4.0): the printed values;
                                         #   test_schedule uses LAYER_TEST (§6.3)
    bridge_mid_guard: int = 16           # direct middle DFT internal grid: P + K + guard
    net_bit: str = "B1"                  # bit network for Lemma 12 inside Lemma 13: a fixture (SPEC §6.3) or
                                         #   "triple:<h>:bit" (real, lazy, never executed)
    lemma12_min_e: int = 2               # Lemma 12 digitwise below this radix-q width (Dev-6)
    lemma12_min_u: int = 1               # Lemma 12 bitwise below this binary width (Dev-6)
    min_root_exponent: int = 0           # test-only: R0 >= 2^min_root_exponent (Dev-9; R0 >= 2N kept)
    theorem_row: str = "printed"         # theorem-mode parameter row (subnlogn.theorem.THEOREM_ROWS): "printed"
                                         #   (SPEC §6.1, Bluestein) | "walsh47" | "walsh46" (SPEC_WALSH §1.3, §9.1)
    # --- 2D routing (MS Lemma 2.4 ``lem:routing``, Lemma 2.5 proof, leaf L693) ---
    routing: str = "tape"                # "tape": the proofs' split/merge passes for every routing step of
                                         #   the 2D fallback (the faithful algorithm) | "index": RAM index
                                         #   maps (oracle; DEVIATIONS D2)

    def __post_init__(self):
        if self.routing not in ("tape", "index"):
            raise ValueError(f"routing must be 'tape' or 'index', got {self.routing!r}")
        if self.theorem_row not in THEOREM_ROWS:
            raise ValueError(f"theorem_row must be one of {sorted(THEOREM_ROWS)}, got {self.theorem_row!r}")
        for role, kind in (("net_cx", "complex"), ("net_bit", "bit")):   # real-network names match their role
            hk = real_network_params(getattr(self, role))                # ValueError if malformed
            if hk is not None:
                if hk[1] != kind:
                    raise ValueError(f"{role} needs a {kind} network ('triple:<h>:{kind}' or a SPEC §2.5 fixture), "
                                     f"got {getattr(self, role)!r}")
                from .net.triple import check_admissible
                check_admissible(*hk)                                    # NotAdmissible (SPEC §2.4)
        if self.bridge_middle in ("bluestein", "walsh") and self.bridge_constants != "r2":
            raise ValueError("the Bluestein and Walsh middles need br_r2's input pre-scaling "
                             "(bridge_constants='r2', SPEC §5.10); 'r3' is supported with the direct middle")

    # ------------------------------------------------------------------------------------------

    def is_leaf(self, R: int, p: int, depth: int) -> bool:
        """Leaf rule.  R <= 2 is always a leaf (Thm 5.1 needs t1 >= 2, i.e. K >= 2)."""
        if R <= 2:
            return True
        if self.max_depth is not None and depth >= self.max_depth:
            return True
        if self.base_threshold is not None:
            return R <= self.base_threshold
        if self.leaf_quadratic:
            return R <= 4 * p * p
        return False

    def level(self, R: int, p: int, depth: int = 0) -> Level2D:
        """Parameters of a FastDFT node (2D algorithm, M1)."""
        if R < 1 or R & (R - 1):
            raise ValueError(f"R={R} is not a power of two")
        K = R.bit_length() - 1
        if self.is_leaf(R, p, depth):
            return Level2D(R=R, K=K, p=p, depth=depth, leaf=True, q_b=p + K + self.base_guard)
        k1, k2 = split_2d(K)
        t1, r = 1 << k1, 1 << k2
        p_work = p + self.work_K * K + self.work_c
        p_child = p + self.child_K * K + self.child_c
        q_child = p_child + 2
        m1 = p_child
        W = 2 * m1 + 1
        W_tilde = min(W, r)
        # eq. (slot-width): B_slot = 2q + p + ceil(lg(W~ + 1)) + 4, and ceil(lg(n)) = (n-1).bit_length()
        B_slot = 2 * q_child + p + W_tilde.bit_length() + 4
        return Level2D(R=R, K=K, p=p, depth=depth, leaf=False, k1=k1, k2=k2, t1=t1, r=r,
                       nu=r // t1, p_work=p_work, p_child=p_child, q_child=q_child, m1=m1,
                       W=W, W_tilde=W_tilde, B_slot=B_slot)

    def chain(self, R: int, p: int) -> list[Level2D]:
        """The level chain R_0 = R -> R_1 = r_0 -> ... -> leaf (all nodes at one depth share it)."""
        out = []
        depth = 0
        while True:
            lv = self.level(R, p, depth)
            out.append(lv)
            if lv.leaf:
                return out
            R, p, depth = lv.r, lv.p_child, depth + 1

    def bridge_params(self, p: int, K: int, d: int) -> tuple[int, int, int]:
        """Lemma C budget (P, w, m) of the d-dimensional bridge.

        "r2" (faithful default: the paper's bridge precision contract): w = p + K + ceil(lg d) + 20,
        P = 2p + 12K + 32 ceil(lg(p + K + 2)) + 256, m = P (r2 Thm 2, (2.8)-(2.9)).
        "r3" (alternative profile): P = 2p + 6K + 128, w = P, m = P (r3 eq. (2.3)).
        r2's P >= r3's P for all p, K."""
        if self.bridge_constants == "r3":
            P = 2 * p + 6 * K + 128
            return P, P, P
        if self.bridge_constants == "r2":
            lgd = (d - 1).bit_length()
            P = 2 * p + 12 * K + 32 * (p + K + 1).bit_length() + 256
            return P, p + K + lgd + 20, P
        raise ValueError(self.bridge_constants)

    def with_(self, **kw) -> "Schedule":
        return replace(self, **kw)


#: The Prop 14 policy preset of each theorem row (SPEC §4.0 LAYER_THEOREM; SPEC_WALSH §1.4).
ROW_LAYERS = {"printed": LAYER_THEOREM, "walsh47": LAYER_WALSH_47, "walsh46": LAYER_WALSH_46}
#: The real networks of the theorem configuration (SPEC §2.4; h = 100), named by every faithful schedule and
#: resolved lazily by ``m6.engine.network_descriptor``; executing them raises RealNetworkNotExecutable.
REAL_NET_CX, REAL_NET_BIT = "triple:100:complex", "triple:100:bit"


def faithful_schedule(row: str = "printed") -> Schedule:
    """The manuscript's certified schedule plus the drop-in's 4 headroom bits (module docstring), with the
    theorem-mode parameter row ``row``: "printed" (SPEC §6.1, Bluestein middle, LAYER_THEOREM; name "faithful") or a
    Walsh row of SPEC_WALSH §1.3 / §9.1, "walsh47" or "walsh46" (Walsh middle, LAYER_WALSH_47 / LAYER_WALSH_46;
    name "faithful-walsh47" / "faithful-walsh46").  The row decides theorem_shape's (eps, c) and the theorem
    branch's middle and policy; theorem mode is unreachable at every feasible size for every row, so the 2D
    fallback runs.  Every row names the real h = 100 networks (REAL_NET_CX, REAL_NET_BIT; SPEC §2.4), not the SPEC
    §2.5 test fixtures: they are resolved lazily and never executed (the theorem branch raises
    RealNetworkNotExecutable before any data moves)."""
    if row not in ROW_LAYERS:
        raise ValueError(f"row must be one of {sorted(ROW_LAYERS)}, got {row!r}")
    return Schedule(name="faithful" if row == "printed" else f"faithful-{row}", theorem_row=row,
                    layer=ROW_LAYERS[row], net_cx=REAL_NET_CX, net_bit=REAL_NET_BIT)


def test_schedule(base_threshold: int | None = 2, max_depth: int | None = None,
                  bridge_d: int | None = None, mul_direct_bits: int = 0,
                  rounding: Rounding = Rounding.HALF_EVEN) -> Schedule:
    """Same precision formulas as :func:`faithful_schedule`, forced small thresholds.

    ``base_threshold=2`` forces the deepest possible recursion; ``max_depth`` caps it;
    ``bridge_d`` forces the d-dimensional bridge (M2); ``mul_direct_bits=0`` forces the full
    multiplier pipeline even for tiny operands.
    """
    return Schedule(name="test", leaf_quadratic=False, base_threshold=base_threshold,
                    max_depth=max_depth, bridge_d=bridge_d, mul_direct_bits=mul_direct_bits,
                    rounding=rounding, layer=LAYER_TEST)


test_schedule.__test__ = False   # not a pytest test despite its name


def test_policy(d: int, chunk_bits: int = 1, net_bit: str = "B1", net_cx: str = "C1",
                layer: LayerPolicy = LAYER_TEST, middle: str = "bluestein", lemma12_min_e: int = 2,
                lemma12_min_u: int = 1, direct_layers: bool = False, min_root_exponent: int = 0,
                base_threshold: int | None = 2, bridge_movement: str = "lemma12") -> Schedule:
    """SPEC §6.3 ``TestPolicy`` as a schedule: forced bridge dimension d (t as in theorem_shape),
    chunk width, test networks, the Prop 14 engine policy, the middle ("bluestein" | "walsh" |
    "direct"), Lemma 12 cutoffs, M3 direct layers or the network engine, the Dev-9 root
    exponent, and the bridge address movements (default "lemma12": SPEC §7.2 exchanges).  The inner-product backend (TestPolicy.mul) is the context's ``imul``.  Forced test
    mode never takes the n <= 64 shortcut (mul_direct_bits = 0)."""
    return replace(test_schedule(base_threshold=base_threshold, bridge_d=d), chunk_bits=chunk_bits,
                   net_bit=net_bit, net_cx=net_cx, layer=layer, bridge_middle=middle,
                   lemma12_min_e=lemma12_min_e, lemma12_min_u=lemma12_min_u,
                   prop14_layer="base" if direct_layers else "network",
                   min_root_exponent=min_root_exponent, bridge_movement=bridge_movement)


test_policy.__test__ = False
