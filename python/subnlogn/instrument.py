"""Instrumentation: per-component call counters, record-height monitors and a component coverage
report (M0).  An :class:`Instrument` lives inside the explicit :class:`~subnlogn.context.Ctx`;
nothing here is global.

Component names are dotted strings.  ``COMPONENTS`` lists every algorithm component that a full
test run is expected to exercise; :meth:`Instrument.coverage_report` shows which were hit.
"""

from __future__ import annotations

from collections import Counter

__all__ = ["Instrument", "COMPONENTS"]

#: Registry of algorithm components (name -> source of the step it counts).
COMPONENTS: dict[str, str] = {
    "fastdft.node": "listing FastDFT, non-leaf node (Lemma 6.5)",
    "fastdft.leaf": "BaseRadix2FFT leaf (Lemma 6.5 part 2, §2.2 (d))",
    "basefft.butterfly": "leaf radix-2 butterfly W=RM(w,B), Q(1/2(A+-W))",
    "spread.row": "Step 1 row spreading (Thm 6.3)",
    "kron.product": "signed Kronecker block product, counted per product (Lemma 6.2, Thm 6.3)",
    "tables.closure_powering": "closure gamma-hat by br_r2 (4.21) truncated powering (the default)",
    "twist.pre": "Step 2a pre-twist (Thm 3.1 step 1)",
    "synfft.butterfly": "Step 2b synthetic butterfly over C[y]/(y^r+1) (Lemma 2.5)",
    "twist.post": "Step 2c post-twist (Thm 3.1 step 3)",
    "route.oddstride": "Step 2e odd-stride routing (Thm 3.1 step 5, Lemma 2.4(ii))",
    "routing.transpose_pass": "Lemma 2.4(i) split/interleave pass, k1 per transpose (routing='tape')",
    "routing.tag_scan": "Lemma 2.4(ii) tagging scan u1 = (2u2-1)v1 mod t1 (routing='tape')",
    "routing.merge_pass": "Lemma 2.4(ii) bottom-up merge pass on the tags, k1 per route (routing='tape')",
    "routing.syn_bitrev_pass": "Lemma 2.5 proof: split-and-concatenate bit-reversal pass of G_t1 (routing='tape')",
    "routing.syn_stage_split": "Lemma 2.5 proof: stage-s half-block split / lockstep / T4 copy-back (routing='tape')",
    "routing.leaf_bitrev_pass": "BaseRadix2FFT even/odd split bit-reversal pass, K per leaf (MS L693; 'tape')",
    "routing.leaf_stage_split": "BaseRadix2FFT stage-s half-block split + twiddle replay (MS L693, L821; 'tape')",
    "solver.forward": "CyclicSolve case 1, c0 > c1 (§5.2; drop-in r2 §8)",
    "solver.backward": "CyclicSolve case 2, c1 > c0 (§5.2; drop-in r2 §8)",
    "multiply.call": "Multiply, two-call root packing (Thm 7.1)",
    "multiply.direct": "Multiply small-operand shortcut (listing line 706)",
    "word.call": "word-scale product: one call of Ctx.word_mul (every routed or inline product)",
    "hierarchy.word_product": "word-scale product (> 64-bit operand) sent to the next hierarchy stage (MS Thm 7.1 pt 3)",
    "python.word_product_over_64": "word-scale product with a > 64-bit operand by Python's * (products=python; 0 in hierarchy mode)",
    "safety.residue_check": "runtime safety net: product checked mod word-size moduli (not the algorithm)",
    "python.big_product": "packed product by Python's * (D1; must stay 0 with products='hierarchy')",
    "multiply.fallback_2d": "faithful dispatcher: no theorem shape/cutoff -> 2D fallback (SPEC §6.2, §6.4)",
    "hierarchy.basic": "BasicMul: two-call root + base radix-2 FFT (SPEC §6.5)",
    "hierarchy.multiply1": "Multiply1: 2D negative carrier, packed products by BasicMul (SPEC §6.5)",
    "hierarchy.multiply2": "Multiply2: 2D negative carrier, packed products by Multiply1 (SPEC §6.5)",
    "bridge.dft": "d-dimensional bridge DFT (Lemmas A-C)",
    "bridge.spread_axis": "bridge spreading S_h, h = d..2 (Lemma A)",
    "bridge.middle": "direct middle tensor DFT (M2 reference)",
    "bridge.deconv_axis": "bridge deconvolution B_h^-1, h = 2..d (Lemma A order, Lemma B)",
    "bridge.d_clamped": "multiplier: bridge dimension clamped so the middle's hypotheses hold for small R",
    "bridge.fallback_2d": "multiplier: no admissible bridge dimension >= 2 for small R -> 2D FastDFT",
    "prop18.ring_product": "Lemma 17 normalized ring products inside Prop 18 (M3)",
    "bluestein.complex_convolution": "coefficient twist + Prop 18 (Pr §9.4; M3)",
    "bluestein.tensor_dft": "positive tensor DFT by the chirp identity (Lemma 21 (36); M3)",
    "prop14.network_layer": "Prop 14 layer through the complex network (M6)",
    # M6 engine coverage (SPEC §4.11, §6.7); CCtx mirrors its counters as "m6.<key>"
    "m6.layer.network": "Prop 14 network layer: lift, S_D, batched C, S_D, b^D, one Q_p (SPEC §4.7)",
    "m6.c_power.network": "C^{te} internal node through the complex network (SPEC §4.5)",
    "m6.c_power.leaf": "C^{te} leaf: individual exact kernels (SPEC §4.5 leaf rule)",
    "m6.gate": "pointwise Gaussian-dyadic gate from saved inputs (SPEC §2.1, §4.5)",
    "m6.phase_edge.nonzero": "phase edge C_V C_U^-1 with a nonzero residual (SPEC §4.4)",
    "m6.phase_edge.inverse_kernel": "inverse directional kernel (-i)^f Z C Z (SPEC §4.4)",
    "m6.phase_edge.source_correction": "nonzero first edge out of the source frame (SPEC §4.5)",
    "m6.phase_edge.sink_correction": "nonzero last edge into the sink frame (SPEC §4.5)",
    "m6.zmask.pre": "endpoint Z mask before the gates (SPEC §4.5)",
    "m6.zmask.post": "endpoint Z mask after the gates (SPEC §4.5)",
    "m6.ipow.post": "post i-power, once per role (SPEC §4.5)",
    "m6.route_sign": "route sign undone once per role (SPEC §4.5)",
    "m6.rows.padded": "zero rows added to a multiple of W^k0 (SPEC §4.6)",
    "m6.rows.removed": "padded rows asserted zero and removed (SPEC §4.6)",
    "layout.executed": "Lemma 16 layout L / L^-1 executed by Lemma 3 moves and Lemma 12 exchanges (SPEC §5.2)",
    "m6.row_add.lemma13": "P_M row addition as one Lemma 13 call (SPEC §4.3)",
    "lemma13.call": "Lemma 13 packed selected-bit addition (Pr L1928-2151; SPEC §4.1)",
    "lemma13.call_f2plus": "Lemma 13 call with f >= 2 slot chunks: rotations, swaps and repair run (f = 1: XOR only)",
    "lemma13.records_f2plus": "records in the f >= 2 Lemma 13 calls (the denominator of lemma13.bad_records)",
    "lemma13.repair_partial": "Lemma 13 repair whose exceptional set B is neither empty nor the whole rectangle",
    "lemma13.rotation": "Lemma 13 packed rotation (20)/(22) by a Lemma 4 controlled shift",
    "lemma13.swap": "Lemma 13 chunk exchange bringing the target rightmost (SPEC §4.1)",
    "lemma13.bad_records": "Lemma 13 exceptional extraction (23) (SPEC §4.2)",
    "lemma13.sort": "Lemma 13 stable LSD radix sort of the extracted bank (SPEC §4.2)",
    "lemma13.reinsert": "Lemma 13 reinsertion into the holes, keys == holes (SPEC §4.2)",
    "lemma13.top_xor": "Lemma 13 Lemma 3 XOR of the top selected position (SPEC §4.1)",
    "interchange.lemma12_network_call": "Lemma 12 Prop 11 call through the bit network (SPEC §3.7)",
    "interchange.prop11_node": "Prop 11 node: roles, Lemma 10 shears per edge, F2 gates (SPEC §3.6)",
    "interchange.child_call": "Lemma 10 interchange child of a nonzero-rank bit edge (SPEC §3.5)",
    "walsh.gadget": "selective Walsh operation H_T = scalar (H_all S_U)^3 (SPEC_WALSH §2; M9)",
    "walsh.gadget.q_even": "selective gadget with q = D - s even (no (1 - i) factor; SPEC_WALSH §2.2)",
    "walsh.gadget.q_odd": "selective gadget with q odd (one (1 - i) factor; SPEC_WALSH §2.2)",
    "walsh.su_scan": "S_U diagonal scan of a selective gadget (SPEC_WALSH §2.3)",
    "walsh.cz_scan": "CZ sign scan of a CNOT batch (SPEC_WALSH §3)",
    "walsh.slice_batch": "nonempty CNOT batch on one slice (SPEC_WALSH §3, §4.3)",
    "walsh.leftover_cnot": "elementary CNOT on a leftover target (Lemma 3 index map; Dev-W3)",
    "walsh.positional_map": "positional map executed by two involutions (SPEC_WALSH §4.3)",
    "walsh.chunk_round": "record-axis chunk round through Prop 14 (SPEC_WALSH §5.3)",
    "walsh.prefix_round": "record-axis prefix round, exact H0 factors + one Q_p (SPEC_WALSH §5.3)",
    "walsh.bit_reversal": "last-axis bit reversal (index map; Dev-W3)",
    "walsh.phase": "phase-table lookups (one 2r-entry table; SPEC_WALSH §5.2)",
    "walsh.exact_boundary": "gadget layer whose final Q_{p*} discarded only zeros (SPEC_WALSH §2.5)",
}


class Instrument:
    """Counters and monitors for one computation (or one test)."""

    def __init__(self, monitor_heights: bool = False):
        self.counts: Counter[str] = Counter()
        self.heights: dict[str, int] = {}
        self.monitor_heights = monitor_heights
        self.notes: list[tuple[str, object]] = []

    def hit(self, component: str, n: int = 1) -> None:
        self.counts[component] += n

    def height(self, key: str, *lists: list[int]) -> None:
        """Record the max numerator bit length seen under ``key`` (record-width monitor,
        manuscript eq. (record-width)).  No-op unless ``monitor_heights``."""
        if not self.monitor_heights:
            return
        m = self.heights.get(key, 0)
        for lst in lists:
            for v in lst:
                b = abs(v).bit_length()
                if b > m:
                    m = b
        self.heights[key] = m

    def note(self, key: str, value: object) -> None:
        self.notes.append((key, value))

    def merge(self, other: "Instrument") -> None:
        self.counts.update(other.counts)
        for k, v in other.heights.items():
            self.heights[k] = max(self.heights.get(k, 0), v)
        self.notes.extend(other.notes)

    def coverage_report(self) -> str:
        lines = ["component                 calls  source"]
        for name, src in COMPONENTS.items():
            c = self.counts.get(name, 0)
            mark = " " if c else "!"
            lines.append(f"{mark}{name:<24} {c:>6}  {src}")
        extra = sorted(set(self.counts) - set(COMPONENTS))
        for name in extra:
            lines.append(f"?{name:<24} {self.counts[name]:>6}  (unregistered)")
        return "\n".join(lines)
