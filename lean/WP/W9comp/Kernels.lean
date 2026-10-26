import WP.W9comp.PreNode
import WP.W9comp.PostNode

/-!
# WP.W9comp.Kernels — `W9_kernels_of_machine` from the stage theorems

The W9 stage kernels are proved modularly in their respective sub-packages; accordingly,
their theorems are **hypotheses** here, bundled in `W9StageThms`. They use the uniform binding
shape across all stage theorems:
* a multiplication kernel is `∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → Kernel Mul`;
* any other kernel is `W3_all → W4_all → W6a_all → Kernel`.

A stage theorem that needs fewer machine contracts fits this shape by projection
(`fun _ h4 _ => thm h4.1`) at top-level composition.

* `W9_kernels_of_machine_holds`: `W5_toom3Mul` gives one triple `c0 c1 w0` with
  `W5_mulAt (T3 c0 c1 w0)` (`W5_toom3Mul_iff_mulAt`, `Iff.rfl`). Every multiplication kernel is
  instantiated at that **single** `Mul := T3 c0 c1 w0`.
* `W9_nodes_of_machine`: the node kernels (`W9_preNode`, `W9_leafFFT`, `W9_postNode`) at the same
  shared `Mul`, via `W9_preNode_of_phases_holds` and `W9_postNode_of_phases_holds`. These are the
  inputs of `W9_levels_of_kernels`.
-/

namespace WP.W9comp

open TMFw TMFw.Contracts

/-- **The W9 stage theorems**, in the binding shape (multiplication kernels quantify over `Mul`
under `W5_mulAt Mul`). -/
structure W9StageThms : Prop where
  preTranspose : W3_all → W4_all → W6a_all → W9_preTranspose
  altSum : W3_all → W4_all → W6a_all → W9_altSum
  spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul
  preTwist : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_preTwist Mul
  synFFT : W3_all → W4_all → W6a_all → W9_synFFT
  postTwist : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_postTwist Mul
  emitRows : W3_all → W4_all → W6a_all → W9_emitRows
  postTranspose : W3_all → W4_all → W6a_all → W9_postTranspose
  columnRoutes : W3_all → W4_all → W6a_all → W9_columnRoutes
  columns : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul
  postOutput : W3_all → W4_all → W6a_all → W9_postOutput
  leafFFT : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_leafFFT Mul
  splitPack : W3_all → W4_all → W6a_all → W9_splitPack
  square : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul
  extract : W3_all → W4_all → W6a_all → W9_extract
  reconstruct : W3_all → W4_all → W6a_all → W9_reconstruct
  retFlip : W3_all → W4_all → W6a_all → W9_retFlip
  sweep : W3_all → W4_all → W6a_all → W9_sweep
  level : W3_all → W4_all → W6a_all → W9_level

/-- **`W9_kernels_of_machine`** from the stage theorems: all kernels from W3, W4, W6a and W5, with
one shared multiplication cost `T3 c0 c1 w0`. -/
theorem W9_kernels_of_machine_holds (H : W9StageThms) : W9_kernels_of_machine := by
  intro h3 h4 h6 h5
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  exact ⟨c0, c1, w0, H.preTranspose h3 h4 h6, H.altSum h3 h4 h6, H.spread _ hM h3 h4 h6,
    H.preTwist _ hM h3 h4 h6, H.synFFT h3 h4 h6, H.postTwist _ hM h3 h4 h6, H.emitRows h3 h4 h6,
    H.postTranspose h3 h4 h6, H.columnRoutes h3 h4 h6, H.columns _ hM h3 h4 h6,
    H.postOutput h3 h4 h6, H.leafFFT _ hM h3 h4 h6, H.splitPack h3 h4 h6, H.square _ hM h3 h4 h6,
    H.extract h3 h4 h6, H.reconstruct h3 h4 h6, H.retFlip h3 h4 h6, H.sweep h3 h4 h6,
    H.level h3 h4 h6⟩

/-- The node kernels at the shared `Mul`, from the phase kernels and the two composites. -/
theorem W9_nodes_of_machine (H : W9StageThms) (h3 : W3_all) (h4 : W4_all) (h6 : W6a_all)
    (h5 : W5_toom3Mul) : ∃ c0 c1 w0 : ℕ,
      W9_preNode (T3 c0 c1 w0) ∧ W9_leafFFT (T3 c0 c1 w0) ∧ W9_postNode (T3 c0 c1 w0) := by
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  exact ⟨c0, c1, w0,
    W9_preNode_of_phases_holds _ (H.preTranspose h3 h4 h6) (H.altSum h3 h4 h6)
      (H.spread _ hM h3 h4 h6) (H.preTwist _ hM h3 h4 h6) (H.synFFT h3 h4 h6)
      (H.postTwist _ hM h3 h4 h6) (H.emitRows h3 h4 h6),
    H.leafFFT _ hM h3 h4 h6,
    W9_postNode_of_phases_holds _ (H.postTranspose h3 h4 h6) (H.columnRoutes h3 h4 h6)
      (H.columns _ hM h3 h4 h6) (H.postOutput h3 h4 h6)⟩

#assert_std_axioms W9_kernels_of_machine_holds W9_nodes_of_machine

end WP.W9comp
