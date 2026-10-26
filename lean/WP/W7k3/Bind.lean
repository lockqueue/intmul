import WP.W7k3.Ser

/-!
# WP.W7k3.Bind — the series contract in the binding shape of the W7 kernels

`W7S_series_bind : ∀ Mul, W5_mulAt Mul → growth → W7.Hyps → W7S_series Mul`. The `stdChar` and
`c0c1` kernels take `W7S_series Mul` as a hypothesis; with this lemma their binding forms
(`∀ Mul, W5_mulAt Mul → growth → W7.Hyps → W7_stdChar / W7_c0c1`) follow by projection.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts

/-- **The series sub-kernel from `W7.Hyps`.** -/
theorem W7S_series_bind : ∀ Mul : ℕ → ℕ, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) →
    W7.Hyps → W7S_series Mul := by
  intro Mul h5 hg hH
  obtain ⟨⟨hcopy, hdrop, -, hisz, -, -, -, -, -, -, -, -, -, hinc, hdec, -, -, -, -, -, haddI, -,
    -, -⟩, -, -, -, h6⟩ := hH
  exact W7S_series_holds Mul hg h5 hcopy hdrop hisz hdec hinc haddI h6

#assert_std_axioms W7S_series_bind

end WP.W7k3
