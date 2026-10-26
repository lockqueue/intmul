import WP.W7sc.Main
import WP.W7k3.Bind
import WP.W7k1.Pi

/-!
# WP.W7k3.StdChar — `W7_stdChar` in the binding shape of the W7 kernels

`W7_stdChar_bind : ∀ Mul, W5_mulAt Mul → growth → W7.Hyps → W7_stdChar`, from
* `WP.W7sc.W7_stdChar_holds` (`WP.W7sc`): the `stdChar` kernel proved over the series contract;
* `W7S_series_bind` (this package): the series contract from `W7.Hyps`;
* `WP.W7k1.W7_piScaled_holds` (W7k1): the `π` kernel from W3 contracts;
* the W3 / W6a conjuncts of `W7.Hyps`.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts

/-- **`W7_stdChar` from `W7.Hyps`** (binding shape). -/
theorem W7_stdChar_bind : ∀ Mul : ℕ → ℕ, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) →
    W7.Hyps → W7_stdChar := by
  intro Mul h5 hg hH
  have hser := W7S_series_bind Mul h5 hg hH
  obtain ⟨⟨hcopy, hdrop, -, hisz, -, hadd, hsub, hshl, hshr, hshlV, hshrV, -, -, hinc, hdec, -, -,
    -, hng, -, haddI, -, -, -⟩, -, -, -, h6⟩ := hH
  exact WP.W7sc.W7_stdChar_holds Mul hg h5 hser hcopy hdrop hisz hdec hinc haddI hadd hshl hshlV
    hng h6 (WP.W7k1.W7_piScaled_holds hcopy hinc hshl hshlV hadd hsub hshrV hshr hdrop hisz hdec)

#assert_std_axioms W7_stdChar_bind

end WP.W7k3
