import WP.W11b.Root
import WP.W11b.Leaf

/-!
# WP.W11b.Final — the W11b deliverable, hypothesis-free

Both W11b hypotheses of `intMul_TM2_nlogn_current2` (`IntMulTM.Remaining`):
* `hroot : WP.Top.W9RootOK wdF wdI wR`;
* `hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw·(log₂ n + 1) ∧ wdI n ℓ ≤ … ∧ wR n ≤ …`,

at `wdF = wdI = fun n _ => wdHead n` and `wR = wRHead`
(`wdHead n = 2·p0 + 3 + 4·specW (hSpec n)`, `wRHead n = 4·p0`; `width_bound` gives `cw = 787`).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

/-- **W11b**: `W9RootOK` and the `O(log n)` width bound at the headline width profiles. -/
theorem w11b_final :
    WP.Top.W9RootOK (fun n _ => wdHead n) (fun n _ => wdHead n) wRHead ∧
      ∃ cw, ∀ n ≥ 1, ∀ ℓ : ℕ, (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧
        (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wRHead n ≤ cw * (Nat.log2 n + 1) :=
  w11b_main leafChainOK root_parts

/-- `hroot` of `intMul_TM2_nlogn_current2`. -/
theorem w9RootOK_headline :
    WP.Top.W9RootOK (fun n _ => wdHead n) (fun n _ => wdHead n) wRHead :=
  w11b_final.1

/-- `hw` of `intMul_TM2_nlogn_current2`. -/
theorem widths_headline :
    ∃ cw, ∀ n ≥ 1, ∀ ℓ : ℕ, (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wRHead n ≤ cw * (Nat.log2 n + 1) :=
  w11b_final.2

#assert_std_axioms w11b_final w9RootOK_headline widths_headline

end WP.W11b
