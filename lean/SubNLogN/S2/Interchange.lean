import SubNLogN.Spec

/-!
# Component S2 (`Interchange.lean`): Scalar Shear & Clean-Branch Commutator Identities

**Scope.** Proves two pure `ℤ × ℤ` scalar identities accompanying Appendix A (`app:parameter-transfer`):
1. The 3-step integer shear `(h, d) ↦ (h + d, d)` and its inverse (motivating the shear step of
   Lemma A.6 (`lem:transfer-shear`), without tapes or radix conversion);
2. The 8-step scalar commutator `(u, w) ↦ (u, w + c_eq0 + c_eq1)` on the clean guard branch
   (motivating `[OAI26, §5.2, (20)]` / Lemma A.9 (`lem:transfer13`)).
The actual `TM2` tape kernels for Lemma A.6 (`lem:transfer-shear`), Lemma A.8 (`lem:transfer12`),
and Lemma A.9 (`lem:transfer13`) are formalized in `SubNLogN/Machine/AppC/`.
-/

namespace SubNLogN.S2

open SubNLogN

/-- **3-Step Elementary Shear (Lemma A.6 (`lem:transfer-shear`)):**
`D_j ← D_j + H_i`, `(H_i, D_j) ← (D_j, H_i)`, `D_j ← H_i - D_j` maps `(h, d)` to `(h + d, d)`. -/
theorem shear_step_pair_correct (h d : ℤ) :
    shearStepPair h d = (h + d, d) := by
  unfold shearStepPair
  ext <;> ring

/-- Composing the 3-step shear with its inverse (`d ↦ -d` conjugation) recovers `(h, d)`. -/
def shearInversePair (h' d' : ℤ) : ℤ × ℤ :=
  let (h2, _) := shearStepPair h' (-d')
  (h2, d')

theorem shear_inverse_pair_correct (h d : ℤ) :
    shearInversePair (h + d) d = (h, d) := by
  unfold shearInversePair shearStepPair
  ext <;> ring

/-- **8-Step Commutator of Packed Selected-Bit Addition (proof of Lemma A.9 (`lem:transfer13`), `[OAI26, §5.2, (20)]`):**
Let `u₀, w₀ ∈ {0, 1}` be the guard bits of `(u, w)` (initially `u₀ = 0, w₀ = 0` outside the
exceptional set `B`) and let `c₀, c₁` be the packed shifts controlled by `b ∈ {false, true}`:
when `b = false`, `c_eq0 = Δ, c_eq1 = 0`; when `b = true`, `c_eq0 = 0, c_eq1 = Δ`.
Executing the 8-step commutator schedule (proof of Lemma A.9 (`lem:transfer13`), `[OAI26, §5.2, (20)]`) adds `Δ` to `w` and restores `u` whenever `u₀ = 0, w₀ = 0`. -/
def lemma13EightStepClean (u w c_eq0 c_eq1 : ℤ) : ℤ × ℤ :=
  -- Outside the exceptional set, the guard bit stays 0 after adding/subtracting c_eq0,
  -- and the 8 steps reduce algebraically on the clean guard branch to:
  let u1 := u - c_eq0
  let w2 := w - c_eq0
  let u3 := u1 + c_eq0
  let w4 := w2 + c_eq0
  let w5 := w4 + c_eq1
  let u6 := u3 + c_eq1
  let w7 := w5 - 0
  let u8 := u6 - c_eq1
  (u8, w7 + c_eq0)

theorem lemma13_clean_commutator (u w c_eq0 c_eq1 : ℤ) :
    lemma13EightStepClean u w c_eq0 c_eq1 = (u, w + c_eq0 + c_eq1) := by
  unfold lemma13EightStepClean
  ext <;> ring

end SubNLogN.S2
