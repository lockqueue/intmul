import SubNLogN.Math.Bridge.FnewFinal
import SubNLogN.Math.Walsh.Proofs.Middle
import SubNLogN.Math.Walsh.Proofs.PhaseTable

/-!
# Bridge: the closed transform `F_newConcrete(K)` at the root

Proves the root contract for the closed transform `F_newConcreteK Kc ρ` (and `F_newConcrete ρ`)
of `SubNLogN/Math/Bridge/FnewFinal.lean`, whose roundings are `roundHalfUpR`, from the component
contracts `RootW8_FnewStmt` (Theorem 4.7 + Proposition 7.2 for `FnewOfR rr`), `TabConcrete_certifiedStmt`
(Lemma 4.6 (bridge Lemma C)(iii) for the concrete tables `TabConcreteR rr`), both instantiated at
`rr = roundHalfUpR` (a nearest rounding by `isNearestRounding_roundHalfUpR`), and
`Walsh.DirectFFTStmt` (Theorem 6.5); `Walsh.PhaseTableStmt` (Lemma 6.1) is used through its proof
`Walsh.phase_table`.

Route (helpers in the namespace `SubNLogN.Math.Bridge.FnewFinalProof`):
* both root inputs `x0 = rootPackV …` and `x1 = rootSquareV p0 K0 yF` have size `2^{K0}`, so
  `log₂` of the size is `K0` and both calls of `F_newConcreteK Kc ρ` take the bridge branch
  `FnewOfR roundHalfUpR ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ)` (`call_eq`);
* the tables are certified by `TabConcrete_certifiedStmt` at `rr = roundHalfUpR`;
* the middle `walshMid ρ p0 K0` is a middle transform with `E_mid = 12ℓ`, `δ_mid = 0` by
  `Walsh.walsh_middle_ideal_of`, whose side conditions come from `WalshOK` (`walshMid_isMiddle`);
* `RootW8_FnewStmt` with `rr = roundHalfUpR`, `Tab = TabConcreteR roundHalfUpR ρ`,
  `mid = walshMid ρ` gives the conclusion.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost

namespace FnewFinalProof

/-- The packed root input has `2^{K0}` entries. -/
theorem size_rootPackV (b K0 k1 k2 A B : ℕ) :
    (TMFw.Contracts.W9.rootPackV b K0 k1 k2 A B).size = 2 ^ K0 := by
  unfold TMFw.Contracts.W9.rootPackV
  simp [IntMul.size_runSequentialScanSteps]

/-- The squared root array has `2^{K0}` entries. -/
theorem size_rootSquareV (p0 K0 : ℕ) (y : Array (ℤ × ℤ)) :
    (TMFw.Contracts.W9.rootSquareV p0 K0 y).size = 2 ^ K0 := by
  unfold TMFw.Contracts.W9.rootSquareV
  simp [IntMul.size_runSequentialScanSteps]

/-- Under `WalshOK ρ p0 K0`, the Walsh middle with the ideal layer is a middle transform
(Definition 4.5) at `P = schedP p0 K0` with `E_mid = 12ℓ`, `δ_mid = 0` (Corollary 6.6, given Theorem 6.5). -/
theorem walshMid_isMiddle (hfft : Walsh.DirectFFTStmt) (ρ : RowExps) (p0 K0 : ℕ)
    (hOK : WalshOK ρ p0 K0 = true) :
    IsMiddleTransform (fnewShape ρ K0) (schedP p0 K0) (12 * (fnewL ρ K0 : ℝ)) 0
      (walshMid ρ p0 K0) := by
  obtain ⟨⟨hd, hl, -, hK1, hKl, -, -, hq, hlq⟩, -, -⟩ := (WalshOK_iff ρ p0 K0).1 hOK
  have ha : ∀ i, fnewA ρ K0 i = fnewL ρ K0 - 1 ∨ fnewA ρ K0 i = fnewL ρ K0 := by
    intro i
    unfold fnewA fnewL
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hD : 1 ≤ fnewD ρ K0 := by unfold fnewD; omega
  exact Walsh.walsh_middle_ideal_of hfft Walsh.phase_table (schedP p0 K0) (fnewD ρ K0)
    (fnewL ρ K0) (KK ρ K0) (fnewA ρ K0) hq hD hl hlq hK1 hKl ha

/-- At an input of size `2^{K0}`, with `cSpec.p` eligible (`WalshOK ρ cSpec.p K0`) and `Kc ≤ K0`,
`F_newConcreteK Kc ρ` takes the bridge branch
`FnewOfR roundHalfUpR ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ)`. -/
theorem call_eq (Kc : ℕ) (ρ : RowExps) (K0 p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (x : Array (ℤ × ℤ)) (hx : x.size = 2 ^ K0) (hK : Kc ≤ K0)
    (hOK : WalshOK ρ cSpec.p K0 = true) :
    F_newConcreteK Kc ρ p_in cSpec x =
      FnewOfR roundHalfUpR ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ) p_in cSpec x := by
  have hlog : Nat.log2 x.size = K0 := by rw [hx, Nat.log2_two_pow]
  exact F_newKR_eq_FnewOfR roundHalfUpR Kc ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ) p_in
    cSpec x (by rw [hlog]; exact hOK) (by rw [hlog]; exact hK)

end FnewFinalProof

open FnewFinalProof

/-- **Theorem 4.7 + Proposition 7.2 for the closed transform `F_newConcreteK Kc ρ`** (bridge branch):
`FnewConcreteK_rootStmt`, from `RootW8_FnewStmt` (instantiated at `rr = roundHalfUpR`,
`Tab = TabConcreteR roundHalfUpR ρ`, `mid = walshMid ρ`), `TabConcrete_certifiedStmt` (at
`rr = roundHalfUpR`) and Theorem 6.5 (`Walsh.DirectFFTStmt`). -/
theorem fnewConcreteK_root_of (hroot : RootW8_FnewStmt) (htab : TabConcrete_certifiedStmt)
    (hfft : Walsh.DirectFFTStmt) : FnewConcreteK_rootStmt := by
  intro Kc ρ b K0 k1 k2 A1 A2 cSpec hb hk hA1 hA2 hp hK hOK
  have hrr : IsNearestRounding roundHalfUpR := isNearestRounding_roundHalfUpR
  have hOK' : WalshOK ρ cSpec.p K0 = true := by rw [hp]; exact hOK
  have h1 := call_eq Kc ρ K0 b cSpec (TMFw.Contracts.W9.rootPackV b K0 k1 k2 A1 A2)
    (size_rootPackV _ _ _ _ _ _) hK hOK'
  have h2 := fun y => call_eq Kc ρ K0 (IntMul.rootPrecision b K0) cSpec
    (TMFw.Contracts.W9.rootSquareV (IntMul.rootPrecision b K0) K0 y) (size_rootSquareV _ _ _) hK
    hOK'
  have h := hroot roundHalfUpR hrr ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ) b K0 k1 k2 A1 A2
    cSpec hb hk hA1 hA2 hp hOK (htab roundHalfUpR hrr ρ _ K0 hOK) _ _
    (walshMid_isMiddle hfft ρ _ K0 hOK)
  simp only [] at h ⊢
  rw [h1, h2]
  exact h

/-- `FnewConcrete_rootStmt` (the cutoff `Kc = KstarOf ρ`), from the same hypotheses. -/
theorem fnewConcrete_root_of (hroot : RootW8_FnewStmt) (htab : TabConcrete_certifiedStmt)
    (hfft : Walsh.DirectFFTStmt) : FnewConcrete_rootStmt :=
  fnewConcrete_root_of_K (fnewConcreteK_root_of hroot htab hfft)

end SubNLogN.Math.Bridge
