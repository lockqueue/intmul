import WP.W9ex.Extract

/-!
# WP.W9ex.Concrete — concrete witness exports for `W9_extract`

`W9_extract_proved` needs no machine-contract hypotheses, so its witness is already concrete: the
program `extractProg` over `BLoc 4` with registers `Option Sym`, built only from framework macros.
Exports: `mC`, `RC`, `r0C`, `progC` (= `WP.W9ex.extractProg`, the witness of `W9_extract_proved`),
`hmC`, `closedC`, the contract body `specC` (cost constant `64`), and `W9_extract_of_concrete`
(the contract rebuilt from these exports).
-/

namespace WP.W9ex.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- Scratch count of the witness. -/
abbrev mC : ℕ := 4

/-- Register type of the witness. -/
abbrev RC : Type := Option Sym

/-- Initial registers. -/
def r0C : RC := none

/-- The witness program of `W9_extract_proved`. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := WP.W9ex.extractProg

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := WP.W9ex.extractProg_closed

/-- The contract body of `W9_extract` for `progC`, cost constant `64`. -/
theorem specC : ∀ (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) (σ : BLoc mC → List Sym)
    (restS r0 : List Sym), v.size = 2 ^ K0 → k1 + k2 ≤ 2 ^ K0 → ArrW wR v →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .S) = streamSyms [v] ++ restS →
    Runs progC σ (Function.update (Function.update σ (.inl .S) restS) (.inl .OA)
        (hdrSyms (rootDigits b K0 k1 k2 v) ++ σ (.inl .OA))) (fun _ => True)
      (64 * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1)) := by
  intro b K0 k1 k2 wR v σ restS r0 hv hk hw hC0 hS
  have h := xt_extract σ b K0 k1 k2 wR v restS r0 hv hk hw hC0 hS
  rw [← rootDigits_eq_mdig b K0 k1 k2 v hv hk] at h
  exact h.runs

/-- `W9_extract` rebuilt from the concrete exports. -/
theorem W9_extract_of_concrete : W9_extract :=
  ⟨64, fun _ => ⟨mC, RC, progC, hmC, inferInstance, ⟨r0C⟩, closedC, specC⟩⟩

#assert_std_axioms hmC closedC specC W9_extract_of_concrete

end WP.W9ex.Concrete
