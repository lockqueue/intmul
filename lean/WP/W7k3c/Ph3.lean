import WP.W7k3c.Comb
import WP.W7k3c.Lay

/-!
# WP.W7k3c.Ph3 — phase 3: the three half-erf evaluations

From the shared values on scratch `0 … 6` and the numerators `r + 2u2'`, `r - 2u2'`, `3r - 2u2'`
on 7, 8, 9, compute `h₊`, `h₋`, `h₃` onto 10, 11, 7 (`pHe` three times, 54 steps).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- Phase 3. -/
def pPh3 (I : CI) : CP I := (pHe I 7 10).seq <| (pHe I 8 11).seq (pHe I 9 7)

theorem pHe_closed (I : CI) (i o : Fin 16) : (pHe I i o).Closed :=
  ⟨trivial, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    cb_pDrI_closed I 13, callI_closed _ _ _ _, cb_pDrI_closed I 12, callI_closed _ _ _ _,
    cb_pDrI_closed I 13, callI_closed _ _ _ _, cb_pDrI_closed I 12, cb_pDrI_closed I 14,
    callI_closed _ _ _ _, cb_pDrI_closed I 13, callI_closed _ _ _ _, cb_pDrI_closed I 12,
    cb_pDrI_closed I i⟩

theorem pPh3_closed (I : CI) : (pPh3 I).Closed :=
  ⟨pHe_closed I 7 10, pHe_closed I 8 11, pHe_closed I 9 7⟩

/-- The scratch contents after phase 2. -/
def V2 (pw ps r u2 : ℕ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (V1 pw ps r) 7 (some (.nat (vXp r u2))))
    8 (some (.nat (vXm r u2)))) 9 (some (.nat (vX3 r u2)))

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C) {S : HL → List Sym} {dv : List Sym}

include hI

theorem sPh3 {pw ps r u2 : ℕ} (hw : Wid W pw ps r u2) :
    HT [] (St S (V2 pw ps r u2) dv) (pPh3 I)
      (St S (V3 pw ps r (vH pw ps r (vXp r u2)) (vH pw ps r (vXm r u2)) (vH pw ps r (vX3 r u2))) dv)
      (54 * U C W) := by
  unfold pPh3
  refine (HT.seq (sHe (W := W) hI (i := 7) (o := 10) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hw.heP) <|
    HT.seq (sHe (W := W) hI (i := 8) (o := 11) (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hw.heM) <|
    sHe (W := W) hI (i := 9) (o := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hw.he3).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

end

#assert_std_axioms pHe_closed pPh3_closed sPh3

end WP.W7k3c
