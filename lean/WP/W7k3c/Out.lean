import WP.W7k3c.Comb
import WP.W7k3c.Lay

/-!
# WP.W7k3c.Out — the output phase of the `W7_c0c1` program

From the phase-3 layout `V3` (shared half-erf values on scratch `0 … 6`, `h³`, `h⁺`, `h⁻` on 7, 10,
11), `pOutPh`:
1. `pOutDrop`: drops the shared values (`VoA`: only `h³`, `h⁺`, `h⁻` left);
2. `pOutSet`: `B = pSub + 2` and `B_e = B + 2` by `pAff`, then `2^B` (int) on 1, `2^B_e` (nat) on 2,
   `0` (int) on 3 (`VoB`, the layout of `sComb`);
3. `pComb`: pushes `intSyms c0 ++ intSyms c1` on the destination (`WP.W7k3c.Comb`);
4. `pOutClean`: drops slots 10, 11, 7, 1, 2, 3, so the scratch is empty.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- Scratch after the shared values are dropped. -/
def VoA (hP hM h3 : ℤ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (fun _ => none)
    7 (some (.int h3))) 10 (some (.int hP))) 11 (some (.int hM))

/-- Scratch set up for `pComb`. -/
def VoB (ps : ℕ) (hP hM h3 : ℤ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (VoA hP hM h3)
    1 (some (.int ((2 ^ vB ps : ℕ) : ℤ)))) 2 (some (.nat (2 ^ vBe ps)))) 3 (some (.int 0))

/-! ## Programs -/

/-- Drop the shared half-erf values. -/
def pOutDrop (I : CI) : CP I :=
  (pDrI I 0).seq <| (pDrI I 1).seq <| (pDrN I 2).seq <| (pDrI I 3).seq <| (pDrN I 4).seq <|
  (pDrN I 5).seq (pDrN I 6)

/-- `2^B` (int) on 1, `2^B_e` (nat) on 2, `0` (int) on 3. -/
def pOutSet (I : CI) : CP I :=
  (pAff I 0 1 2 0).seq <| (pPow2 I 1 0).seq <| (pToInt I 1).seq <| (pDrN I 0).seq <|
  (pAff I 0 1 4 0).seq <| (pPow2 I 2 0).seq <| (pDrN I 0).seq <| (pPush I 3 0).seq (pToInt I 3)

/-- Empty the scratch after the combine. -/
def pOutClean (I : CI) : CP I :=
  (pDrI I 10).seq <| (pDrI I 11).seq <| (pDrI I 7).seq <| (pDrI I 1).seq <| (pDrN I 2).seq
    (pDrI I 3)

/-- **The output phase.** -/
def pOutPh (I : CI) : CP I :=
  (pOutDrop I).seq <| (pOutSet I).seq <| (pComb I).seq (pOutClean I)

/-! ## Closedness -/

theorem out_pAff_closed (I : CI) (α β γ : ℕ) (d : Fin 16) : (pAff I α β γ d).Closed :=
  ⟨pushBits_closed _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    cb_pDrI_closed I 12, cb_pDrI_closed I 13, pushBits_closed _ _, trivial, callI_closed _ _ _ _,
    trivial, callI_closed _ _ _ _, trivial, cb_pDrI_closed I 12, cb_pDrI_closed I 13,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pushBits_closed _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem out_pPow2_closed (I : CI) (j c : Fin 16) : (pPow2 I j c).Closed :=
  ⟨pushBits_closed _ _, callI_closed _ _ _ _⟩

theorem pOutPh_closed (I : CI) : (pOutPh I).Closed :=
  ⟨⟨cb_pDrI_closed I 0, cb_pDrI_closed I 1, callI_closed _ _ _ _, cb_pDrI_closed I 3,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    ⟨out_pAff_closed I 0 1 2 0, out_pPow2_closed I 1 0, trivial, callI_closed _ _ _ _,
      out_pAff_closed I 0 1 4 0, out_pPow2_closed I 2 0, callI_closed _ _ _ _,
      pushBits_closed _ _, trivial⟩,
    pComb_closed I,
    ⟨cb_pDrI_closed I 10, cb_pDrI_closed I 11, cb_pDrI_closed I 7, cb_pDrI_closed I 1,
      callI_closed _ _ _ _, cb_pDrI_closed I 3⟩⟩

#assert_std_axioms out_pAff_closed out_pPow2_closed pOutPh_closed

/-! ## Rules -/

section Rules

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {dv : List Sym}

include hI

theorem sOutDrop {pw ps r : ℕ} {hP hM h3 : ℤ}
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W)
    (bA : bitLen (vA pw ps) ≤ W) (bPd : bitLen (vP pw ps * 2 ^ vBint pw ps) ≤ W)
    (bDZ : bitLen (vDZ pw ps r) ≤ W) (bDS : bitLen (vDS pw ps r) ≤ W) :
    HT [] (St S (V3 pw ps r hP hM h3) dv) (pOutDrop I) (St S (VoA hP hM h3) dv) (7 * U C W) := by
  have b0 : bitLen ((vA pw ps : ℕ) : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact bA
  have b1 : bitLen ((2 ^ vBint pw ps : ℕ) : ℤ).natAbs ≤ W := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; unfold vBint; omega
  have b3 : bitLen ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ).natAbs ≤ W := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; unfold vS vBe; omega
  have b6 : bitLen (vN pw ps) ≤ W := le_trans (bitLen_le_self _) (by unfold vN; omega)
  unfold pOutDrop
  refine (HT.seq (sDrI (W := W) hI (S := S) (dv := dv) (V := V3 pw ps r hP hM h3) (x := 0)
      (z := ((vA pw ps : ℕ) : ℤ)) rfl b0) <|
    HT.seq (sDrI (W := W) hI (x := 1) (z := ((2 ^ vBint pw ps : ℕ) : ℤ)) rfl b1) <|
    HT.seq (sDrN (W := W) hI (x := 2) (a := vP pw ps * 2 ^ vBint pw ps) rfl bPd) <|
    HT.seq (sDrI (W := W) hI (x := 3) (z := ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ)) rfl b3) <|
    HT.seq (sDrN (W := W) hI (x := 4) (a := vDZ pw ps r) rfl bDZ) <|
    HT.seq (sDrN (W := W) hI (x := 5) (a := vDS pw ps r) rfl bDS) <|
    sDrN (W := W) hI (x := 6) (a := vN pw ps) rfl b6).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sOutSet {pw ps : ℕ} {hP hM h3 : ℤ} {r0 r1 : List Sym}
    (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1) (lin : 400 * pw + 4 * ps + 500 ≤ W) :
    HT [] (St S (VoA hP hM h3) dv) (pOutSet I) (St S (VoB ps hP hM h3) dv) (55 * U C W) := by
  have hWa : ∀ γ, γ ≤ 4 → 0 * pw + 1 * ps + γ + 0 + 1 + pw + ps < 2 ^ W := fun γ hγ =>
    (bitLen_le_iff W _).1 (le_trans (bitLen_le_self _) (by omega))
  have bB : bitLen (vB ps) ≤ W := le_trans (bitLen_le_self _) (by unfold vB; omega)
  have bBe : bitLen (vBe ps) ≤ W := le_trans (bitLen_le_self _) (by unfold vBe; omega)
  have hW1 : 1 ≤ W := by omega
  unfold pOutSet
  refine (HT.seq (sAff' (W := W) hI (S := S) (dv := dv) (V := VoA hP hM h3) h0 hr0 h1 hr1 0 1 2 0
      (by decide) rfl rfl rfl rfl rfl (hWa 2 (by norm_num)) (vB ps) (by unfold vB; omega)) <|
    HT.seq (sPow2 (W := W) hI (j := 1) (c := 0) (k := vB ps) (by decide) rfl rfl
      (by unfold vB; omega) hW1) <|
    HT.seq (sToInt (W := W) hI (j := 1) (a := 2 ^ vB ps) rfl) <|
    HT.seq (sDrN (W := W) hI (x := 0) (a := vB ps) rfl bB) <|
    HT.seq (sAff' (W := W) hI h0 hr0 h1 hr1 0 1 4 0 (by decide) rfl rfl rfl rfl rfl
      (hWa 4 le_rfl) (vBe ps) (by unfold vBe; omega)) <|
    HT.seq (sPow2 (W := W) hI (j := 2) (c := 0) (k := vBe ps) (by decide) rfl rfl
      (by unfold vBe; omega) hW1) <|
    HT.seq (sDrN (W := W) hI (x := 0) (a := vBe ps) rfl bBe) <|
    HT.seq (sPush (W := W) hI 3 0 rfl (by simp [bitLen_zero])) <|
    sToInt (W := W) hI (j := 3) (a := 0) rfl).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sOutClean {ps : ℕ} {hP hM h3 : ℤ} (bP : bitLen hP.natAbs ≤ W)
    (bM : bitLen hM.natAbs ≤ W) (b3 : bitLen h3.natAbs ≤ W) (bB : bitLen (2 ^ vB ps) ≤ W)
    (bBe : bitLen (2 ^ vBe ps) ≤ W) :
    HT [] (St S (VoB ps hP hM h3) dv) (pOutClean I) (St S (fun _ => none) dv) (6 * U C W) := by
  have bB' : bitLen ((2 ^ vB ps : ℕ) : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact bB
  unfold pOutClean
  refine (HT.seq (sDrI (W := W) hI (S := S) (dv := dv) (V := VoB ps hP hM h3) (x := 10) (z := hP)
      rfl bP) <|
    HT.seq (sDrI (W := W) hI (x := 11) (z := hM) rfl bM) <|
    HT.seq (sDrI (W := W) hI (x := 7) (z := h3) rfl b3) <|
    HT.seq (sDrI (W := W) hI (x := 1) (z := ((2 ^ vB ps : ℕ) : ℤ)) rfl bB') <|
    HT.seq (sDrN (W := W) hI (x := 2) (a := 2 ^ vBe ps) rfl bBe) <|
    sDrI (W := W) hI (x := 3) (z := 0) rfl (by simp [bitLen_zero])).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **The output phase**: from `V3`, push `intSyms c0 ++ intSyms c1` on the destination and leave
the scratch empty. `K = 120`. -/
theorem sOutPh {pw ps r u2 : ℕ} {hP hM h3 : ℤ} {r0 r1 r2 r3 : List Sym}
    (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (h2 : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2)
    (h3' : S (.inl 3) = natSyms u2 ++ r3) (hr3 : TermOK r3)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W)
    (bA : bitLen (vA pw ps) ≤ W) (bPd : bitLen (vP pw ps * 2 ^ vBint pw ps) ≤ W)
    (bDZ : bitLen (vDZ pw ps r) ≤ W) (bDS : bitLen (vDS pw ps r) ≤ W)
    (hw : CombW W (vB ps) (vBe ps) r u2 hP hM h3) :
    HT [] (St S (V3 pw ps r hP hM h3) dv) (pOutPh I)
      (St S (fun _ => none) (intSyms (c0c1Comb (vB ps) (vBe ps) r u2 hP hM h3).1 ++
        intSyms (c0c1Comb (vB ps) (vBe ps) r u2 hP hM h3).2 ++ dv)) (120 * U C W) := by
  unfold pOutPh
  refine (HT.seq (sOutDrop (W := W) hI (S := S) (dv := dv) (hP := hP) (hM := hM) (h3 := h3) lin bA bPd bDZ
      bDS) <|
    HT.seq (sOutSet (W := W) hI (S := S) (dv := dv) (hP := hP) (hM := hM) (h3 := h3) h0 hr0 h1 hr1
      (by omega)) <|
    HT.seq (sComb (W := W) hI (S := S) (V := VoB ps hP hM h3) (dv := dv) (B := vB ps)
      (Be := vBe ps) (r := r) (u2 := u2) (hP := hP) (hM := hM) (h3 := h3) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h2 hr2 h3' hr3 hw) <|
    sOutClean (W := W) hI hw.bP hw.bM hw.b3 hw.bB hw.bBe).mono (by omega)

#assert_std_axioms sOutDrop sOutSet sOutClean sOutPh

end Rules

end WP.W7k3c
