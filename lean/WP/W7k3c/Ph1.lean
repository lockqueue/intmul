import WP.W7k3c.Lay

/-!
# WP.W7k3c.Ph1 — phase 1 of the `W7_c0c1` program: the shared constants

From `p_work`, `pSub`, `r` on the named stacks `0`, `1`, `2`, `pPh1` leaves the seven shared
half-erf arguments `V1` on scratch `0 … 6` (`A`, `2^Bint`, `P·2^Bint`, `2^(S+B_e)`, `denZ`, `denZ²`,
`N`); every other scratch stack ends empty. Seven stages, each proved between explicit
intermediate scratch states `ph1_Va … ph1_Vf`:

| stage | result | cost (`U C W`) |
|---|---|---|
| `ph1_p1` | `vLn` on 9, `vP` on 10 (`π`, `ln 2` at `vS2`) | 30 |
| `ph1_p2` | `vA` on 0 (integer) | 34 |
| `ph1_p3` | `2^vBint` on 1 (integer), `vP·2^vBint` on 2 | 30 |
| `ph1_p4` | `2^(vS+vBe)` on 3 (integer) | 27 |
| `ph1_p5` | `vDZ` on 4 | 29 |
| `ph1_p6` | `vDS` on 5 | 8 |
| `ph1_p7` | `vN` on 6 | 23 |

Total: `181·U C W`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-! ## The program -/

section Prog

variable (I : CI)

/-- Stage 1: `vS2` on 7; `π`, `ln 2` at `vS2` on 8, 9 (made natural); `vP = √vPi` on 10. -/
def ph1_p1 : CP I :=
  (pAff I 32 2 24 7).seq <| (pPi I 7 8).seq <| (pLn I 7 9).seq <| (pDrN I 7).seq <|
  (pToNat I 8).seq <| (pToNat I 9).seq <| (pIsq I 8 10).seq (pDrN I 8)

/-- Stage 2: `vA = √(4·p·vLn)` on 0 (made an integer); `vLn` dropped. -/
def ph1_p2 : CP I :=
  (pAff I 4 0 0 7).seq <| (pMulN I 7 9 8).seq <| (pDrN I 7).seq <| (pDrN I 9).seq <|
  (pIsq I 8 0).seq <| (pDrN I 8).seq (pToInt I 0)

/-- Stage 3: `2^vBint` on 1 (made an integer), `vP·2^vBint` on 2; `vP` dropped. -/
def ph1_p3 : CP I :=
  (pAff I 352 3 40 7).seq <| (pPow2 I 1 7).seq <| (pToInt I 1).seq <| (pCp I (.inr 10) 2).seq <|
  (pShl I 2 7).seq <| (pDrN I 7).seq (pDrN I 10)

/-- Stage 4: `2^(vS+vBe)` on 3 (made an integer). -/
def ph1_p4 : CP I :=
  (pAff I 16 2 16 7).seq <| (pPow2 I 3 7).seq <| (pToInt I 3).seq (pDrN I 7)

/-- Stage 5: `vDZ = 2r·2^vS` on 4. -/
def ph1_p5 : CP I :=
  (pAff I 16 1 12 7).seq <| (pCp I (.inl 2) 4).seq <| (pDbl I 4 8).seq <| (pShl I 4 7).seq <|
  pDrN I 7

/-- Stage 6: `vDS = vDZ²` on 5. -/
def ph1_p6 : CP I := (pCp I (.inr 4) 7).seq <| (pMulN I 4 7 5).seq (pDrN I 7)

/-- Stage 7: `vN` on 6. -/
def ph1_p7 : CP I := pAff I 136 1 13 6

/-- **Phase 1** of the `W7_c0c1` program: the shared half-erf arguments `V1` on scratch `0 … 6`. -/
def pPh1 : CP I :=
  (ph1_p1 I).seq <| (ph1_p2 I).seq <| (ph1_p3 I).seq <| (ph1_p4 I).seq <| (ph1_p5 I).seq <|
  (ph1_p6 I).seq (ph1_p7 I)

/-! ## Closedness -/

theorem ph1_push_closed (j : Fin 16) (c : ℕ) : (pPush I j c).Closed := pushBits_closed _ _

theorem ph1_drI_closed (x : Fin 16) : (pDrI I x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem ph1_aff_closed (α β γ : ℕ) (d : Fin 16) : (pAff I α β γ d).Closed :=
  ⟨ph1_push_closed I 12 α, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    ph1_drI_closed I 12, ph1_drI_closed I 13, ph1_push_closed I 12 β, trivial,
    callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, ph1_drI_closed I 12,
    ph1_drI_closed I 13, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    ph1_push_closed I 13 γ, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem ph1_mulN_closed (x y z : Fin 16) : (pMulN I x y z).Closed :=
  ⟨trivial, trivial, callI_closed _ _ _ _, trivial, trivial, trivial⟩

theorem ph1_pow2_closed (j c : Fin 16) : (pPow2 I j c).Closed :=
  ⟨ph1_push_closed I j 1, callI_closed _ _ _ _⟩

theorem ph1_dbl_closed (x t : Fin 16) : (pDbl I x t).Closed :=
  ⟨ph1_push_closed I t 1, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem ph1_p1_closed : (ph1_p1 I).Closed :=
  ⟨ph1_aff_closed I 32 2 24 7, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    trivial, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem ph1_p2_closed : (ph1_p2 I).Closed :=
  ⟨ph1_aff_closed I 4 0 0 7, ph1_mulN_closed I 7 9 8, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, trivial⟩

theorem ph1_p3_closed : (ph1_p3 I).Closed :=
  ⟨ph1_aff_closed I 352 3 40 7, ph1_pow2_closed I 1 7, trivial, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem ph1_p4_closed : (ph1_p4 I).Closed :=
  ⟨ph1_aff_closed I 16 2 16 7, ph1_pow2_closed I 3 7, trivial, callI_closed _ _ _ _⟩

theorem ph1_p5_closed : (ph1_p5 I).Closed :=
  ⟨ph1_aff_closed I 16 1 12 7, callI_closed _ _ _ _, ph1_dbl_closed I 4 8, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem ph1_p6_closed : (ph1_p6 I).Closed :=
  ⟨callI_closed _ _ _ _, ph1_mulN_closed I 4 7 5, callI_closed _ _ _ _⟩

theorem ph1_p7_closed : (ph1_p7 I).Closed := ph1_aff_closed I 136 1 13 6

theorem pPh1_closed : (pPh1 I).Closed :=
  ⟨ph1_p1_closed I, ph1_p2_closed I, ph1_p3_closed I, ph1_p4_closed I, ph1_p5_closed I,
    ph1_p6_closed I, ph1_p7_closed I⟩

end Prog

/-! ## Intermediate scratch states -/

/-- After stage 1. -/
def ph1_Va (pw ps : ℕ) : Fin 16 → Option Val :=
  Function.update (Function.update (fun _ => none)
    9 (some (.nat (vLn pw ps))))
    10 (some (.nat (vP pw ps)))

/-- After stage 2. -/
def ph1_Vb (pw ps : ℕ) : Fin 16 → Option Val :=
  Function.update (Function.update (fun _ => none)
    0 (some (.int ((vA pw ps : ℕ) : ℤ))))
    10 (some (.nat (vP pw ps)))

/-- After stage 3: the first three slots of `V1`. -/
def ph1_Vc (pw ps : ℕ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (fun _ => none)
    0 (some (.int ((vA pw ps : ℕ) : ℤ))))
    1 (some (.int ((2 ^ vBint pw ps : ℕ) : ℤ))))
    2 (some (.nat (vP pw ps * 2 ^ vBint pw ps)))

/-- After stage 4. -/
def ph1_Vd (pw ps : ℕ) : Fin 16 → Option Val :=
  Function.update (ph1_Vc pw ps) 3 (some (.int ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ)))

/-- After stage 5. -/
def ph1_Ve (pw ps r : ℕ) : Fin 16 → Option Val :=
  Function.update (ph1_Vd pw ps) 4 (some (.nat (vDZ pw ps r)))

/-- After stage 6. -/
def ph1_Vf (pw ps r : ℕ) : Fin 16 → Option Val :=
  Function.update (ph1_Ve pw ps r) 5 (some (.nat (vDS pw ps r)))

theorem ph1_V1 (pw ps r : ℕ) :
    Function.update (ph1_Vf pw ps r) 6 (some (.nat (vN pw ps))) = V1 pw ps r := rfl

theorem ph1_lt {W x : ℕ} (h : x ≤ W) : x < 2 ^ W := lt_of_le_of_lt h Nat.lt_two_pow_self

theorem ph1_bl {W x : ℕ} (h : x ≤ W) : bitLen x ≤ W := le_trans (bitLen_le_self x) h

/-! ## Copy rules with implicit slots -/

section Rules

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem ph1_sCpS {x j : Fin 16} {a : ℕ} (hxj : x ≠ j) (hx : V x = some (.nat a))
    (hj : V j = none) (ha : bitLen a ≤ W) :
    HT [] (St S V dv) (pCp I (.inr x) j) (St S (Function.update V j (some (.nat a))) dv) (U C W) :=
  sCp (W := W) hI (.inr x) j (nd2 hxj) (St_nat S V dv hx) (termOK_mark _) hj ha

theorem ph1_sCp2 {j : Fin 16} {r : ℕ} {r2 : List Sym} (h2 : S (.inl 2) = natSyms r ++ r2)
    (hr2 : TermOK r2) (hj : V j = none) (ha : bitLen r ≤ W) :
    HT [] (St S V dv) (pCp I (.inl 2) j) (St S (Function.update V j (some (.nat r))) dv) (U C W) :=
  sCp (W := W) hI (.inl 2) j (by simp) h2 hr2 hj ha

end Rules

#assert_std_axioms ph1_push_closed ph1_drI_closed ph1_aff_closed ph1_mulN_closed ph1_pow2_closed
  ph1_dbl_closed ph1_p1_closed ph1_p2_closed ph1_p3_closed ph1_p4_closed ph1_p5_closed
  ph1_p6_closed ph1_p7_closed pPh1_closed ph1_V1 ph1_lt ph1_bl ph1_sCpS ph1_sCp2

/-! ## The seven stages -/

section Stages

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C) {S : HL → List Sym}
  {dv : List Sym} {pw ps r : ℕ} {r0 r1 : List Sym}

include hI

theorem ph1_s1 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) (bPi : bitLen (vPi pw ps) ≤ W) :
    HT [] (St S (fun _ => none) dv) (ph1_p1 I) (St S (ph1_Va pw ps) dv) (30 * U C W) := by
  have hS2 : vS2 pw ps ≤ W := by unfold vS2; omega
  have hS1 : 1 ≤ vS2 pw ps := by unfold vS2; omega
  unfold ph1_p1
  refine (HT.seq (sAff' (W := W) (V := fun _ => none) hI h0 hr0 h1 hr1 32 2 24 7 (by decide)
      rfl rfl rfl rfl rfl (ph1_lt (by omega)) (vS2 pw ps) rfl) <|
    HT.seq (sPi (W := W) hI (x := 7) (z := 8) (B := vS2 pw ps) (by decide) rfl rfl hS2) <|
    HT.seq (sLn (W := W) hI (x := 7) (z := 9) (B := vS2 pw ps) (by decide) rfl rfl hS2) <|
    HT.seq (sDrN (W := W) hI (x := 7) (a := vS2 pw ps) rfl (ph1_bl hS2)) <|
    HT.seq (sToNat (W := W) hI (j := 8) (z := (IntMul.computablePiScaledWithCost (vS2 pw ps)).1)
      rfl (piScaled_nonneg _)) <|
    HT.seq (sToNat (W := W) hI (j := 9)
      (z := (IntMul.computableLog2ScaledWithCost (vS2 pw ps)).1) rfl
      (by have := log2Scaled_pos (vS2 pw ps) hS1; omega)) <|
    HT.seq (sIsq (W := W) hI (x := 8) (z := 10) (a := vPi pw ps) (by decide) rfl rfl bPi) <|
    sDrN (W := W) hI (x := 8) (a := vPi pw ps) rfl bPi).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s2 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) (bLn : bitLen (vLn pw ps) ≤ W)
    (bAL : bitLen (4 * pw * vLn pw ps) ≤ W) :
    HT [] (St S (ph1_Va pw ps) dv) (ph1_p2 I) (St S (ph1_Vb pw ps) dv) (34 * U C W) := by
  have b4 : bitLen (4 * pw) ≤ W := ph1_bl (by omega)
  unfold ph1_p2
  refine (HT.seq (sAff' (W := W) (V := ph1_Va pw ps) hI h0 hr0 h1 hr1 4 0 0 7 (by decide)
      rfl rfl rfl rfl rfl (ph1_lt (by omega)) (4 * pw) (by omega)) <|
    HT.seq (sMulN (W := W) hI (x := 7) (y := 9) (z := 8) (a := 4 * pw) (b := vLn pw ps)
      (by decide) (by decide) (by decide) rfl rfl rfl b4 bLn) <|
    HT.seq (sDrN (W := W) hI (x := 7) (a := 4 * pw) rfl b4) <|
    HT.seq (sDrN (W := W) hI (x := 9) (a := vLn pw ps) rfl bLn) <|
    HT.seq (sIsq (W := W) hI (x := 8) (z := 0) (a := 4 * pw * vLn pw ps) (by decide) rfl rfl
      bAL) <|
    HT.seq (sDrN (W := W) hI (x := 8) (a := 4 * pw * vLn pw ps) rfl bAL) <|
    sToInt (W := W) hI (j := 0) (a := vA pw ps) rfl).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s3 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) (bPi : bitLen (vPi pw ps) ≤ W) :
    HT [] (St S (ph1_Vb pw ps) dv) (ph1_p3 I) (St S (ph1_Vc pw ps) dv) (30 * U C W) := by
  have hB : vBint pw ps ≤ W := by unfold vBint; omega
  have bP : bitLen (vP pw ps) ≤ W := le_trans (bitLen_mono (Nat.sqrt_le_self (vPi pw ps))) bPi
  have hW1 : 1 ≤ W := by omega
  unfold ph1_p3
  refine (HT.seq (sAff' (W := W) (V := ph1_Vb pw ps) hI h0 hr0 h1 hr1 352 3 40 7 (by decide)
      rfl rfl rfl rfl rfl (ph1_lt (by omega)) (vBint pw ps) rfl) <|
    HT.seq (sPow2 (W := W) hI (j := 1) (c := 7) (k := vBint pw ps) (by decide) rfl rfl hB hW1) <|
    HT.seq (sToInt (W := W) hI (j := 1) (a := 2 ^ vBint pw ps) rfl) <|
    HT.seq (ph1_sCpS (W := W) hI (x := 10) (j := 2) (a := vP pw ps) (by decide) rfl rfl bP) <|
    HT.seq (sShl (W := W) hI (x := 2) (c := 7) (a := vP pw ps) (k := vBint pw ps) (by decide)
      rfl rfl hB) <|
    HT.seq (sDrN (W := W) hI (x := 7) (a := vBint pw ps) rfl (ph1_bl hB)) <|
    sDrN (W := W) hI (x := 10) (a := vP pw ps) rfl bP).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s4 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) :
    HT [] (St S (ph1_Vc pw ps) dv) (ph1_p4 I) (St S (ph1_Vd pw ps) dv) (27 * U C W) := by
  have hK : vS pw ps + vBe ps ≤ W := by unfold vS vBe; omega
  have hW1 : 1 ≤ W := by omega
  unfold ph1_p4
  refine (HT.seq (sAff' (W := W) (V := ph1_Vc pw ps) hI h0 hr0 h1 hr1 16 2 16 7 (by decide)
      rfl rfl rfl rfl rfl (ph1_lt (by omega)) (vS pw ps + vBe ps) (by unfold vS vBe; omega)) <|
    HT.seq (sPow2 (W := W) hI (j := 3) (c := 7) (k := vS pw ps + vBe ps) (by decide) rfl rfl hK
      hW1) <|
    HT.seq (sToInt (W := W) hI (j := 3) (a := 2 ^ (vS pw ps + vBe ps)) rfl) <|
    sDrN (W := W) hI (x := 7) (a := vS pw ps + vBe ps) rfl (ph1_bl hK)).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s5 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1) {r2 : List Sym}
    (h2 : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) :
    HT [] (St S (ph1_Vd pw ps) dv) (ph1_p5 I) (St S (ph1_Ve pw ps r) dv) (29 * U C W) := by
  have hS : vS pw ps ≤ W := by unfold vS; omega
  have hW1 : 1 ≤ W := by omega
  have br : bitLen r ≤ W := by omega
  unfold ph1_p5
  refine (HT.seq (sAff' (W := W) (V := ph1_Vd pw ps) hI h0 hr0 h1 hr1 16 1 12 7 (by decide)
      rfl rfl rfl rfl rfl (ph1_lt (by omega)) (vS pw ps) (by unfold vS; omega)) <|
    HT.seq (ph1_sCp2 (W := W) hI (j := 4) h2 hr2 rfl br) <|
    HT.seq (sDbl (W := W) hI (x := 4) (t := 8) (a := r) (by decide) rfl rfl hW1) <|
    HT.seq (sShl (W := W) hI (x := 4) (c := 7) (a := 2 * r) (k := vS pw ps) (by decide) rfl rfl
      hS) <|
    sDrN (W := W) hI (x := 7) (a := vS pw ps) rfl (ph1_bl hS)).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s6 (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) (hr : 0 < r) :
    HT [] (St S (ph1_Ve pw ps r) dv) (ph1_p6 I) (St S (ph1_Vf pw ps r) dv) (8 * U C W) := by
  have bD : bitLen (vDZ pw ps r) ≤ W := by
    have e1 : bitLen (vDZ pw ps r) ≤ bitLen (2 * r) + vS pw ps :=
      bitLen_mul_two_pow_le (2 * r) (vS pw ps)
    have e2 := bitLen_double r hr
    have e3 : vS pw ps = 16 * pw + ps + 12 := rfl
    omega
  unfold ph1_p6
  refine (HT.seq (ph1_sCpS (W := W) (V := ph1_Ve pw ps r) hI (x := 4) (j := 7) (a := vDZ pw ps r)
      (by decide) rfl rfl bD) <|
    HT.seq (sMulN (W := W) hI (x := 4) (y := 7) (z := 5) (a := vDZ pw ps r) (b := vDZ pw ps r)
      (by decide) (by decide) (by decide) rfl rfl rfl bD bD) <|
    sDrN (W := W) hI (x := 7) (a := vDZ pw ps r) rfl bD).of_eq ?_ (by omega)
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ph1_s7 (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W) :
    HT [] (St S (ph1_Vf pw ps r) dv) (ph1_p7 I) (St S (V1 pw ps r) dv) (23 * U C W) := by
  rw [← ph1_V1]
  exact sAff' (W := W) (V := ph1_Vf pw ps r) hI h0 hr0 h1 hr1 136 1 13 6 (by decide) rfl rfl rfl
    rfl rfl (ph1_lt (by omega)) (vN pw ps) (by unfold vN; omega)

end Stages

/-! ## Phase 1 -/

/-- **Phase 1**: from `p_work`, `pSub`, `r` on the named stacks, the shared half-erf arguments `V1`
on scratch `0 … 6`, all other scratch stacks empty, in `181·U C W` steps. -/
theorem sPh1 {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
    {S : HL → List Sym} {dv : List Sym} {pw ps r : ℕ} {r0 r1 r2 : List Sym}
    (h0 : S (.inl 0) = natSyms pw ++ r0) (hr0 : TermOK r0)
    (h1 : S (.inl 1) = natSyms ps ++ r1) (hr1 : TermOK r1)
    (h2 : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2)
    (hp : 0 < pw) (hr : 0 < r)
    (lin : 2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W)
    (bPi : bitLen (vPi pw ps) ≤ W) (bLn : bitLen (vLn pw ps) ≤ W)
    (bAL : bitLen (4 * pw * vLn pw ps) ≤ W) :
    HT [] (St S (fun _ => none) dv) (pPh1 I) (St S (V1 pw ps r) dv) (181 * U C W) := by
  have _ := hp
  unfold pPh1
  exact (HT.seq (ph1_s1 hI h0 hr0 h1 hr1 lin bPi) <|
    HT.seq (ph1_s2 hI h0 hr0 h1 hr1 lin bLn bAL) <| HT.seq (ph1_s3 hI h0 hr0 h1 hr1 lin bPi) <|
    HT.seq (ph1_s4 hI h0 hr0 h1 hr1 lin) <| HT.seq (ph1_s5 hI h0 hr0 h1 hr1 h2 hr2 lin) <|
    HT.seq (ph1_s6 hI lin hr) <| ph1_s7 hI h0 hr0 h1 hr1 lin).mono (by omega)

#assert_std_axioms ph1_s1 ph1_s2 ph1_s3 ph1_s4 ph1_s5 ph1_s6 ph1_s7 pPh1_closed sPh1

end WP.W7k3c
