import WP.W7k3c.Ph2
import WP.W7k3c.Ph3
import WP.W7k3c.Wid

/-!
# WP.W7k3c.Main — the `W7_c0c1` program, composed from its phases

`pMainOf p1 po`: push the floors, phase 1 (`p1`: shared values), phase 2 (numerators), phase 3
(three half-erfs), output (`po`: combine, push `c0`, `c1`, clean up), pop the floors.
`sMain_of` composes the phase rules (phase 1 and output as hypotheses `Ph1OK`, `OutOK` in the exact
shapes of `sPh1`, `sOutPh`; the value lemma as `hval`) into the main contract shape `MainSpec`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- Shape of the phase-1 rule. -/
def Ph1OK (p : (I : CI) → CP I) (K : ℕ) : Prop :=
  ∀ {I : CI} {Mul : ℕ → ℕ} {C W : ℕ}, I.Spec Mul C →
    ∀ {S : HL → List Sym} {dv : List Sym} {pw ps r : ℕ} {r0 r1 r2 : List Sym},
      S (.inl 0) = natSyms pw ++ r0 → TermOK r0 → S (.inl 1) = natSyms ps ++ r1 → TermOK r1 →
      S (.inl 2) = natSyms r ++ r2 → TermOK r2 → 0 < pw → 0 < r →
      2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W → bitLen (vPi pw ps) ≤ W →
      bitLen (vLn pw ps) ≤ W → bitLen (4 * pw * vLn pw ps) ≤ W →
      HT [] (St S (fun _ => none) dv) (p I) (St S (V1 pw ps r) dv) (K * U C W)

/-- Shape of the output rule. -/
def OutOK (p : (I : CI) → CP I) (K : ℕ) : Prop :=
  ∀ {I : CI} {Mul : ℕ → ℕ} {C W : ℕ}, I.Spec Mul C →
    ∀ {S : HL → List Sym} {dv : List Sym} {pw ps r u2 : ℕ} {hP hM h3 : ℤ} {r0 r1 r2 r3 : List Sym},
      S (.inl 0) = natSyms pw ++ r0 → TermOK r0 → S (.inl 1) = natSyms ps ++ r1 → TermOK r1 →
      S (.inl 2) = natSyms r ++ r2 → TermOK r2 → S (.inl 3) = natSyms u2 ++ r3 → TermOK r3 →
      2 * bitLen r + 400 * pw + 4 * ps + 500 ≤ W →
      bitLen (vA pw ps) ≤ W → bitLen (vP pw ps * 2 ^ vBint pw ps) ≤ W →
      bitLen (vDZ pw ps r) ≤ W → bitLen (vDS pw ps r) ≤ W →
      CombW W (vB ps) (vBe ps) r u2 hP hM h3 →
      HT [] (St S (V3 pw ps r hP hM h3) dv) (p I)
        (St S (fun _ => none) (intSyms (c0c1Comb (vB ps) (vBe ps) r u2 hP hM h3).1 ++
          intSyms (c0c1Comb (vB ps) (vBe ps) r u2 hP hM h3).2 ++ dv)) (K * U C W)

/-- The main contract shape (as `MainOK` of the assembly). -/
def MainSpec (P : (I : CI) → CP I) (K : ℕ) : Prop :=
  ∀ {I : CI} {Mul : ℕ → ℕ} {C : ℕ}, I.Spec Mul C →
    ∀ (S : HL → List Sym) (pw ps r u2 : ℕ) (r0 r1 r2 r3 : List Sym),
      0 < pw → 0 < r → u2 < r → TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = natSyms pw ++ r0 → S (.inl 1) = natSyms ps ++ r1 →
      S (.inl 2) = natSyms r ++ r2 → S (.inl 3) = natSyms u2 ++ r3 →
      HT [] S (P I) (Function.update S (.inl 4)
          (intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.1.1 ++
            intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.2.1 ++ S (.inl 4)))
        (K * U C (c0c1W pw ps r))

/-- Phases 2 and 3. -/
def pMid (I : CI) : CP I := (pPh2 I).seq (pPh3 I)

/-- The program from its phase-1 and output parts. -/
def pMainOf (p1 po : (I : CI) → CP I) (I : CI) : CP I :=
  (pushMarks (List.finRange 16)).seq <| (p1 I).seq <| (pMid I).seq <|
    (po I).seq (popMarks (List.finRange 16))

theorem pMainOf_closed {p1 po : (I : CI) → CP I} (h1 : ∀ I, (p1 I).Closed)
    (ho : ∀ I, (po I).Closed) (I : CI) : (pMainOf p1 po I).Closed :=
  ⟨pushMarks_closed _, h1 I, ⟨pPh2_closed I, pPh3_closed I⟩, ho I, popMarks_closed _⟩

theorem bitLen_vDS_le (pw ps r : ℕ) (hr : 0 < r) :
    bitLen (vDS pw ps r) ≤ 2 * bitLen r + 32 * pw + 2 * ps + 26 := by
  have h1 : bitLen (vDZ pw ps r) ≤ bitLen r + 1 + vS pw ps := by
    unfold vDZ
    have := bitLen_mul_two_pow_le (2 * r) (vS pw ps)
    rw [bitLen_double r hr] at this
    exact this
  have h2 := bitLen_mul_le (vDZ pw ps r) (vDZ pw ps r)
  unfold vDS
  unfold vS at h1
  omega

theorem combW_of {W pw ps r u2 : ℕ} (hr : 0 < r) (hu : u2 < r) (hw : Wid W pw ps r u2) :
    CombW W (vB ps) (vBe ps) r u2 (vH pw ps r (vXp r u2)) (vH pw ps r (vXm r u2))
      (vH pw ps r (vX3 r u2)) where
  bP := hw.bHp
  bM := hw.bHm
  b3 := hw.bH3
  bS := le_trans (bitLen_mono (natAbs_le_mul_natCast _ (Nat.two_pow_pos _))) hw.bHi
  bD := le_trans (bitLen_mono (natAbs_le_mul_natCast _ (Nat.two_pow_pos _))) hw.bLo
  bXS := hw.bHi
  bXD := hw.bLo
  bHi := hw.bRawHi
  bLo := hw.bRawLo
  bB := by rw [bitLen_two_pow]; unfold vB; have := hw.lin; omega
  bBe := by rw [bitLen_two_pow]; unfold vBe; have := hw.lin; omega
  br := by have := hw.lin; omega
  bu := by
    have h1 := bitLen_mono (show 2 * u2 ≤ 2 * r by omega)
    rw [bitLen_double r hr] at h1
    have := hw.lin
    omega

theorem bA_of {W pw ps r u2 : ℕ} (hw : Wid W pw ps r u2) : bitLen (vA pw ps) ≤ W := by
  have h := HeW.bA hw.heP
  rw [Int.natAbs_natCast] at h
  exact h

theorem bPd_of {W pw ps r u2 : ℕ} (hw : Wid W pw ps r u2) :
    bitLen (vP pw ps * 2 ^ vBint pw ps) ≤ W := HeW.bP hw.heP

theorem bDZ_of {W pw ps r u2 : ℕ} (hw : Wid W pw ps r u2) : bitLen (vDZ pw ps r) ≤ W :=
  HeW.bD hw.heP

theorem bDS_of {W pw ps r u2 : ℕ} (hr : 0 < r) (hw : Wid W pw ps r u2) :
    bitLen (vDS pw ps r) ≤ W := by
  have h1 := bitLen_vDS_le pw ps r hr
  have h2 := hw.lin
  omega

section

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C) {S : HL → List Sym} {dv : List Sym}

include hI

theorem sMid {pw ps r u2 : ℕ} {r2 r3 : List Sym} (hu : u2 < r)
    (h2 : S (.inl 2) = natSyms r ++ r2) (hr2 : TermOK r2) (h3 : S (.inl 3) = natSyms u2 ++ r3)
    (hr3 : TermOK r3) (hw : Wid W pw ps r u2) :
    HT [] (St S (V1 pw ps r) dv) (pMid I)
      (St S (V3 pw ps r (vH pw ps r (vXp r u2)) (vH pw ps r (vXm r u2)) (vH pw ps r (vX3 r u2))) dv)
      (75 * U C W) := by
  have lin := hw.lin
  exact (HT.seq (sPh2 (W := W) hI (S := S) (V := V1 pw ps r) (dv := dv) h2 hr2 h3 hr3 hu
    (by omega) rfl rfl rfl rfl rfl rfl) (sPh3 (W := W) hI (S := S) (dv := dv) hw)).mono
    (by omega)

end

#assert_std_axioms pMainOf_closed bitLen_vDS_le combW_of bA_of bPd_of bDZ_of bDS_of sMid

end WP.W7k3c
