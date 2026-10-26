import WP.W7k3c.Wid
import WP.W7k1.Isqrt
import WP.W7k1.Pi
import WP.W7k1.Ln
import WP.W7k3.Bind

/-!
# WP.W7k3c.Asm — the `W7_c0c1` contract from the main program

Generic in the kernel's main program `P : (I : CI) → CP I`:
* `MainOK P K`: for every instance bundle `I` meeting `I.Spec Mul C`, `P I` pushes the two passband
  coefficients onto stack `4` (exact host triple) within `K · U C (c0c1W pw ps r)` steps.
* `W7_c0c1_of_main`: extract one instance per contract (`exists_inst`; the series at `SK.erf`),
  raise all constants to the shared `Cs = ΣCᵢ + Km + 1` (`*.mono`; `Km` is the growth constant of
  `Mul`, folded into `Spec.mulB`), and bound `K·U Cs W` by `K·4Cs²·K0⁴·(p + pSub + |r| + 1)⁴` with
  `c0c1W_lin`.
* `W7_c0c1_bind_of_main`: the binding shape `∀ Mul, W5_mulAt Mul → growth → W7.Hyps → W7_c0c1`
  (W7k1's `isqrt`, `π`, `ln 2`; W7k3's `W7S_series_bind`).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- The main-program hypothesis (the shape of the owner's `sMain`). -/
def MainOK (P : (I : CI) → CP I) (K : ℕ) : Prop :=
  ∀ {I : CI} {Mul : ℕ → ℕ} {C : ℕ}, I.Spec Mul C →
    ∀ (S : HL → List Sym) (pw ps r u2 : ℕ) (r0 r1 r2 r3 : List Sym),
      0 < pw → 0 < r → u2 < r → TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = natSyms pw ++ r0 → S (.inl 1) = natSyms ps ++ r1 →
      S (.inl 2) = natSyms r ++ r2 → S (.inl 3) = natSyms u2 ++ r3 →
      HT [] S (P I) (Function.update S (.inl 4)
          (intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.1.1 ++
            intSyms (IntMul.computableC0C1WithProgramCost pw ps r u2).1.2.1 ++ S (.inl 4)))
        (K * U C (c0c1W pw ps r))

/-- The cost bound of the contract. -/
theorem asm_cost_le (K Cs K0 pw ps r : ℕ)
    (hK0 : c0c1W pw ps r + 2 ≤ K0 * (pw + ps + bitLen r + 1)) :
    K * U Cs (c0c1W pw ps r) ≤ K * (4 * Cs * Cs) * K0 ^ 4 * (pw + ps + bitLen r + 1) ^ 4 := by
  have h4 : (c0c1W pw ps r + 2) ^ 4 ≤ (K0 * (pw + ps + bitLen r + 1)) ^ 4 :=
    Nat.pow_le_pow_left hK0 4
  calc K * U Cs (c0c1W pw ps r) = K * (4 * Cs * Cs) * (c0c1W pw ps r + 2) ^ 4 := by
        unfold U
        ring
    _ ≤ K * (4 * Cs * Cs) * (K0 * (pw + ps + bitLen r + 1)) ^ 4 := Nat.mul_le_mul_left _ h4
    _ = K * (4 * Cs * Cs) * K0 ^ 4 * (pw + ps + bitLen r + 1) ^ 4 := by ring

/-- **`W7_c0c1` from the main program** and the contracts it calls. -/
theorem W7_c0c1_of_main (P : (I : CI) → CP I) (hcl : ∀ I, (P I).Closed) (K : ℕ)
    (hmain : MainOK P K)
    (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (hcopy : W3_copyNat) (hdrop : W3_dropNat) (hadd : W3_addNat) (hsub : W3_subNat)
    (hshlV : W3_shlVar) (hcmp : W3_cmpNat) (haddI : W3_addInt) (hsubI : W3_subInt)
    (hneg : W3_negInt) (hcmpI : W3_cmpInt) (h6 : W6a_divRound)
    (hpi : W7_piScaled) (hln : W7_log2Scaled) (hsq : W7_isqrt)
    (hser : WP.W7k3.W7S_series Mul) : W7_c0c1 := by
  obtain ⟨Km, hKm⟩ := hMul
  obtain ⟨C1, g1⟩ := exists_inst hcopy
  obtain ⟨I1, s1⟩ := g1 ()
  obtain ⟨C2, g2⟩ := exists_inst hdrop
  obtain ⟨I2, s2⟩ := g2 ()
  obtain ⟨C3, g3⟩ := exists_inst hadd
  obtain ⟨I3, s3⟩ := g3 ()
  obtain ⟨C4, g4⟩ := exists_inst hsub
  obtain ⟨I4, s4⟩ := g4 ()
  obtain ⟨C5, g5⟩ := exists_inst hshlV
  obtain ⟨I5, s5⟩ := g5 ()
  obtain ⟨C6, g6⟩ := exists_inst hcmp
  obtain ⟨I6, s6⟩ := g6 ()
  obtain ⟨C7, g7⟩ := exists_inst haddI
  obtain ⟨I7, s7⟩ := g7 ()
  obtain ⟨C8, g8⟩ := exists_inst hsubI
  obtain ⟨I8, s8⟩ := g8 ()
  obtain ⟨C9, g9⟩ := exists_inst hneg
  obtain ⟨I9, s9⟩ := g9 ()
  obtain ⟨C10, g10⟩ := exists_inst hcmpI
  obtain ⟨I10, s10⟩ := g10 ()
  obtain ⟨C11, g11⟩ := exists_inst h5
  obtain ⟨I11, s11⟩ := g11 ()
  obtain ⟨C12, g12⟩ := exists_inst h6
  obtain ⟨I12, s12⟩ := g12 ()
  obtain ⟨C13, g13⟩ := exists_inst hpi
  obtain ⟨I13, s13⟩ := g13 ()
  obtain ⟨C14, g14⟩ := exists_inst hln
  obtain ⟨I14, s14⟩ := g14 ()
  obtain ⟨C15, g15⟩ := exists_inst hsq
  obtain ⟨I15, s15⟩ := g15 ()
  obtain ⟨C16, g16⟩ := exists_inst hser
  obtain ⟨I16, s16⟩ := g16 WP.W7k3.SK.erf
  have s16' : SpecSer I16 C16 := s16 WP.W7k3.SK.erf_OK
  obtain ⟨K0, hK0⟩ := c0c1W_lin
  let Cs := C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14 + C15 +
    C16 + Km + 1
  let I : CI := ⟨I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16⟩
  have hI : I.Spec Mul Cs :=
    ⟨SpecCopy.mono s1 (by omega), SpecDrop.mono s2 (by omega), SpecAddNat.mono s3 (by omega),
      SpecSubNat.mono s4 (by omega), SpecShlVar.mono s5 (by omega),
      SpecCmpNat.mono s6 (by omega), SpecAddInt.mono s7 (by omega),
      SpecSubInt.mono s8 (by omega), SpecNegInt.mono s9 (by omega),
      SpecCmpInt.mono s10 (by omega), SpecMul.mono s11 (by omega),
      SpecDivRound.mono s12 (by omega), SpecPi.mono s13 (by omega), SpecLn2.mono s14 (by omega),
      SpecIsq.mono s15 (by omega), SpecSer.mono s16' (by omega), by omega,
      fun w => (hKm w).trans (Nat.mul_le_mul_right _ (by omega))⟩
  refine ⟨K * (4 * Cs * Cs) * K0 ^ 4, fun _ => ⟨16, I.R, fun _ => (), P I, le_rfl, I.R_finite,
    I.R_nonempty, hcl I, ?_⟩⟩
  intro pw ps r u2 r0 r1 r2 r3 S hp hr hu t0 t1 t2 t3 e0 e1 e2 e3
  exact HT.runs ((hmain hI S pw ps r u2 r0 r1 r2 r3 hp hr hu t0 t1 t2 t3 e0 e1 e2 e3).mono
    (asm_cost_le K Cs K0 pw ps r (hK0 pw ps r)))

/-- **`W7_c0c1` in the binding shape of the W7 kernels.** -/
theorem W7_c0c1_bind_of_main (P : (I : CI) → CP I) (hcl : ∀ I, (P I).Closed) (K : ℕ)
    (hmain : MainOK P K) :
    ∀ Mul : ℕ → ℕ, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1 := by
  intro Mul h5 hg hH
  have hser := WP.W7k3.W7S_series_bind Mul h5 hg hH
  obtain ⟨⟨hcopy, hdrop, -, hisz, hcmp, hadd, hsub, hshl, hshr, hshlV, hshrV, -, -, hinc, hdec, -,
    -, -, hneg, -, haddI, hsubI, hcmpI, -⟩, -, -, hdm, hdr⟩ := hH
  exact W7_c0c1_of_main P hcl K hmain Mul h5 hg hcopy hdrop hadd hsub hshlV hcmp haddI hsubI hneg
    hcmpI hdr (WP.W7k1.W7_piScaled_holds hcopy hinc hshl hshlV hadd hsub hshrV hshr hdrop hisz hdec)
    (WP.W7k1.W7_log2Scaled_holds hcopy hinc hshl hshlV hadd hsub hshrV hshr hdrop hisz hdec hdm)
    WP.W7k1.W7_isqrt_holds hser

#assert_std_axioms asm_cost_le W7_c0c1_of_main W7_c0c1_bind_of_main

end WP.W7k3c
