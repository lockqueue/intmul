import WP.W9d.Twist
import WP.W9dR.Holds
import Contracts.W9.Pipeline

/-!
# WP.W9d.Final — `W9_preTwist` and `W9_postTwist`

* Shift setups: `stpPre` (`shlConst 1`: `s = 2·pSub`) and `stpPost` (two `incNat`: `s = pSub + 2`).
* `twInst_exists`: one instance bundle with one constant `D` from `W5_mulAt Mul`, `W3_addInt`,
  `W3_subInt`, `W3_shlConst`, `W9d_roundShift` (copyNat and incNat: the proved contract instances).
* `W9_preTwist_core`, `W9_postTwist_core`: the contracts from exactly those hypotheses.
* `W9_preTwist_holds`, `W9_postTwist_holds`: the **binding shape**
  `∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_… Mul` (one shared `Mul`), with
  `W9d_roundShift` discharged by WP W9dR (`WP.W9dR.w9d_roundShift`, from W3_all's addNat, subNat,
  shlVar, shrVar, shrConst, dropNat).
-/

namespace WP.W9d

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability TMFw.Lib

/-- Pre-twist shift setup: `K := 2·pSub` (`shlConst 1`). -/
def stpPre (J : TwInst) : Prog TwL (fun _ => Sym) J.Reg := callI J.shl1 [sK] (.inl 0) J.lShl1

/-- Post-twist shift setup: `K := pSub + 2` (two `incNat`). -/
def stpPost (J : TwInst) : Prog TwL (fun _ => Sym) J.Reg :=
  (callI J.inc [sK] (.inl 0) J.lInc).seq (callI J.inc [sK] (.inl 0) J.lInc)

theorem bitLen_succ_le (p : ℕ) : bitLen (p + 1) ≤ bitLen p + 2 := by
  have h := WP.W7k2.bitLen_add_le p 1
  have h1 : bitLen 1 = 1 := by simpa using WP.W7k2.bitLen_two_pow 0
  rw [h1] at h
  omega

theorem preTwist_of_inst {Mul : ℕ → ℕ} (J : TwInst) (D : ℕ) (hJ : J.Spec Mul D) :
    W9_preTwist Mul :=
  twist_holds J D hJ (stpPre J) (callI_closed _ _ _ _) (fun p => 2 * p) (fun _ => D * (1 + 1))
    (fun p => show 2 * p ≤ 2 * p + 2 by omega)
    (fun p => Nat.mul_le_mul_left D (by omega))
    (fun p B rk hrk hB =>
      (HT.shlConst hJ.shl1 (.inl 0) J.lShl1 sK (by decide) B p rk hrk hB []).of_eq
        (by rw [show p * 2 ^ 1 = 2 * p by rw [Nat.pow_one, Nat.mul_comm]]) le_rfl)
    w9P (fun pSub t1 r tw U => w9P_toList pSub t1 r tw U)

theorem postTwist_of_inst {Mul : ℕ → ℕ} (J : TwInst) (D : ℕ) (hJ : J.Spec Mul D) :
    W9_postTwist Mul :=
  twist_holds J D hJ (stpPost J) ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩ (fun p => p + 2)
    (fun p => D * (ones (encodeNat p) + 1) + D * (ones (encodeNat (p + 1)) + 1))
    (fun p => show p + 2 ≤ 2 * p + 2 by omega)
    (fun p => by
      have h1 : ones (encodeNat p) ≤ bitLen p := ones_le_length _
      have h2 : ones (encodeNat (p + 1)) ≤ bitLen (p + 1) := ones_le_length _
      have h3 := bitLen_succ_le p
      show D * (ones (encodeNat p) + 1) + D * (ones (encodeNat (p + 1)) + 1) ≤
        D * (2 * bitLen p + 4)
      calc D * (ones (encodeNat p) + 1) + D * (ones (encodeNat (p + 1)) + 1)
          ≤ D * (bitLen p + 1) + D * (bitLen p + 3) :=
            Nat.add_le_add (Nat.mul_le_mul_left D (by omega)) (Nat.mul_le_mul_left D (by omega))
        _ = D * (2 * bitLen p + 4) := by ring)
    (fun p B rk hrk hB =>
      (HT.seq (HT.incI hJ.inc J.lInc sK B p rk hrk hB)
        (HT.incI hJ.inc J.lInc sK _ (p + 1) rk hrk (by simp))).of_eq
        (by rw [Function.update_idem]) le_rfl)
    w9QPost (fun pSub t1 r tw U => w9QPost_toList pSub t1 r tw U)

/-- One instance bundle, one constant. -/
theorem twInst_exists (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hadd : W3_addInt) (hsub : W3_subInt)
    (hshl : W3_shlConst) (hrnd : WP.W9dR.W9d_roundShift) : ∃ (J : TwInst) (D : ℕ), J.Spec Mul D := by
  obtain ⟨Cm, hm⟩ := exists_inst hM
  obtain ⟨Im, hIm⟩ := hm ()
  obtain ⟨Ca, ha⟩ := exists_inst hadd
  obtain ⟨Ia, hIa⟩ := ha ()
  obtain ⟨Cs, hs⟩ := exists_inst hsub
  obtain ⟨Is, hIs⟩ := hs ()
  obtain ⟨Cr, hr⟩ := exists_inst hrnd
  obtain ⟨Ir, hIr⟩ := hr ()
  obtain ⟨Cc, hc⟩ := exists_inst w3_copyNat
  obtain ⟨Ic, hIc⟩ := hc ()
  obtain ⟨Cl, hl⟩ := exists_inst hshl
  obtain ⟨Il, hIl⟩ := hl 1
  obtain ⟨Ci, hi⟩ := exists_inst w3_incNat
  obtain ⟨Ii, hIi⟩ := hi ()
  refine ⟨⟨Im, Ia, Is, Ir, Ic, Il, Ii⟩, Cm + Ca + Cs + Cr + Cc + Cl + Ci, ?_⟩
  exact ⟨SpecMul.mono hIm (by omega), SpecAddInt.mono hIa (by omega),
    SpecSubInt.mono hIs (by omega), SpecRnd.mono hIr (by omega), SpecCopy.mono hIc (by omega),
    SpecShlConst.mono hIl (by omega), SpecInc.mono hIi (by omega)⟩

/-- **W9.preTwist** from W5 (at the shared `Mul`), W3 add/sub/shlConst and the round shift. -/
theorem W9_preTwist_core (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hadd : W3_addInt)
    (hsub : W3_subInt) (hshl : W3_shlConst) (hrnd : WP.W9dR.W9d_roundShift) :
    W9_preTwist Mul := by
  obtain ⟨J, D, hJ⟩ := twInst_exists Mul hM hadd hsub hshl hrnd
  exact preTwist_of_inst J D hJ

/-- **W9.postTwist** from W5 (at the shared `Mul`), W3 add/sub/shlConst and the round shift. -/
theorem W9_postTwist_core (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hadd : W3_addInt)
    (hsub : W3_subInt) (hshl : W3_shlConst) (hrnd : WP.W9dR.W9d_roundShift) :
    W9_postTwist Mul := by
  obtain ⟨J, D, hJ⟩ := twInst_exists Mul hM hadd hsub hshl hrnd
  exact postTwist_of_inst J D hJ

/-- `W9d_roundShift` from the W3 contracts (WP W9dR). -/
theorem roundShift_of_W3 (h3 : W3_all) : WP.W9dR.W9d_roundShift := by
  obtain ⟨-, hdrop, -, -, -, haddN, hsubN, -, hshr1, hshl, hshr, -⟩ := h3
  exact WP.W9dR.w9d_roundShift haddN hsubN hshl hshr hshr1 hdrop

/-- **`W9_preTwist` in the binding shape** (one shared `Mul`). -/
theorem W9_preTwist_holds :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_preTwist Mul := by
  intro Mul hM h3 _ _
  have hr := roundShift_of_W3 h3
  obtain ⟨-, -, -, -, -, -, -, hshl, -, -, -, -, -, -, -, -, -, -, -, -, -, hadd, hsub, -⟩ := h3
  exact W9_preTwist_core Mul hM hadd hsub hshl hr

/-- **`W9_postTwist` in the binding shape** (one shared `Mul`). -/
theorem W9_postTwist_holds :
    ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_postTwist Mul := by
  intro Mul hM h3 _ _
  have hr := roundShift_of_W3 h3
  obtain ⟨-, -, -, -, -, -, -, hshl, -, -, -, -, -, -, -, -, -, -, -, -, -, hadd, hsub, -⟩ := h3
  exact W9_postTwist_core Mul hM hadd hsub hshl hr

#assert_std_axioms bitLen_succ_le preTwist_of_inst postTwist_of_inst twInst_exists W9_preTwist_core
  W9_postTwist_core roundShift_of_W3 W9_preTwist_holds W9_postTwist_holds

end WP.W9d
