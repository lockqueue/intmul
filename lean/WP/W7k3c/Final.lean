import WP.W7k3c.Main2
import WP.W7k3c.Ph1
import WP.W7k3c.Out
import WP.W7k3c.HeVal
import WP.W7k3c.Asm

/-!
# WP.W7k3c.Final — the `W7_c0c1` kernel on the machine

`pMain I` (host `Loc 5 16`, registers `I.R`) over the instance bundle `I : CI` of the contracts it
calls: phase 1 (`Ph1`: π, ln 2, √, the shared half-erf arguments), phase 2 (`Ph2`: `u2'` and the
three numerators), phase 3 (`Ph3`: three half-erf evaluations through `W7S_series`), output (`Out`:
the combine `Comb` pushes `c0`, `c1`), between pushed/popped scratch floors (`Main`, `Main2`).
Values: `c0c1_val` (`HeVal`); widths: `c0c1_wid` (`Wid*`); contract assembly: `Asm`.

* `W7_c0c1_holds`: `W7_c0c1` from the contracts called (and the series sub-kernel).
* `W7_c0c1_bind`: the binding shape `∀ Mul, W5_mulAt Mul → growth → W7.Hyps → W7_c0c1`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- **The `W7_c0c1` program** over an instance bundle `I`. -/
def pMain (I : CI) : CP I := pMainOf pPh1 pOutPh I

theorem pMain_closed (I : CI) : (pMain I).Closed := pMainOf_closed pPh1_closed pOutPh_closed I

theorem ph1OK : Ph1OK pPh1 181 := by
  intro I Mul C W hI S dv pw ps r r0 r1 r2 h0 hr0 h1 hr1 h2 hr2 hp hr lin bPi bLn bAL
  exact sPh1 hI h0 hr0 h1 hr1 h2 hr2 hp hr lin bPi bLn bAL

theorem outOK : OutOK pOutPh 120 := by
  intro I Mul C W hI S dv pw ps r u2 hP hM h3 r0 r1 r2 r3 h0 hr0 h1 hr1 h2 hr2 h3' hr3 lin bA bPd
    bDZ bDS hw
  exact sOutPh hI h0 hr0 h1 hr1 h2 hr2 h3' hr3 lin bA bPd bDZ bDS hw

/-- **The main triple**: `pMain I` pushes the snapshot's `(c0.re, c1.re)` within
`410 · U C (c0c1W p_work pSub r)` steps. -/
theorem sMain : MainOK pMain (181 + 120 + 109) := sMain_of ph1OK outOK c0c1_val

/-- **`W7_c0c1`** from the contracts the kernel calls. -/
theorem W7_c0c1_holds (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul)
    (hMul : ∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2)
    (hcopy : W3_copyNat) (hdrop : W3_dropNat) (hadd : W3_addNat) (hsub : W3_subNat)
    (hshlV : W3_shlVar) (hcmp : W3_cmpNat) (haddI : W3_addInt) (hsubI : W3_subInt)
    (hneg : W3_negInt) (hcmpI : W3_cmpInt) (h6 : W6a_divRound)
    (hpi : W7_piScaled) (hln : W7_log2Scaled) (hsq : W7_isqrt)
    (hser : WP.W7k3.W7S_series Mul) : W7_c0c1 :=
  W7_c0c1_of_main pMain pMain_closed _ sMain Mul h5 hMul hcopy hdrop hadd hsub hshlV hcmp haddI
    hsubI hneg hcmpI h6 hpi hln hsq hser

/-- **`W7_c0c1` in its binding shape.** -/
theorem W7_c0c1_bind : ∀ Mul : ℕ → ℕ, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) →
    W7.Hyps → W7_c0c1 :=
  W7_c0c1_bind_of_main pMain pMain_closed _ sMain

/-- The kernel as a W7k2 instance over a bundle `I` (for concrete table builders). -/
def c0c1InstOf (I : CI) : Inst 5 16 Unit :=
  ⟨16, I.R, fun _ => (), pMain I, le_rfl, I.R_finite, I.R_nonempty, pMain_closed I⟩

#assert_std_axioms pMain_closed ph1OK outOK sMain W7_c0c1_holds W7_c0c1_bind

end WP.W7k3c
