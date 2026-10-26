import WP.W7k2.B.Base
import Contracts.W7.Tables

/-!
# WP.W7k2.B.Inst — the builder's contract instances (Top plumbing)

`exists_BI`: from the frozen contracts (`W7.Hyps`, `W5_mulAt Mul`) and the kernels (`W7_kernels`),
an instance bundle `I : BI` with all twenty contract bodies at one shared constant `C ≥ 1`.
Pattern of `W7_colRecip_holds` (ColRecip.lean:404-438): `exists_inst` per contract, the bodies are
the `SpecX` definitions by `rfl` (Ops/Ops2/Loops), then `SpecX.mono` to `C = ΣCᵢ + 1`.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- **The builder's instance bundle exists.** -/
theorem exists_BI (Mul : ℕ → ℕ) (hmul : W5_mulAt Mul) (hyps : W7.Hyps) (hk : W7_kernels) :
    ∃ I : BI, ∃ C : ℕ, 1 ≤ C ∧ I.Spec Mul C := by
  obtain ⟨⟨hcopy, hdrop, _, hiz, hcmp, hadd, _, hshl, hshr, hshlV, _, _, _, hinc, hdec, _, _, _,
    _, _, haddI, _, _, _⟩, _, _, hdiv, _⟩ := hyps
  obtain ⟨_, hpi, hln, hsc, htap, hc01, hcr⟩ := hk
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hiz
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hdec
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst hinc
  obtain ⟨Iic, hIic⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst hadd
  obtain ⟨Iad, hIad⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst hshl
  obtain ⟨Is1, hIs1⟩ := h7 1
  obtain ⟨C8, h8⟩ := exists_inst hshr
  obtain ⟨Ir1, hIr1⟩ := h8 1
  obtain ⟨C9, h9⟩ := exists_inst hshlV
  obtain ⟨Isv, hIsv⟩ := h9 ()
  obtain ⟨C10, h10⟩ := exists_inst hcmp
  obtain ⟨Icm, hIcm⟩ := h10 ()
  obtain ⟨C11, h11⟩ := exists_inst haddI
  obtain ⟨Iai, hIai⟩ := h11 ()
  obtain ⟨C12, h12⟩ := exists_inst hmul
  obtain ⟨Imu, hImu⟩ := h12 ()
  obtain ⟨C13, h13⟩ := exists_inst hdiv
  obtain ⟨Idm, hIdm⟩ := h13 ()
  obtain ⟨C14, h14⟩ := exists_inst hsc
  obtain ⟨Isf, hIsf⟩ := h14 false
  obtain ⟨Ist, hIst⟩ := h14 true
  obtain ⟨C15, h15⟩ := exists_inst htap
  obtain ⟨Itp, hItp⟩ := h15 ()
  obtain ⟨C16, h16⟩ := exists_inst hc01
  obtain ⟨Icc, hIcc⟩ := h16 ()
  obtain ⟨C17, h17⟩ := exists_inst hcr
  obtain ⟨Icr, hIcr⟩ := h17 ()
  obtain ⟨C18, h18⟩ := exists_inst hpi
  obtain ⟨Ipi, hIpi⟩ := h18 ()
  obtain ⟨C19, h19⟩ := exists_inst hln
  obtain ⟨Iln, hIln⟩ := h19 ()
  -- the contract bodies are the `SpecX` definitions
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecInc Iic C5 := hIic
  have s6 : SpecAddNat Iad C6 := hIad
  have s7 : SpecShlConst 1 Is1 C7 := hIs1
  have s8 : SpecShrConst 1 Ir1 C8 := hIr1
  have s9 : SpecShlVar Isv C9 := hIsv
  have s10 : SpecCmpNat Icm C10 := hIcm
  have s11 : SpecAddInt Iai C11 := hIai
  have s12 : SpecMul Mul Imu C12 := hImu
  have s13 : SpecDivMod Idm C13 := hIdm
  have s14 : SpecStdChar false Isf C14 := hIsf
  have s15 : SpecStdChar true Ist C14 := hIst
  have s16 : SpecTap Itp C15 := hItp
  have s17 : SpecC0C1 Icc C16 := hIcc
  have s18 : SpecColRecip Icr C17 := hIcr
  have s19 : SpecPi Ipi C18 := hIpi
  have s20 : SpecLn2 Iln C19 := hIln
  refine ⟨⟨Icp, Idr, Iiz, Idc, Iic, Iad, Is1, Ir1, Isv, Icm, Iai, Imu, Idm, Isf, Ist, Itp, Icc, Icr,
      Ipi, Iln⟩,
    C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14 + C15 + C16 + C17 +
      C18 + C19 + 1, by omega, ?_⟩
  exact ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
    s5.mono (by omega), s6.mono (by omega), s7.mono (by omega), s8.mono (by omega),
    s9.mono (by omega), s10.mono (by omega), s11.mono (by omega), s12.mono (by omega),
    s13.mono (by omega), s14.mono (by omega), s15.mono (by omega), s16.mono (by omega),
    s17.mono (by omega), s18.mono (by omega), s19.mono (by omega), s20.mono (by omega)⟩

#assert_std_axioms exists_BI

end WP.W7k2
