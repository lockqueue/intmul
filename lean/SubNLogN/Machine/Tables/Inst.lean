/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Host
import SubNLogN.Machine.MulBig.Instances

/-!
# K6 (`Machine/Tables/Inst.lean`): the table machine's instance bundle, unconditionally

**Scope (honest summary).** `exists_TB`: a multiplication cost function `Mul` with
`Mul w ≤ K·(w+1)²` and an instance bundle `I : TB` whose twenty contract bodies hold with one
shared constant `C ≥ 1`. Everything is assembled from proved results, as in
`SubNLogN/Machine/MulBig/Instances.lean`: W3 (`WP.Top.W3_all_holds`), W5 Toom-3
(`SubNLogN.Machine.MulBig.w5_toom3Mul_proved`), W6a (`WP.W6a.W6a_holds`), the W7 evaluator kernels
(`WP.W7k3.W7_stdChar_bind`, `WP.W7k3t.W7_sincGaussianTap_bind`, `WP.W7k3c.W7_c0c1_bind`,
`WP.Top.W7_kernels_of`). No hypothesis.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2

/-- **The table machine's instance bundle exists** (no hypotheses). -/
theorem exists_TB : ∃ Mul : ℕ → ℕ, (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) ∧
    ∃ I : TB, ∃ C : ℕ, 1 ≤ C ∧ I.Spec Mul C := by
  have h5 : W5_toom3Mul := SubNLogN.Machine.MulBig.w5_toom3Mul_proved
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  have hg := WP.W7k2.T3_le_quad c0 c1 w0
  have h3 : W3_all := WP.Top.W3_all_holds
  have h6 : W6a_all := WP.W6a.W6a_holds WP.W3.W3_subNat_holds
  have hH : W7.Hyps := WP.Top.W7_hyps_of h3 h5 h6
  have hk : W7_kernels := WP.Top.W7_kernels_of h3 h6 (WP.W7k3.W7_stdChar_bind _ hM hg hH)
    (WP.W7k3t.W7_sincGaussianTap_bind _ hM hg hH) (WP.W7k3c.W7_c0c1_bind _ hM hg hH)
  refine ⟨T3 c0 c1 w0, hg, ?_⟩
  obtain ⟨⟨hcopy, hdrop, _, hiz, hcmp, hadd, hsub, _, _, hshlV, hshrV, _, _, hinc, hdec, _, _, _,
    _, _, haddI, hsubI, _, _⟩, _, _, hdiv, hdivR⟩ := hH
  obtain ⟨_, hpi, hln, hsc, htap, hc01, _⟩ := hk
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3'⟩ := exists_inst hiz
  obtain ⟨Iiz, hIiz⟩ := h3' ()
  obtain ⟨C4, h4⟩ := exists_inst hdec
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5'⟩ := exists_inst hinc
  obtain ⟨Iic, hIic⟩ := h5' ()
  obtain ⟨C6, h6'⟩ := exists_inst hadd
  obtain ⟨Iad, hIad⟩ := h6' ()
  obtain ⟨C7, h7⟩ := exists_inst hsub
  obtain ⟨Isb, hIsb⟩ := h7 ()
  obtain ⟨C8, h8⟩ := exists_inst hshlV
  obtain ⟨Isv, hIsv⟩ := h8 ()
  obtain ⟨C9, h9⟩ := exists_inst hshrV
  obtain ⟨Isr, hIsr⟩ := h9 ()
  obtain ⟨C10, h10⟩ := exists_inst hcmp
  obtain ⟨Icm, hIcm⟩ := h10 ()
  obtain ⟨C11, h11⟩ := exists_inst haddI
  obtain ⟨Iai, hIai⟩ := h11 ()
  obtain ⟨C12, h12⟩ := exists_inst hsubI
  obtain ⟨Isi, hIsi⟩ := h12 ()
  obtain ⟨C13, h13⟩ := exists_inst hM
  obtain ⟨Imu, hImu⟩ := h13 ()
  obtain ⟨C14, h14⟩ := exists_inst hdiv
  obtain ⟨Idm, hIdm⟩ := h14 ()
  obtain ⟨C15, h15⟩ := exists_inst hdivR
  obtain ⟨Idv, hIdv⟩ := h15 ()
  obtain ⟨C16, h16⟩ := exists_inst hsc
  obtain ⟨Isf, hIsf⟩ := h16 false
  obtain ⟨C17, h17⟩ := exists_inst htap
  obtain ⟨Itp, hItp⟩ := h17 ()
  obtain ⟨C18, h18⟩ := exists_inst hc01
  obtain ⟨Icc, hIcc⟩ := h18 ()
  obtain ⟨C19, h19⟩ := exists_inst hpi
  obtain ⟨Ipi, hIpi⟩ := h19 ()
  obtain ⟨C20, h20⟩ := exists_inst hln
  obtain ⟨Iln, hIln⟩ := h20 ()
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecInc Iic C5 := hIic
  have s6 : SpecAddNat Iad C6 := hIad
  have s7 : SpecSubNat Isb C7 := hIsb
  have s8 : SpecShlVar Isv C8 := hIsv
  have s9 : SpecShrVar Isr C9 := hIsr
  have s10 : SpecCmpNat Icm C10 := hIcm
  have s11 : SpecAddInt Iai C11 := hIai
  have s12 : SpecSubInt Isi C12 := hIsi
  have s13 : SpecMul (T3 c0 c1 w0) Imu C13 := hImu
  have s14 : SpecDivMod Idm C14 := hIdm
  have s15 : SpecDivRound Idv C15 := hIdv
  have s16 : SpecStdChar false Isf C16 := hIsf
  have s17 : SpecTap Itp C17 := hItp
  have s18 : SpecC0C1 Icc C18 := hIcc
  have s19 : SpecPi Ipi C19 := hIpi
  have s20 : SpecLn2 Iln C20 := hIln
  refine ⟨⟨Icp, Idr, Iiz, Idc, Iic, Iad, Isb, Isv, Isr, Icm, Iai, Isi, Imu, Idm, Idv, Isf, Itp,
      Icc, Ipi, Iln⟩,
    C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14 + C15 + C16 + C17 +
      C18 + C19 + C20 + 1, by omega, ?_⟩
  exact ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
    s5.mono (by omega), s6.mono (by omega), s7.mono (by omega), s8.mono (by omega),
    s9.mono (by omega), s10.mono (by omega), s11.mono (by omega), s12.mono (by omega),
    s13.mono (by omega), s14.mono (by omega), s15.mono (by omega), s16.mono (by omega),
    s17.mono (by omega), s18.mono (by omega), s19.mono (by omega), s20.mono (by omega)⟩

end SubNLogN.Machine.Tables
