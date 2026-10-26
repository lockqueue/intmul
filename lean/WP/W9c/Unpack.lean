import WP.W9c.UnpackLoop

/-!
# WP.W9c.Unpack — `W9c_unpack` holds

`w9c_unpack_holds`: from the frozen W3 contracts `W3_splitAt`, `W3_subNat`, `W3_dropNat`,
`W3_shlVar` and the pure `W3_dec_amortised` (the proved instances `w3_incNat`, `w3_cmpNat`,
`w3_isZeroNat`, `w3_decNat`, `w3_copyNat` are used directly), the program `Unp.unpackP` (host
`Loc 4 8`, 8 scratch stacks) satisfies the frozen `W9c_unpack` with the constant `100·(C+1)`, `C`
the sum of the instance constants.

`unpackP`: if `n = 0` drop the number; otherwise peek the sign, pop it, set up, run the digit loop
(`n` streamed balanced digits, `Unp.udig`, equal to `unpackSignedKronecker` by `unpack_eq_udig`),
tear down.
-/

namespace WP.W9c.Unp

open TMFw TMFw.Contracts WP.W7k2 WP.W9c IntMul Computability

/-- Cost of `mainP` (sign popped, setup, loop, teardown). -/
def mainCost (C k n bM : ℕ) : ℕ :=
  1 + ((C * (n + 5 * k + 5) + 8) + ((C + (C * (2 * n + bitLen n) +
    n * (20 * (C + 1) * (k + 1) + C + 1) + 1)) + (C * (bM + k + 4) + 4 * (n * (k + 2)) + 8)))

theorem mainCost_le (C k n bM : ℕ) (hn : 1 ≤ n) :
    C + (1 + (mainCost C k n bM + 1) + 1) ≤ 100 * (C + 1) * (bM + n * (k + 1) + 1) := by
  unfold mainCost
  obtain ⟨P, hP⟩ : ∃ P, P = n * (k + 1) := ⟨_, rfl⟩
  have hnP : n ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_right n (by omega)
  have hkP : k + 1 ≤ P := by rw [hP]; exact Nat.le_mul_of_pos_left (k + 1) hn
  have hb : bitLen n ≤ n := bitLen_le_self n
  have e1 : C * (n + 5 * k + 5) ≤ 6 * (C * P) := by
    calc C * (n + 5 * k + 5) ≤ C * (6 * P) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (C * P) := by ring
  have e2 : C * (2 * n + bitLen n) ≤ 3 * (C * P) := by
    calc C * (2 * n + bitLen n) ≤ C * (3 * P) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (C * P) := by ring
  have e3 : n * (20 * (C + 1) * (k + 1) + C + 1) = 20 * (C * P) + 20 * P + C * n + n := by
    rw [hP]; ring
  have e4 : C * n ≤ C * P := Nat.mul_le_mul_left _ hnP
  have e5 : C * (bM + k + 4) ≤ C * bM + 4 * (C * P) := by
    calc C * (bM + k + 4) ≤ C * (bM + 4 * P) := Nat.mul_le_mul_left _ (by omega)
      _ = C * bM + 4 * (C * P) := by ring
  have e6 : n * (k + 2) ≤ 2 * P := by
    rw [hP]
    calc n * (k + 2) ≤ n * (2 * (k + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (n * (k + 1)) := by ring
  have e7 : 100 * (C + 1) * (bM + n * (k + 1) + 1) =
      100 * (C * bM) + 100 * (C * P) + 100 * C + 100 * bM + 100 * P + 100 := by
    rw [hP]; ring
  omega

/-- **After the sign**: pop it, set up, `n` digits, tear down. -/
theorem mainP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (hA : W3_dec_amortised) (neg : Bool)
    (k n : ℕ) (hk : 1 ≤ k) (Pz : ℤ) (rx rk rn : List Sym) (S : UL → List Sym) (hrx : TermOK rx)
    (hrk : TermOK rk) (hrn : TermOK rn) (hX : S (.inl 0) = intSyms Pz ++ rx)
    (hK : S (.inl 1) = natSyms k ++ rk) (hN : S (.inl 2) = natSyms n ++ rn) :
    HT [] S (mainP J neg)
      (Function.update (Function.update S (.inl 0) rx) (.inl 3)
        (listSyms (udig neg k n Pz.natAbs 0) ++ S (.inl 3)))
      (mainCost C k n (bitLen Pz.natAbs)) := by
  have hds := bitLen_udig_le neg k hk n Pz.natAbs 0 (Nat.zero_le _)
  have hlen := udig_length neg k n Pz.natAbs 0
  have hMn := bitLen_mono (udSt_fst_le neg k n Pz.natAbs 0)
  apply HT.mono
  · unfold mainP
    exact HT.seq ((HT.popS (.inl 0) S (sgnSym Pz) (natSyms Pz.natAbs ++ rx)
        (by rw [hX, intSyms, List.cons_append]) []).of_eq (ust_init S _) le_rfl) <| HT.seq
      ((setupP_spec J hJ k n hk S rk rn hrk hrn hK hN _).of_eq (lst_n neg k Pz.natAbs n rx S).symm
        le_rfl) <| HT.seq
      ((loopP_spec J hJ hA neg k hk S rk hrk hK rx hrx Pz.natAbs n).of_eq
        (lst_zero neg k Pz.natAbs n rx S) le_rfl)
      (teardownP_spec J hJ k hk S rx hrx _ _ (udSt_carry_le neg k hk n Pz.natAbs 0 (Nat.zero_le _))
        _ hds)
  · unfold mainCost
    rw [hlen]
    have := Nat.mul_le_mul_left C (show bitLen (udSt neg k n Pz.natAbs 0).1 + k + 4 ≤
      bitLen Pz.natAbs + k + 4 by omega)
    omega

theorem optT_sgn (Pz : ℤ) (rx : List Sym) :
    optT (fun s => decide (s = Sym.neg)) (intSyms Pz ++ rx).head? = decide (Pz < 0) := by
  unfold intSyms sgnSym
  by_cases h : Pz < 0 <;> simp [h, optT]

/-- **The `W9c_unpack` program**: correctness and cost. -/
theorem unpackP_spec (J : UInst) {C : ℕ} (hJ : J.Spec C) (hA : W3_dec_amortised) (k n : ℕ)
    (Pz : ℤ) (rx rk rn : List Sym) (S : UL → List Sym) (hk : 1 ≤ k) (hrx : TermOK rx)
    (hrk : TermOK rk) (hrn : TermOK rn) (hX : S (.inl 0) = intSyms Pz ++ rx)
    (hK : S (.inl 1) = natSyms k ++ rk) (hN : S (.inl 2) = natSyms n ++ rn) :
    HT [] S (unpackP J)
      (Function.update (Function.update S (.inl 0) rx) (.inl 3)
        (listSyms (unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n Pz) ++ S (.inl 3)))
      (100 * (C + 1) * (bitLen Pz.natAbs + n * (k + 1) + 1)) := by
  rw [unpack_eq_udig k hk n Pz]
  unfold unpackP
  by_cases hn : n = 0
  · subst hn
    refine (HT.callI_test J.zero [.inl 2] (.inl 0) (List.nodup_singleton _) rfl (by norm_num)
      J.lZero S _ (fun b => b) (decide (0 = 0)) (hJ.zero 0 rn _ hrn hN) _ _ []
      (T₁ := 1 + C * (bitLen Pz.natAbs + 1)) (T₂ := 0) (fun _ => ?_)
      (fun h0 => absurd h0 (by decide))).mono ?_
    · refine HT.seq (HT.popS (.inl 0) S (sgnSym Pz) (natSyms Pz.natAbs ++ rx)
        (by rw [hX, intSyms, List.cons_append]) []) ((HT.dropNat hJ.drop (.inl 0) J.lDrop (.inl 0)
        (by norm_num) _ Pz.natAbs rx hrx (by simp) []).of_eq ?_ le_rfl)
      rw [Function.update_idem]
      symm
      rw [Function.update_eq_self_iff]
      simp [udig, listSyms]
    · have e : C ≤ C * (bitLen Pz.natAbs + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have e2 : 100 * (C + 1) * (bitLen Pz.natAbs + 0 * (k + 1) + 1) =
          100 * (C * (bitLen Pz.natAbs + 1)) + 100 * (bitLen Pz.natAbs + 1) := by ring
      omega
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    refine (HT.callI_test J.zero [.inl 2] (.inl 0) (List.nodup_singleton _) rfl (by norm_num)
      J.lZero S _ (fun b => b) (decide (n = 0)) (hJ.zero n rn _ hrn hN) _ _ []
      (T₁ := 0) (T₂ := 1 + (max (mainCost C k n (bitLen Pz.natAbs))
        (mainCost C k n (bitLen Pz.natAbs)) + 1))
      (fun h0 => absurd (of_decide_eq_true h0) hn) (fun _ => ?_)).mono ?_
    · refine ht_ifTop J.lS (.inl 0) (fun s => decide (s = Sym.neg)) S _ _ _ (fun hs => ?_)
        (fun hs => ?_)
      · rw [hX, optT_sgn] at hs
        rw [hs]
        exact mainP_spec J hJ hA true k n hk Pz rx rk rn S hrx hrk hrn hX hK hN
      · rw [hX, optT_sgn] at hs
        rw [hs]
        exact mainP_spec J hJ hA false k n hk Pz rx rk rn S hrx hrk hrn hX hK hN
    · have := mainCost_le C k n (bitLen Pz.natAbs) hn1
      omega

/-! ## One constant for all instances -/

theorem specSplit_mono {I : Inst 3 4 Unit} {C₁ C₂ : ℕ} (h : SpecSplitU I C₁) (hC : C₁ ≤ C₂) :
    SpecSplitU I C₂ := fun a c rx rc S h1 h2 h3 h4 =>
  Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem specInc_mono {I : Inst 1 4 Unit} {C₁ C₂ : ℕ} (h : SpecIncU I C₁) (hC : C₁ ≤ C₂) :
    SpecIncU I C₂ := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem specCmp_mono {I : Inst 2 4 Ordering} {C₁ C₂ : ℕ} (h : SpecCmpNat I C₁) (hC : C₁ ≤ C₂) :
    SpecCmpNat I C₂ := fun a b rx ry S h1 h2 h3 h4 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem specSub_mono {I : Inst 3 4 Unit} {C₁ C₂ : ℕ} (h : SpecSubU I C₁) (hC : C₁ ≤ C₂) :
    SpecSubU I C₂ := fun a b rx ry S h1 h2 h3 h4 h5 =>
  Triple.cost_mono (h a b rx ry S h1 h2 h3 h4 h5) (Nat.mul_le_mul_right _ hC)

theorem specDrop_mono {I : Inst 1 4 Unit} {C₁ C₂ : ℕ} (h : SpecDrop I C₁) (hC : C₁ ≤ C₂) :
    SpecDrop I C₂ := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem specZero_mono {I : Inst 1 4 Bool} {C₁ C₂ : ℕ} (h : SpecIsZero I C₁) (hC : C₁ ≤ C₂) :
    SpecIsZero I C₂ := fun a rx S h1 h2 => Triple.cost_mono (h a rx S h1 h2) hC

theorem specDec_mono {I : Inst 1 4 Unit} {C₁ C₂ : ℕ} (h : SpecDec I C₁) (hC : C₁ ≤ C₂) :
    SpecDec I C₂ := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem specCopy_mono {I : Inst 2 4 Unit} {C₁ C₂ : ℕ} (h : SpecCopy I C₁) (hC : C₁ ≤ C₂) :
    SpecCopy I C₂ := fun a rx S h1 h2 =>
  Triple.cost_mono (h a rx S h1 h2) (Nat.mul_le_mul_right _ hC)

theorem specShlV_mono {I : Inst 2 4 Unit} {C₁ C₂ : ℕ} (h : SpecShlVar I C₁) (hC : C₁ ≤ C₂) :
    SpecShlVar I C₂ := fun a c rx rc S h1 h2 h3 h4 =>
  Triple.cost_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

#assert_std_axioms mainCost_le mainP_spec optT_sgn unpackP_spec specSplit_mono specInc_mono
  specCmp_mono specSub_mono specDrop_mono specZero_mono specDec_mono specCopy_mono specShlV_mono

end WP.W9c.Unp

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 Unp

/-- **`W9c_unpack` holds**, from the frozen W3 contracts it calls. -/
theorem w9c_unpack_holds (hsplit : W3_splitAt) (hsub : W3_subNat) (hdrop : W3_dropNat)
    (hshl : W3_shlVar) (hA : W3_dec_amortised) : W9c_unpack := by
  obtain ⟨Cs, hs⟩ := exists_inst hsplit
  obtain ⟨Is, hIs⟩ := hs ()
  obtain ⟨Ci, hi⟩ := exists_inst w3_incNat
  obtain ⟨Ii, hIi⟩ := hi ()
  obtain ⟨Cm, hm⟩ := exists_inst w3_cmpNat
  obtain ⟨Im, hIm⟩ := hm ()
  obtain ⟨Cb, hb⟩ := exists_inst hsub
  obtain ⟨Ib, hIb⟩ := hb ()
  obtain ⟨Cd, hd⟩ := exists_inst hdrop
  obtain ⟨Id, hId⟩ := hd ()
  obtain ⟨Cz, hz⟩ := exists_inst w3_isZeroNat
  obtain ⟨Iz, hIz⟩ := hz ()
  obtain ⟨Cc, hc⟩ := exists_inst w3_decNat
  obtain ⟨Ic, hIc⟩ := hc ()
  obtain ⟨Cp, hp⟩ := exists_inst w3_copyNat
  obtain ⟨Ip, hIp⟩ := hp ()
  obtain ⟨Cv, hv⟩ := exists_inst hshl
  obtain ⟨Iv, hIv⟩ := hv ()
  obtain ⟨C, hC⟩ : ∃ C, C = Cs + Ci + Cm + Cb + Cd + Cz + Cc + Cp + Cv := ⟨_, rfl⟩
  have s1 : SpecSplitU Is Cs := hIs
  have s2 : SpecIncU Ii Ci := hIi
  have s3 : SpecCmpNat Im Cm := hIm
  have s4 : SpecSubU Ib Cb := hIb
  have s5 : SpecDrop Id Cd := hId
  have s6 : SpecIsZero Iz Cz := hIz
  have s7 : SpecDec Ic Cc := hIc
  have s8 : SpecCopy Ip Cp := hIp
  have s9 : SpecShlVar Iv Cv := hIv
  have hJ : UInst.Spec ⟨Is, Ii, Im, Ib, Id, Iz, Ic, Ip, Iv⟩ C :=
    ⟨specSplit_mono s1 (by omega), specInc_mono s2 (by omega), specCmp_mono s3 (by omega),
      specSub_mono s4 (by omega), specDrop_mono s5 (by omega), specZero_mono s6 (by omega),
      specDec_mono s7 (by omega), specCopy_mono s8 (by omega), specShlV_mono s9 (by omega)⟩
  haveI := Is.fin
  haveI := Ii.fin
  haveI := Im.fin
  haveI := Ib.fin
  haveI := Id.fin
  haveI := Iz.fin
  haveI := Ic.fin
  haveI := Ip.fin
  haveI := Iv.fin
  haveI := Is.ne
  haveI := Ii.ne
  haveI := Im.ne
  haveI := Ib.ne
  haveI := Id.ne
  haveI := Iz.ne
  haveI := Ic.ne
  haveI := Ip.ne
  haveI := Iv.ne
  refine ⟨100 * (C + 1), fun _ => ⟨8, UInst.Reg ⟨Is, Ii, Im, Ib, Id, Iz, Ic, Ip, Iv⟩, fun _ => (),
    unpackP ⟨Is, Ii, Im, Ib, Id, Iz, Ic, Ip, Iv⟩, by norm_num,
    (inferInstance : Finite (Option Sym × Is.R × Ii.R × Im.R × Ib.R × Id.R × Iz.R × Ic.R × Ip.R ×
      Iv.R)),
    (inferInstance : Nonempty (Option Sym × Is.R × Ii.R × Im.R × Ib.R × Id.R × Iz.R × Ic.R ×
      Ip.R × Iv.R)),
    unpackP_closed _, ?_⟩⟩
  intro k n Pz rx rk rn S hk hrx hrk hrn hX hK hN
  exact HT.runs (unpackP_spec _ hJ hA k n Pz rx rk rn S hk hrx hrk hrn hX hK hN)

#assert_std_axioms w9c_unpack_holds

end WP.W9c
