import WP.W0m.PhasesA

/-!
# WP.W0m.PhasesB — correctness and cost of phases E–H

* Phase E uses the hypothesized W6a divider (`DivSpec`).
* Phase H uses the hypothesized W3 adder (`AddSpec`).
* Phases F and G use library and new macros only.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

variable {Ra Rd : Type}

theorem sq_succ (Λ : ℕ) : (Λ + 1) * (Λ + 1) = Λ * Λ + 2 * Λ + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- **Phase E** (W6a divider): `kk := n / b + 1`. -/
theorem phE_runs {md Cd : ℕ} {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hP : DivSpec Pdiv Cd)
    (hmd : md ≤ 6) (S : Stk → List Sym) (n b : ℕ) (hb : 0 < b) (hnn : S .nn = natSyms n)
    (hbb : S .bb = natSyms b) (hkk : S .kk = []) (hrr : S .rr = []) (Λ : ℕ) (hn : bitLen n ≤ Λ)
    (hbΛ : bitLen b ≤ Λ) :
    Runs (phE Pdiv hmd : WProg Ra Rd) S (Function.update S .kk (natSyms (n / b + 1)))
      (fun _ => True) (Cd * ((Λ + 1) * (Λ + 1)) + 8 * Λ + 14) := by
  have hinj : Function.Injective (embL (nm4 .nn .bb .kk .rr) (scr hmd)) :=
    embL_inj (by decide) (scr_inj hmd)
      (by intro i j h; unfold nm4 scr at h; split_ifs at h)
  have hdv := rs_div hP (lD (Ra := Ra) (Rd := Rd)) hinj n b [] [] S hb TermOK.nil TermOK.nil
    (by show S .nn = _; rw [hnn, List.append_nil]) (by show S .bb = _; rw [hbb, List.append_nil])
  set S1 := Function.update (Function.update S .kk (natSyms (n / b))) .rr (natSyms (n % b))
    with hS1
  have hdv' : Runs (divW Pdiv hmd : WProg Ra Rd) S S1 (fun _ => True)
      (Cd * (bitLen n * bitLen b + bitLen n + bitLen b + 1)) := by
    refine runs_post hdv ?_ le_rfl
    show Function.update (Function.update S .kk (natSyms (n / b) ++ S .kk)) .rr
      (natSyms (n % b) ++ S .rr) = S1
    rw [hkk, hrr, List.append_nil, List.append_nil]
  have hd := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.rr) (n % b) [] S1 TermOK.nil
    (by rw [hS1, Function.update_self, List.append_nil])
  set S2 := Function.update S1 .rr [] with hS2
  have hi := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.kk) (t := .ct) (by decide) (n / b) [] S2
    TermOK.nil (by rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide),
      Function.update_self, List.append_nil])
  have hmod : bitLen (n % b) ≤ Λ := (bitLen_mono (Nat.le_of_lt (Nat.mod_lt n hb))).trans hbΛ
  have hdiv : bitLen (n / b) ≤ Λ := (bitLen_mono (Nat.div_le_self n b)).trans hn
  have hprod : bitLen n * bitLen b ≤ Λ * Λ := Nat.mul_le_mul hn hbΛ
  have hC : Cd * (bitLen n * bitLen b + bitLen n + bitLen b + 1) ≤ Cd * ((Λ + 1) * (Λ + 1)) :=
    Nat.mul_le_mul_left Cd (by rw [sq_succ]; omega)
  refine runs_post (runs_seq hdv' (runs_seq hd hi)) ?_ ?_
  · funext z
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · omega

/-- **Phase F**: `k0 := max 4 (bitLen k + 2)`. -/
theorem phF_runs (S : Stk → List Sym) (k : ℕ) (hkk : S .kk = natSyms k) (hk0 : S .k0 = [])
    (hc4 : S .c4 = []) (Λ : ℕ) (hΛ : bitLen k ≤ Λ) :
    Runs (phF : WProg Ra Rd) S (Function.update S .k0 (natSyms (max 4 (bitLen k + 2))))
      (fun _ => True) (100 * Λ + 150) := by
  have h4 : bitLen 4 = 3 := by rw [← length_natSyms, natSyms_four]; rfl
  have hb1 : bitLen (bitLen k) ≤ Λ := (bitLen_le_self _).trans hΛ
  have hb2 : bitLen (bitLen k + 1) ≤ Λ + 1 := (bitLen_le_self _).trans (by omega)
  have hb3 : bitLen (bitLen k + 1 + 1) ≤ Λ + 2 := (bitLen_le_self _).trans (by omega)
  -- count, inc, inc
  have hc := rs_count0 (lS (Ra := Ra) (Rd := Rd)) (src := Stk.kk) (t := .cs) (tm := .tm) (c := .k0)
    (ct := .ct) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k [] [] S
    TermOK.nil TermOK.nil (by rw [hkk, List.append_nil]) hk0
  set S1 := Function.update S .k0 (natSyms (bitLen k) ++ []) with hS1
  have hi1 := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.k0) (t := .ct) (by decide) (bitLen k) []
    S1 TermOK.nil (by rw [hS1, Function.update_self])
  set S2 := Function.update S1 .k0 (natSyms (bitLen k + 1) ++ []) with hS2
  have hi2 := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.k0) (t := .ct) (by decide)
    (bitLen k + 1) [] S2 TermOK.nil (by rw [hS2, Function.update_self])
  set S3 := Function.update S2 .k0 (natSyms (bitLen k + 1 + 1) ++ []) with hS3
  -- the constant 4 on c4
  have hp1 := rs_push (lS (Ra := Ra) (Rd := Rd)) Stk.c4 (Sym.bit true) S3
  set S4 := Function.update S3 .c4 (Sym.bit true :: S3 .c4) with hS4
  have hp2 := rs_push (lS (Ra := Ra) (Rd := Rd)) Stk.c4 (Sym.bit false) S4
  set S5 := Function.update S4 .c4 (Sym.bit false :: S4 .c4) with hS5
  have hp3 := rs_push (lS (Ra := Ra) (Rd := Rd)) Stk.c4 (Sym.bit false) S5
  set S6 := Function.update S5 .c4 (Sym.bit false :: S5 .c4) with hS6
  have hS6c4 : S6 .c4 = natSyms 4 ++ [] := by
    rw [natSyms_four, hS6, Function.update_self, hS5, Function.update_self, hS4,
      Function.update_self, hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), hc4]
    rfl
  have hS6k0 : S6 .k0 = natSyms (bitLen k + 1 + 1) ++ [] := by
    rw [hS6, Function.update_of_ne (by decide), hS5, Function.update_of_ne (by decide), hS4,
      Function.update_of_ne (by decide), hS3, Function.update_self]
  -- compare with 4, conditional overwrite, drop the constant
  have hcmp := rs_cmp (lC (Ra := Ra) (Rd := Rd)) (k₁ := Stk.k0) (k₂ := .c4) (t₁ := .x0) (t₂ := .x1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (bitLen k + 1 + 1) 4
    [] [] S6 TermOK.nil TermOK.nil hS6k0 hS6c4
  set S8 := Function.update S6 .k0 (natSyms (max 4 (bitLen k + 2)) ++ []) with hS8
  have hstep : Runs (.seq (cmpW .k0 .c4)
      (.ite isLt (.seq (sym (dropNat .k0)) (sym (copyBlock .c4 .k0 .tm))) (sym skip)) : WProg Ra Rd)
      S6 S8 (fun _ => True) (12 * min (bitLen (bitLen k + 1 + 1)) (bitLen 4) + 15 +
        (2 * (Λ + 2) + 4 + (7 * 3 + 7) + 1)) := by
    by_cases hlt : bitLen k + 1 + 1 < 4
    · have hc' := runs_mono hcmp (Q' := fun v => isLt v = true)
        (fun v hv => by simp only [isLt, hv, Lib.ordOf, if_pos hlt]; decide) le_rfl
      have hd := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.k0) (bitLen k + 1 + 1) [] S6
        TermOK.nil hS6k0
      have hcp := rs_copy (lS (Ra := Ra) (Rd := Rd)) (src := Stk.c4) (dst := .k0) (tmp := .tm)
        (by decide) (by decide) (by decide) 4 [] (Function.update S6 .k0 []) TermOK.nil
        (by rw [Function.update_of_ne (by decide), hS6c4])
      refine runs_post (runs_ite_true hc' (runs_seq hd hcp)) ?_ ?_
      · rw [hS8, Function.update_idem, Function.update_self, max_eq_left (by omega)]
      · omega
    · have hc' := runs_mono hcmp (Q' := fun v => isLt v = false)
        (fun v hv => by simp only [isLt, hv, Lib.ordOf, if_neg hlt]; split_ifs <;> decide) le_rfl
      have hs := rs_skip (lS (Ra := Ra) (Rd := Rd)) S6
      refine runs_post (runs_ite_false hc' hs) ?_ ?_
      · rw [hS8, max_eq_right (by omega), show bitLen k + 2 = bitLen k + 1 + 1 by omega, ← hS6k0,
          Function.update_eq_self]
      · omega
  have hdc := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.c4) 4 [] S8 TermOK.nil
    (by rw [hS8, Function.update_of_ne (by decide), hS6c4])
  refine runs_post (runs_seq hc (runs_seq hi1 (runs_seq hi2 (runs_seq hp1 (runs_seq hp2
    (runs_seq hp3 (runs_seq hstep hdc))))))) ?_ ?_
  · funext z
    simp only [hS8, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · rw [h4] at hstep ⊢
    omega

/-- **Phase G**: `lf := bitLen (K0 − 1) − 1`. -/
theorem phG_runs (S : Stk → List Sym) (K0 : ℕ) (hK0 : 4 ≤ K0) (hk0 : S .k0 = natSyms K0)
    (ht1 : S .t1 = []) (hlf : S .lf = []) (Λ : ℕ) (hΛ : bitLen K0 ≤ Λ) :
    Runs (phG : WProg Ra Rd) S (Function.update S .lf (natSyms (bitLen (K0 - 1) - 1)))
      (fun _ => True) (60 * Λ + 50) := by
  have hK1 : bitLen (K0 - 1) ≤ Λ := (bitLen_mono (Nat.sub_le _ _)).trans hΛ
  have hpos : 1 ≤ bitLen (K0 - 1) := bitLen_pos (by omega)
  have hK2 : bitLen (K0 - 1 + 1) ≤ Λ := by rw [Nat.sub_add_cancel (by omega)]; exact hΛ
  have hK3 : bitLen (bitLen (K0 - 1) - 1 + 1) ≤ Λ := by
    rw [Nat.sub_add_cancel hpos]; exact (bitLen_le_self _).trans hK1
  have hcp := rs_copy (lS (Ra := Ra) (Rd := Rd)) (src := Stk.k0) (dst := .t1) (tmp := .tm)
    (by decide) (by decide) (by decide) K0 [] S TermOK.nil (by rw [hk0, List.append_nil])
  set S1 := Function.update S .t1 (natSyms K0 ++ S .t1) with hS1
  have hd1 := rs_dec (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t1) (t := .ct) (by decide) (K0 - 1) [] S1
    TermOK.nil (by rw [hS1, Function.update_self, ht1, Nat.sub_add_cancel (by omega)])
  set S2 := Function.update S1 .t1 (natSyms (K0 - 1) ++ []) with hS2
  have hc := rs_count0 (lS (Ra := Ra) (Rd := Rd)) (src := Stk.t1) (t := .cs) (tm := .tm) (c := .lf)
    (ct := .ct) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (K0 - 1) []
    [] S2 TermOK.nil TermOK.nil (by rw [hS2, Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), hlf])
  set S3 := Function.update S2 .lf (natSyms (bitLen (K0 - 1)) ++ []) with hS3
  have hd2 := rs_dec (lS (Ra := Ra) (Rd := Rd)) (k := Stk.lf) (t := .ct) (by decide)
    (bitLen (K0 - 1) - 1) [] S3 TermOK.nil
    (by rw [hS3, Function.update_self, Nat.sub_add_cancel hpos])
  set S4 := Function.update S3 .lf (natSyms (bitLen (K0 - 1) - 1) ++ []) with hS4
  have hdr := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t1) (K0 - 1) [] S4 TermOK.nil
    (by rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_self])
  refine runs_post (runs_seq hcp (runs_seq hd1 (runs_seq hc (runs_seq hd2 hdr)))) ?_ ?_
  · funext z
    simp only [hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · omega

/-- **Phase H** (W3 adder): `p0 := 2·(b + K0 + 3) = 2b + 2K0 + 6`. -/
theorem phH_runs {ma Ca : ℕ} {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra} (hP : AddSpec Padd Ca)
    (hma : ma ≤ 6) (S : Stk → List Sym) (b K0 : ℕ) (hbb : S .bb = natSyms b)
    (hk0 : S .k0 = natSyms K0) (ht2 : S .t2 = []) (ht3 : S .t3 = []) (hp0 : S .p0 = []) (Λ : ℕ)
    (hΛ : bitLen (b + K0 + 3) ≤ Λ) :
    Runs (phH Padd hma : WProg Ra Rd) S (Function.update S .p0 (natSyms (2 * b + 2 * K0 + 6)))
      (fun _ => True) (Ca * (4 * Λ + 2) + 50 * Λ + 50) := by
  have hm0 : bitLen (b + K0) ≤ Λ := (bitLen_mono (by omega)).trans hΛ
  have hm1 : bitLen (b + K0 + 1) ≤ Λ := (bitLen_mono (by omega)).trans hΛ
  have hm2 : bitLen (b + K0 + 1 + 1) ≤ Λ := (bitLen_mono (by omega)).trans hΛ
  have hm3 : bitLen (b + K0 + 1 + 1 + 1) ≤ Λ := by
    rw [show b + K0 + 1 + 1 + 1 = b + K0 + 3 by omega]; exact hΛ
  have hbΛ : bitLen b ≤ Λ := (bitLen_mono (by omega)).trans hΛ
  have hKΛ : bitLen K0 ≤ Λ := (bitLen_mono (by omega)).trans hΛ
  have hinj1 : Function.Injective (embL (nm3 .bb .k0 .t2) (scr hma)) :=
    embL_inj (by decide) (scr_inj hma)
      (by intro i j h; unfold nm3 scr at h; split_ifs at h)
  have hinj2 : Function.Injective (embL (nm3 .t2 .t3 .p0) (scr hma)) :=
    embL_inj (by decide) (scr_inj hma)
      (by intro i j h; unfold nm3 scr at h; split_ifs at h)
  have ha1 := rs_add hP (lA (Ra := Ra) (Rd := Rd)) hinj1 b K0 [] [] S TermOK.nil TermOK.nil
    (by show S .bb = _; rw [hbb, List.append_nil]) (by show S .k0 = _; rw [hk0, List.append_nil])
  set S1 := Function.update S .t2 (natSyms (b + K0) ++ []) with hS1
  have ha1' : Runs (addW Padd hma .bb .k0 .t2 : WProg Ra Rd) S S1 (fun _ => True)
      (Ca * (bitLen b + bitLen K0 + 1)) := by
    refine runs_post ha1 ?_ le_rfl
    show Function.update S .t2 (natSyms (b + K0) ++ S .t2) = S1
    rw [ht2]
  have hi1 := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t2) (t := .ct) (by decide) (b + K0) []
    S1 TermOK.nil (by rw [hS1, Function.update_self])
  set S2 := Function.update S1 .t2 (natSyms (b + K0 + 1) ++ []) with hS2
  have hi2 := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t2) (t := .ct) (by decide) (b + K0 + 1)
    [] S2 TermOK.nil (by rw [hS2, Function.update_self])
  set S3 := Function.update S2 .t2 (natSyms (b + K0 + 1 + 1) ++ []) with hS3
  have hi3 := rs_inc (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t2) (t := .ct) (by decide)
    (b + K0 + 1 + 1) [] S3 TermOK.nil (by rw [hS3, Function.update_self])
  set S4 := Function.update S3 .t2 (natSyms (b + K0 + 1 + 1 + 1) ++ []) with hS4
  have hcp := rs_copy (lS (Ra := Ra) (Rd := Rd)) (src := Stk.t2) (dst := .t3) (tmp := .tm)
    (by decide) (by decide) (by decide) (b + K0 + 1 + 1 + 1) [] S4 TermOK.nil
    (by rw [hS4, Function.update_self])
  set S5 := Function.update S4 .t3 (natSyms (b + K0 + 1 + 1 + 1) ++ S4 .t3) with hS5
  have hS5t3 : S5 .t3 = natSyms (b + K0 + 1 + 1 + 1) ++ [] := by
    rw [hS5, Function.update_self, hS4, Function.update_of_ne (by decide), hS3,
      Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide), ht3]
  have ha2 := rs_add hP (lA (Ra := Ra) (Rd := Rd)) hinj2 (b + K0 + 1 + 1 + 1) (b + K0 + 1 + 1 + 1)
    [] [] S5 TermOK.nil TermOK.nil
    (by show S5 .t2 = _; rw [hS5, Function.update_of_ne (by decide), hS4, Function.update_self])
    (by show S5 .t3 = _; exact hS5t3)
  set S6 := Function.update S5 .p0 (natSyms (2 * b + 2 * K0 + 6) ++ []) with hS6
  have ha2' : Runs (addW Padd hma .t2 .t3 .p0 : WProg Ra Rd) S5 S6 (fun _ => True)
      (Ca * (bitLen (b + K0 + 1 + 1 + 1) + bitLen (b + K0 + 1 + 1 + 1) + 1)) := by
    have hp0' : S5 .p0 = [] := by
      rw [hS5, Function.update_of_ne (by decide), hS4, Function.update_of_ne (by decide), hS3,
        Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
        Function.update_of_ne (by decide), hp0]
    refine runs_post ha2 ?_ le_rfl
    show Function.update S5 .p0
      (natSyms (b + K0 + 1 + 1 + 1 + (b + K0 + 1 + 1 + 1)) ++ S5 .p0) = S6
    rw [hS6, hp0', show b + K0 + 1 + 1 + 1 + (b + K0 + 1 + 1 + 1) = 2 * b + 2 * K0 + 6 by omega]
  have hd2 := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t2) (b + K0 + 1 + 1 + 1) [] S6
    TermOK.nil (by rw [hS6, Function.update_of_ne (by decide), hS5, Function.update_of_ne (by decide),
      hS4, Function.update_self])
  have hd3 := rs_drop (lS (Ra := Ra) (Rd := Rd)) (k := Stk.t3) (b + K0 + 1 + 1 + 1) []
    (Function.update S6 .t2 []) TermOK.nil
    (by rw [Function.update_of_ne (by decide), hS6, Function.update_of_ne (by decide), hS5t3])
  have hA1 : Ca * (bitLen b + bitLen K0 + 1) ≤ Ca * (2 * Λ + 1) :=
    Nat.mul_le_mul_left Ca (by omega)
  have hA2 : Ca * (bitLen (b + K0 + 1 + 1 + 1) + bitLen (b + K0 + 1 + 1 + 1) + 1) ≤
      Ca * (2 * Λ + 1) := Nat.mul_le_mul_left Ca (by omega)
  have hA : Ca * (4 * Λ + 2) = Ca * (2 * Λ + 1) + Ca * (2 * Λ + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  refine runs_post (runs_seq ha1' (runs_seq hi1 (runs_seq hi2 (runs_seq hi3 (runs_seq hcp
    (runs_seq ha2' (runs_seq hd2 hd3))))))) ?_ ?_
  · funext z
    simp only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · omega

#assert_std_axioms sq_succ phE_runs phF_runs phG_runs phH_runs

end WP.W0m
