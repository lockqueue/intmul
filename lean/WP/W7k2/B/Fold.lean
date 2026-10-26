import WP.W7k2.B.Roles

/-!
# WP.W7k2.B.Fold — folded filter taps

`foldBody` (column `u` on `y2`, row `j1` on `y1`) pushes `realRec (foldV pw pSub t1 W j1 u)` onto
`TT`. Here `foldV … u = Σ_{s < 2·pSub+1, s % W = u} tap s` (CTB:35), the sum over the arithmetic
progression `u, u+W, u+2W, … < 2·pSub+1` (`sum_filter_mod_eq`). It is computed by a
`while s < N1` loop (`tapStep`: one `W7_sincGaussianTap` call and one `W3_addInt` per term), with
`n ≤ ⌈N1/W⌉` iterations (`exists_ap_count`).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-! ## Arithmetic progressions and sums -/

theorem exists_ap_count (N W u : ℕ) (hW : 0 < W) :
    ∃ n, (∀ i < n, u + i * W < N) ∧ N ≤ u + n * W ∧ n ≤ (N + W - 1) / W := by
  classical
  have hex : ∃ n, N ≤ u + n * W := ⟨N, by have := Nat.le_mul_of_pos_right N hW; omega⟩
  have hq : N ≤ u + (N + W - 1) / W * W := by
    have h1 := Nat.div_add_mod (N + W - 1) W
    have h2 := Nat.mod_lt (N + W - 1) hW
    have h3 : (N + W - 1) / W * W = W * ((N + W - 1) / W) := Nat.mul_comm _ _
    omega
  refine ⟨Nat.find hex, fun i hi => ?_, Nat.find_spec hex, Nat.find_min' hex hq⟩
  have := Nat.find_min hex hi
  omega

theorem sum_filter_mod_eq (f : ℕ → ℤ) (N W u n : ℕ) (hu : u < W)
    (hlt : ∀ i < n, u + i * W < N) (hge : N ≤ u + n * W) :
    ∑ s ∈ (Finset.range N).filter (fun s => s % W = u), f s =
      ∑ i ∈ Finset.range n, f (u + i * W) := by
  have hW : 0 < W := by omega
  have hinj : Set.InjOn (fun i => u + i * W) (Finset.range n : Set ℕ) := by
    intro i _ j _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hW (by omega)
  rw [← Finset.sum_image hinj]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hs, hsu⟩
    have h1 := Nat.div_add_mod s W
    have h2 : s / W * W = W * (s / W) := Nat.mul_comm _ _
    refine ⟨s / W, ?_, by omega⟩
    by_contra hcon
    push_neg at hcon
    have h3 : n * W ≤ s / W * W := Nat.mul_le_mul_right _ hcon
    omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hlt i hi, by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]⟩

theorem natAbs_sum_range_le (f : ℕ → ℤ) (b : ℕ) :
    ∀ n, (∀ j < n, (f j).natAbs ≤ b) → (∑ j ∈ Finset.range n, f j).natAbs ≤ n * b
  | 0, _ => by simp
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    have h1 := natAbs_sum_range_le f b n (fun j hj => h j (by omega))
    have h2 := Int.natAbs_add_le (∑ j ∈ Finset.range n, f j) (f n)
    have h3 := h n (by omega)
    rw [Nat.succ_mul]
    omega

theorem bitLen_sum_le {z : ℤ} {i N ps : ℕ} (h : z.natAbs ≤ i * (2 ^ ps + 1)) (hi : i ≤ N) :
    bitLen z.natAbs ≤ bitLen N + ps + 1 := by
  apply bitLen_le_of_lt
  have h1 : 2 ^ ps + 1 ≤ 2 ^ (ps + 1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := ps)
    omega
  have h2 : i * (2 ^ ps + 1) ≤ N * 2 ^ (ps + 1) := Nat.mul_le_mul hi h1
  have h3 : N * 2 ^ (ps + 1) < 2 ^ bitLen N * 2 ^ (ps + 1) :=
    Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen N) (by positivity)
  rw [show bitLen N + ps + 1 = bitLen N + (ps + 1) by omega, pow_add]
  omega

theorem tapV_natAbs_le (pw ps t1 j1 s : ℕ) (hpw : 0 < pw) (hps : 0 < ps) (ht1 : 0 < t1)
    (hj1 : j1 < t1) (hs : s < 2 * ps + 1) : (tapV pw ps t1 j1 s).natAbs ≤ 2 ^ ps + 1 :=
  (computableSincGaussianTapWithProgramCost_spec pw ps t1 j1 s hpw hps ht1 hj1 hs).2

theorem cq_le {C x Q : ℕ} (k : ℕ) (h : x ≤ k * Q) : C * x ≤ k * (C * Q) := by
  calc C * x ≤ C * (k * Q) := Nat.mul_le_mul_left _ h
    _ = k * (C * Q) := Nat.mul_left_comm _ _ _

/-! ## The level values read by the fold -/

/-- The level values the fold reads: `pWork`, `pSub`, `t1`, `W`, `N1 = 2·pSub+1`, `π`, `ln 2`. -/
def FoldEnv (B : BL → List Sym) (pw ps t1 W : ℕ) : Prop :=
  NatAt B sPW pw ∧ NatAt B sPS ps ∧ NatAt B sT1 t1 ∧ NatAt B sW W ∧ NatAt B sN1 (2 * ps + 1) ∧
  (∃ r, TermOK r ∧ B sPI = intSyms (computablePiScaledWithCost (W7.tapPrec ps)).1 ++ r) ∧
  (∃ r, TermOK r ∧ B sLN = intSyms (computableLog2ScaledWithCost (W7.tapPrec ps)).1 ++ r)

theorem FoldEnv.upd {B : BL → List Sym} {pw ps t1 W : ℕ} (h : FoldEnv B pw ps t1 W) {k : BL}
    (hk0 : inNamed [sPW, sPS, sT1, sW, sN1, sPI, sLN] k = false) (w : List Sym) :
    FoldEnv (Function.update B k w) pw ps t1 W := by
  have hk : k ∉ [sPW, sPS, sT1, sW, sN1, sPI, sLN] := fun hm => by
    rw [inNamed_iff.mpr hm] at hk0
    exact absurd hk0 (by decide)
  have k1 : sPW ≠ k := fun e => hk (by simp [e])
  have k2 : sPS ≠ k := fun e => hk (by simp [e])
  have k3 : sT1 ≠ k := fun e => hk (by simp [e])
  have k4 : sW ≠ k := fun e => hk (by simp [e])
  have k5 : sN1 ≠ k := fun e => hk (by simp [e])
  have k6 : sPI ≠ k := fun e => hk (by simp [e])
  have k7 : sLN ≠ k := fun e => hk (by simp [e])
  obtain ⟨h1, h2, h3, h4, h5, ⟨r6, t6, e6⟩, ⟨r7, t7, e7⟩⟩ := h
  exact ⟨h1.upd k1 w, h2.upd k2 w, h3.upd k3 w, h4.upd k4 w, h5.upd k5 w,
    ⟨r6, t6, by rw [Function.update_of_ne k6, e6]⟩, ⟨r7, t7, by rw [Function.update_of_ne k7, e7]⟩⟩

/-! ## One term -/

/-- One term of a folded tap: `acc += tap(s)`, `s += W` (`acc` on `y3`, `s` on `y4`). -/
def tapStep (I : BI) : BP I :=
  (btp I sPW sPS sT1 y1 y4 sPI sLN y5).seq <|
  (bai I y3 y5 y6).seq <|
  (bdrI I y5).seq <|
  (bdrI I y3).seq <|
  (bmvI I y6 y3).seq <|
  (bad I y4 sW y7).seq <|
  (bdr I y4).seq <|
  (bcp I y7 y4).seq <|
  bdr I y7

theorem tapStep_closed (I : BI) : (tapStep I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, bdrI_closed _ _, bdrI_closed _ _, bmvI_closed _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

section Fold

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem tapStep_spec (hI : I.Spec Mul C) (pw ps t1 W j1 s Q : ℕ) (acc : ℤ) (B : BL → List Sym)
    (hE : FoldEnv B pw ps t1 W) (hJ : NatAt B y1 j1)
    (r3 r4 : List Sym) (h3 : TermOK r3) (h4 : TermOK r4)
    (e3 : B y3 = intSyms acc ++ r3) (e4 : B y4 = natSyms s ++ r4)
    (h5 : TermOK (B y5)) (h6 : TermOK (B y6)) (h7 : TermOK (B y7))
    (hpw : 0 < pw) (hps : 0 < ps) (ht1 : 0 < t1) (hj1 : j1 < t1) (hs : s < 2 * ps + 1)
    (hQ1 : pw + ps + bitLen t1 + 1 ≤ Q) (hQ2 : bitLen acc.natAbs + 1 ≤ Q) (hQ3 : ps + 3 ≤ Q)
    (hQ4 : bitLen (acc + tapV pw ps t1 j1 s).natAbs + 1 ≤ Q) (hQ5 : bitLen (s + W) + 1 ≤ Q)
    (ρ : List (BP I)) :
    HT ρ B (tapStep I)
      (Function.update (Function.update B y3 (intSyms (acc + tapV pw ps t1 j1 s) ++ r3)) y4
        (natSyms (s + W) ++ r4))
      (C * Q ^ 4 + 12 * (C * Q) + 5) := by
  obtain ⟨⟨rpw, hrpw, epw⟩, ⟨rps, hrps, eps⟩, ⟨rt, hrt, et⟩, ⟨rw, hrw, ew⟩, -,
    ⟨rpi, hrpi, epi⟩, ⟨rln, hrln, eln⟩⟩ := hE
  obtain ⟨rj, hrj, ej⟩ := hJ
  have wt : bitLen (tapV pw ps t1 j1 s).natAbs ≤ ps + 1 := by
    apply bitLen_le_of_lt
    have h1 := tapV_natAbs_le pw ps t1 j1 s hpw hps ht1 hj1 hs
    have h2 : 2 ^ ps + 1 < 2 ^ (ps + 1) := by
      rw [pow_succ]
      have := Nat.one_lt_two_pow (n := ps) (by omega)
      omega
    omega
  apply HT.mono
  · refine HT.seq (HT.btp hI sPW sPS sT1 y1 y4 sPI sLN y5 (by decide) B pw ps t1 j1 s
      rpw rps rt rj r4 rpi rln hpw hps ht1 hj1 hs hrpw hrps hrt hrj h4 hrpi hrln epw eps et ej e4
      epi eln ρ) <|
      HT.seq (HT.bai hI y3 y5 y6 (by decide) _ acc (tapV pw ps t1 j1 s) r3 (B y5) h3 h5
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, e3]) (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      HT.seq (HT.bdrI hI y5 _ (tapV pw ps t1 j1 s) (B y5) h5 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      HT.seq (HT.bdrI hI y3 _ acc r3 h3 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, e3]) ρ) <|
      HT.seq (bmvI_spec hI y6 y3 (by decide) _ (acc + tapV pw ps t1 j1 s) (B y6) h6 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      HT.seq (HT.bad hI y4 sW y7 (by decide) _ s W r4 rw h4 hrw (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, e4])
        (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ew]) ρ) <|
      HT.seq (HT.bdr hI y4 _ s r4 h4 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, e4]) ρ) <|
      HT.seq (HT.bcp hI y7 y4 (by decide) _ (s + W) (B y7) h7 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ) <|
      (HT.bdr hI y7 _ (s + W) (B y7) h7 (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) ρ).of_eq (by simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]) le_rfl
  · have q4 : C * (pw + ps + bitLen t1 + 1) ^ 4 ≤ C * Q ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ1 4)
    have hsW : bitLen s ≤ bitLen (s + W) := bitLen_mono (by omega)
    have hWW : bitLen W ≤ bitLen (s + W) := bitLen_mono (by omega)
    have a1 := cq_le (C := C) 2 (show bitLen acc.natAbs + bitLen (tapV pw ps t1 j1 s).natAbs + 1 ≤
      2 * Q by omega)
    have a2 := cq_le (C := C) 1 (show bitLen (tapV pw ps t1 j1 s).natAbs + 1 ≤ 1 * Q by omega)
    have a3 := cq_le (C := C) 1 (show bitLen acc.natAbs + 1 ≤ 1 * Q by omega)
    have a4 := cq_le (C := C) 1
      (show bitLen (acc + tapV pw ps t1 j1 s).natAbs + 1 ≤ 1 * Q by omega)
    have a5 := cq_le (C := C) 2 (show bitLen s + bitLen W + 1 ≤ 2 * Q by omega)
    have a6 := cq_le (C := C) 1 (show bitLen s + 1 ≤ 1 * Q by omega)
    have a7 := cq_le (C := C) 1 (show bitLen (s + W) + 1 ≤ 1 * Q by omega)
    omega

end Fold

#assert_std_axioms exists_ap_count sum_filter_mod_eq natAbs_sum_range_le bitLen_sum_le
  tapV_natAbs_le cq_le FoldEnv.upd tapStep_closed tapStep_spec

end WP.W7k2
