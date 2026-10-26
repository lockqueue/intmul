import WP.W5.Toom
import Contracts.Machine.W5

/-!
# WP.W5.Main — one level, the recursion, and the contract `W5_toom3Mul`

* `body_spec`: one level `bodyP U` (prologue, counter loop, threshold test, then Toom-3 or the
  base case) meets `Pre g → Post g` within `F (μ g)`, given the recursion hypothesis, for any
  monotone `F` satisfying the two per-level inequalities (`hToom`, `hSchool`).
* `mul_spec`: `Triple.fix` closes the recursion.
* `FOf Cu = C1·T3 3 c1 9 + C1` satisfies the inequalities (`FOf_toom`, `FOf_school`).
* `W5_toom3Mul_holds`: the W5 contract, from the W3 contracts `addInt`, `subInt`,
  `smallOpInt`, `splitAt`, `shlVar` (hypotheses; discharged by the integrator).
  The program is `(mulP U).mapStk skLoc` over `Loc 3 8` (`X Y Z ↦ inl 0 1 2`, `s_j ↦ inr j`).
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## States of the common part of a level -/

/-- After the prologue: separators on `Z` and the scratch stacks, `|a|`, `|b|` on `s1`, `s2`. -/
def Epro (a b : ℤ) : L → List Ent :=
  mk11 [.I a] [.I b] [.S] [.S] [.N a.natAbs, .S] [.N b.natAbs, .S] [.S] [.S] [.S] [.S] [.S]

/-- After the counter loop. -/
def Ek (a b : ℤ) (K : ℕ) : L → List Ent :=
  Function.update (Function.update (Function.update (Epro a b) s0 [.N K, .S]) s1 [.S]) s2 [.S]

/-- The bases below the level's entries: the operand rests, everything else untouched. -/
def baseOf (S : L → List Sym) (ra rb : List Sym) : L → List Sym := fun k =>
  if k = X then ra else if k = Y then rb else S k

theorem allLe_E0 (a b : ℤ) (m : ℕ) (ha : bitLen a.natAbs ≤ m) (hb : bitLen b.natAbs ≤ m) :
    AllLe (E0 a b) m := by
  intro k e he
  cases k
  · exact allLe_one (e1 := .I a) ha e he
  · exact allLe_one (e1 := .I b) hb e he
  all_goals simp [E0] at he

theorem allLe_Epro (a b : ℤ) (m : ℕ) (ha : bitLen a.natAbs ≤ m) (hb : bitLen b.natAbs ≤ m) :
    AllLe (Epro a b) m := by
  have z0 : Ent.S.len ≤ m := Nat.zero_le _
  exact allLe_mk11 (allLe_one (e1 := .I a) ha) (allLe_one (e1 := .I b) hb)
    (allLe_one (e1 := .S) z0) (allLe_one (e1 := .S) z0)
    (allLe_two (e1 := .N a.natAbs) (e2 := .S) ha z0) (allLe_two (e1 := .N b.natAbs) (e2 := .S) hb z0)
    (allLe_one (e1 := .S) z0) (allLe_one (e1 := .S) z0) (allLe_one (e1 := .S) z0)
    (allLe_one (e1 := .S) z0) (allLe_one (e1 := .S) z0)

theorem allLe_Ek (a b : ℤ) (K m : ℕ) (ha : bitLen a.natAbs ≤ m) (hb : bitLen b.natAbs ≤ m)
    (hK : bitLen K ≤ m) : AllLe (Ek a b K) m := by
  have z0 : Ent.S.len ≤ m := Nat.zero_le _
  exact (((allLe_Epro a b m ha hb).update s0 _ (allLe_two (e1 := .N K) (e2 := .S) hK z0)).update
    s1 _ (allLe_one (e1 := .S) z0)).update s2 _ (allLe_one (e1 := .S) z0)

/-- The threshold register: the head of `s3` in the branch state. -/
theorem rBit_s3 {U : Subs} (a b : ℤ) (K : ℕ) (B : L → List Sym) (v : U.σ)
    (hv : v.1 = (stOf (Ebr a b K) B s3).head?) : rBit U v = decide (K / 2 / 2 ≠ 0) := by
  show optIsBit v.1 = _
  rw [hv, stOf_head (Ebr a b K) B (rfl : Ebr a b K s3 = [.N (K / 2 / 2), .S])]
  exact optIsBit_natSyms _ _ (TermOK.cons rfl _)

/-! ## One level -/

section Body

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu)

include hU in
/-- **One level of the procedure.** -/
theorem body_spec (F : ℕ → ℕ) (hF : Monotone F)
    (hToom : ∀ w K, 10 ≤ w → K = (w + 2) / 3 →
      3 * unit Cu w + 38 * K + 26 + (toomCost Cu w K + 5 * (F (K + 3) + 2)) ≤ F w)
    (hSchool : ∀ w K, w ≤ 9 → K = (w + 2) / 3 → 3 * unit Cu w + 38 * K + 26 + schoolCost Cu ≤ F w)
    (g : G)
    (IH : ∀ g' : G, μ g' < μ g → Triple [bodyP U] (Pre g') (.recur 0) (Post g') (F (μ g') + 2)) :
    Triple [bodyP U] (Pre g) (bodyP U) (Post g) (F (μ g)) := by
  rcases g with ⟨a, b, S⟩
  rintro s ⟨hs, ⟨ra, hra, hX⟩, ⟨rb, hrb, hY⟩⟩
  change s.stk = S at hs
  change S X = intSyms a ++ ra at hX
  change S Y = intSyms b ++ rb at hY
  have hB : ∀ k, bokXY k = true → TermOK (baseOf S ra rb k) := by
    intro k hk
    cases k
    · exact hra
    · exact hrb
    all_goals exact absurd hk (by decide)
  have hpre : stOf (E0 a b) (baseOf S ra rb) = S := by
    refine L_funext ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · show encL [.I a] ++ ra = S X
      rw [hX]; simp [Ent.enc]
    · show encL [.I b] ++ rb = S Y
      rw [hY]; simp [Ent.enc]
  have hpost : stOf (Function.update (E0 a b) Z [.I (a * b)]) (baseOf S ra rb) =
      Function.update S Z (intSyms (a * b) ++ S Z) := by
    refine L_funext ?_ ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl
    · show encL [.I a] ++ ra = S X
      rw [hX]; simp [Ent.enc]
    · show encL [.I b] ++ rb = S Y
      rw [hY]; simp [Ent.enc]
    · show encL [.I (a * b)] ++ S Z = intSyms (a * b) ++ S Z
      simp [Ent.enc]
  -- sizes
  obtain ⟨w, hw⟩ : ∃ w, μ ⟨a, b, S⟩ = w := ⟨_, rfl⟩
  have hwa : bitLen a.natAbs ≤ w := by rw [← hw]; exact le_max_left _ _
  have hwb : bitLen b.natAbs ≤ w := by rw [← hw]; exact le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K, K = kOf a.natAbs b.natAbs := ⟨_, rfl⟩
  have hKw : K = (w + 2) / 3 := by rw [hK, ← hw]; rfl
  have hKle : K ≤ w := by omega
  have hbK : bitLen K ≤ w := le_trans (bitLen_le_self K) hKle
  -- prologue, counter loop, threshold, peek
  have P1 := run_post hU hB [bodyP U] 0 (rfl : run bokXY 0 proOps (E0 a b) = some _) (by simp)
    (allLe_E0 a b w hwa hwb) (Epro a b) (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    2 11 0 0 w rfl rfl rfl rfl (by omega)
  have KL := kloop_spec hU hB [bodyP U] (Epro a b) a.natAbs b.natAbs w rfl rfl rfl
    (allLe_Epro a b w hwa hwb) hwa hwb (hK ▸ hKle)
  rw [← hK] at KL
  have TH := run_post hU hB [bodyP U] 0 (rfl : run bokXY 0 thrOps (Ek a b K) = some _) (by simp)
    (allLe_Ek a b K w hwa hwb hbK) (Ebr a b K)
    (L_funext rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) 1 6 0 0 w rfl rfl rfl rfl (by omega)
  have PK := peekL_triple [bodyP U] (stOf (Ebr a b K) (baseOf S ra rb)) s3
  -- the branch
  by_cases hK4 : 4 ≤ K
  · have TT := toom_spec hU hB F hF ⟨a, b, S⟩ IH a b w hw hwa hwb K hKw hK4
    have ITE : Triple [bodyP U]
        (fun s => s.stk = stOf (Ebr a b K) (baseOf S ra rb) ∧
          s.var.1 = (stOf (Ebr a b K) (baseOf S ra rb) s3).head?)
        (.ite (rBit U) (toomP U) (schoolP U))
        (fun s => s.stk = stOf (Function.update (E0 a b) Z [.I (a * b)]) (baseOf S ra rb))
        (toomCost Cu w K + 5 * (F (K + 3) + 2) + 1) := by
      refine Triple.ite (T := toomCost Cu w K + 5 * (F (K + 3) + 2)) (TT.pre fun s hs => hs.1.1) ?_
      rintro s ⟨⟨-, hv⟩, hc⟩
      rw [rBit_s3 a b K _ s.var hv] at hc
      exfalso
      simp only [ne_eq, decide_eq_false_iff_not, not_not] at hc
      omega
    have BODY := Triple.seq P1.1 (Triple.seq KL (Triple.seq TH.1 (Triple.seq PK ITE)))
    obtain ⟨s', t, e, hq, ht⟩ := BODY s (by show s.stk = _; rw [hs, hpre])
    refine ⟨s', t, e, hq.trans hpost, ?_⟩
    · have := hToom w K (by omega) hKw
      rw [hw]
      omega
  · have hK3 : K ≤ 3 := by omega
    have hw9 : w ≤ 9 := by omega
    have TS := school_spec hU hB [bodyP U] a b K (by omega) (by omega) hK3
    have ITE : Triple [bodyP U]
        (fun s => s.stk = stOf (Ebr a b K) (baseOf S ra rb) ∧
          s.var.1 = (stOf (Ebr a b K) (baseOf S ra rb) s3).head?)
        (.ite (rBit U) (toomP U) (schoolP U))
        (fun s => s.stk = stOf (Function.update (E0 a b) Z [.I (a * b)]) (baseOf S ra rb))
        (schoolCost Cu + 1) := by
      refine Triple.ite (T := schoolCost Cu) ?_ (TS.pre fun s hs => hs.1.1)
      rintro s ⟨⟨-, hv⟩, hc⟩
      rw [rBit_s3 a b K _ s.var hv] at hc
      exfalso
      simp only [ne_eq, decide_eq_true_eq] at hc
      omega
    have BODY := Triple.seq P1.1 (Triple.seq KL (Triple.seq TH.1 (Triple.seq PK ITE)))
    obtain ⟨s', t, e, hq, ht⟩ := BODY s (by show s.stk = _; rw [hs, hpre])
    refine ⟨s', t, e, hq.trans hpost, ?_⟩
    · have := hSchool w K hw9 hKw
      rw [hw]
      omega

include hU in
/-- **The procedure** (recursion closed by `Triple.fix`). -/
theorem mul_spec (F : ℕ → ℕ) (hF : Monotone F)
    (hToom : ∀ w K, 10 ≤ w → K = (w + 2) / 3 →
      3 * unit Cu w + 38 * K + 26 + (toomCost Cu w K + 5 * (F (K + 3) + 2)) ≤ F w)
    (hSchool : ∀ w K, w ≤ 9 → K = (w + 2) / 3 → 3 * unit Cu w + 38 * K + 26 + schoolCost Cu ≤ F w) :
    ∀ g : G, Triple [] (Pre g) (mulP U) (Post g) (F (μ g) + 2) :=
  Triple.fix (T := fun g => F (μ g)) μ fun g IH => body_spec hU F hF hToom hSchool g IH

end Body

/-! ## The cost function -/

/-- Slope of the linear part of one Toom-3 level. -/
def lvA (Cu : ℕ) : ℕ := 1000 * Cu + 4000
/-- Offset of the linear part of one Toom-3 level. -/
def lvB (Cu : ℕ) : ℕ := 10000 * Cu + 40000
/-- The recurrence constant `c1` of `T3`. -/
def c1Of (Cu : ℕ) : ℕ := lvA Cu + lvB Cu + 1
/-- The outer constant (covers the base case). -/
def C1Of (Cu : ℕ) : ℕ := 87 * unit Cu 22 + 240
/-- The cost function: `C1·T3 3 c1 9 w + C1`. -/
def FOf (Cu w : ℕ) : ℕ := C1Of Cu * T3 3 (c1Of Cu) 9 w + C1Of Cu

theorem FOf_mono (Cu : ℕ) : Monotone (FOf Cu) := by
  intro x y h
  have := Nat.mul_le_mul_left (C1Of Cu) (T3_mono 3 (c1Of Cu) 9 h)
  unfold FOf
  omega

theorem unit_lin (Cu w : ℕ) : unit Cu (3 * w + 30) = 6 * (Cu * w) + 62 * Cu + 24 * w + 256 := by
  unfold unit
  ring

theorem FOf_toom (Cu : ℕ) : ∀ w K, 10 ≤ w → K = (w + 2) / 3 →
    3 * unit Cu w + 38 * K + 26 + (toomCost Cu w K + 5 * (FOf Cu (K + 3) + 2)) ≤ FOf Cu w := by
  intro w K hw hK
  -- the linear part is at most `lvA·w + lvB`
  have u1 := unit_mono Cu (show w ≤ 3 * w + 30 by omega)
  have u2 := unit_mono Cu (show w + 6 * K + 26 ≤ 3 * w + 30 by omega)
  have hl := unit_lin Cu w
  have hAB : lvA Cu * w + lvB Cu = 1000 * (Cu * w) + 4000 * w + 10000 * Cu + 40000 := by
    unfold lvA lvB; ring
  have hlin : 3 * unit Cu w + 38 * K + 26 + toomCost Cu w K + 10 ≤ lvA Cu * w + lvB Cu := by
    unfold toomCost
    omega
  -- the recurrence step
  have hT : T3 3 (c1Of Cu) 9 w = 5 * T3 3 (c1Of Cu) 9 (K + 3) + c1Of Cu * w := by
    rw [T3_unfold, if_pos ⟨by omega, by omega⟩, hK]
  have hC1 : 1 ≤ C1Of Cu := by unfold C1Of; omega
  have h1 : lvA Cu * w ≤ C1Of Cu * (lvA Cu * w) := Nat.le_mul_of_pos_left _ hC1
  have h2 : lvB Cu ≤ C1Of Cu * (lvB Cu * w) :=
    le_trans (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_mul_of_pos_left _ hC1)
  have h3 : C1Of Cu * 4 ≤ C1Of Cu * w := Nat.mul_le_mul_left _ (by omega)
  have hexp : C1Of Cu * T3 3 (c1Of Cu) 9 w = 5 * (C1Of Cu * T3 3 (c1Of Cu) 9 (K + 3)) +
      C1Of Cu * (lvA Cu * w) + C1Of Cu * (lvB Cu * w) + C1Of Cu * w := by
    rw [hT]; unfold c1Of; ring
  unfold FOf
  omega

theorem FOf_school (Cu : ℕ) : ∀ w K, w ≤ 9 → K = (w + 2) / 3 →
    3 * unit Cu w + 38 * K + 26 + schoolCost Cu ≤ FOf Cu w := by
  intro w K hw hK
  have u1 := unit_mono Cu (show w ≤ 22 by omega)
  unfold FOf C1Of schoolCost
  omega

/-! ## Closedness -/

theorem freeBelow_mono {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, d ≤ d' → p.FreeBelow d → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, hd, h => ⟨freeBelow_mono p hd h.1, freeBelow_mono q hd h.2⟩
  | .ite _ p q, _, _, hd, h => ⟨freeBelow_mono p hd h.1, freeBelow_mono q hd h.2⟩
  | .loop _ p, _, _, hd, h => freeBelow_mono p hd h
  | .fix b, _, _, hd, h => freeBelow_mono b (Nat.succ_le_succ hd) h
  | .recur _, _, _, hd, h => lt_of_lt_of_le h hd

theorem closed_free {K : Type} {Γ : K → Type} {σ : Type} {p : Prog K Γ σ} (h : p.Closed)
    (d : ℕ) : p.FreeBelow d :=
  freeBelow_mono p (Nat.zero_le d) h

section Closed

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu)

include hU in
theorem Op.prog_closed : ∀ o : Op, (o.prog U).Closed
  | .add _ _ _ => closed_liftRegs _ (closed_mapStk _ hU.add_c)
  | .sub _ _ _ => closed_liftRegs _ (closed_mapStk _ hU.sub_c)
  | .sop .mul2 _ => closed_liftRegs _ (closed_mapStk _ hU.mul2_c)
  | .sop .div2 _ => closed_liftRegs _ (closed_mapStk _ hU.div2_c)
  | .sop .div3 _ => closed_liftRegs _ (closed_mapStk _ hU.div3_c)
  | .sop .mul3 _ => trivial
  | .split _ _ _ => closed_liftRegs _ (closed_mapStk _ hU.split_c)
  | .shl _ _ => closed_liftRegs _ (closed_mapStk _ hU.shl_c)
  | .copyI _ _ => closed_liftRegs _ (copyIP_closed _ _ _ _)
  | .copyN _ _ => closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock,
      moveBits, moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip])
  | .dropI _ => closed_liftRegs _ (dropIP_closed _)
  | .toNat _ => trivial
  | .toInt _ => trivial
  | .pushZ _ => trivial
  | .pushS _ => trivial
  | .popS _ => trivial
  | .clr _ => closed_liftRegs _ (clrP_closed _)
  | .shr1 _ => closed_liftRegs _ (shr1P_closed _)
  | .sfix _ _ _ => closed_liftRegs _ (sfixP_closed _ _ _)

include hU in
theorem seqOf_free : ∀ (ops : List Op) (d : ℕ), (seqOf U ops).FreeBelow d
  | [], _ => trivial
  | o :: os, d => ⟨closed_free (Op.prog_closed hU o) d, seqOf_free os d⟩

theorem peekL_free (k : L) (d : ℕ) : (peekL U k).FreeBelow d := trivial

theorem ztP_free (d : ℕ) : (ztP U).FreeBelow d := ⟨trivial, trivial, trivial⟩

include hU in
theorem kloopP_free (d : ℕ) : (kloopP U).FreeBelow d := by
  refine ⟨ztP_free d, ⟨seqOf_free hU _ d, ?_⟩, ztP_free d⟩
  exact closed_free (closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix,
    scanLoop, scanBody, pushC, popR, restoreR, pushR, skip, moveBits, moveBitsBody])) d

include hU in
theorem toomP_free : (toomP U).FreeBelow 1 :=
  ⟨seqOf_free hU _ _, Nat.zero_lt_one, seqOf_free hU _ _, Nat.zero_lt_one, seqOf_free hU _ _,
    Nat.zero_lt_one, seqOf_free hU _ _, Nat.zero_lt_one, seqOf_free hU _ _, Nat.zero_lt_one,
    seqOf_free hU _ _⟩

include hU in
theorem schoolP_free (d : ℕ) : (schoolP U).FreeBelow d :=
  ⟨seqOf_free hU _ _, peekL_free _ _, ⟨⟨seqOf_free hU _ _, trivial⟩, seqOf_free hU _ _,
    peekL_free _ _⟩, seqOf_free hU _ _⟩

include hU in
theorem mulP_closed : (mulP U).Closed :=
  ⟨seqOf_free hU _ _, kloopP_free hU _, seqOf_free hU _ _, peekL_free _ _, toomP_free hU,
    schoolP_free hU _⟩

end Closed

/-! ## Stack names of the contract -/

/-- `X Y Z ↦ inl 0 1 2`, `s_j ↦ inr j`. -/
def skLoc : L → Loc 3 8
  | .X => .inl 0
  | .Y => .inl 1
  | .Z => .inl 2
  | .s0 => .inr 0
  | .s1 => .inr 1
  | .s2 => .inr 2
  | .s3 => .inr 3
  | .s4 => .inr 4
  | .s5 => .inr 5
  | .s6 => .inr 6
  | .s7 => .inr 7

/-- Inverse of `skLoc`. -/
def locSK : Loc 3 8 → L
  | .inl ⟨0, _⟩ => .X
  | .inl ⟨1, _⟩ => .Y
  | .inl _ => .Z
  | .inr ⟨0, _⟩ => .s0
  | .inr ⟨1, _⟩ => .s1
  | .inr ⟨2, _⟩ => .s2
  | .inr ⟨3, _⟩ => .s3
  | .inr ⟨4, _⟩ => .s4
  | .inr ⟨5, _⟩ => .s5
  | .inr ⟨6, _⟩ => .s6
  | .inr _ => .s7

theorem locSK_skLoc : ∀ l : L, locSK (skLoc l) = l := by
  intro l; cases l <;> rfl

theorem skLoc_inj : Function.Injective skLoc :=
  Function.LeftInverse.injective locSK_skLoc

theorem skLoc_locSK : ∀ k : Loc 3 8, skLoc (locSK k) = k
  | .inl ⟨0, _⟩ => rfl
  | .inl ⟨1, _⟩ => rfl
  | .inl ⟨2, _⟩ => rfl
  | .inl ⟨n + 3, h⟩ => absurd h (by omega)
  | .inr ⟨0, _⟩ => rfl
  | .inr ⟨1, _⟩ => rfl
  | .inr ⟨2, _⟩ => rfl
  | .inr ⟨3, _⟩ => rfl
  | .inr ⟨4, _⟩ => rfl
  | .inr ⟨5, _⟩ => rfl
  | .inr ⟨6, _⟩ => rfl
  | .inr ⟨7, _⟩ => rfl
  | .inr ⟨n + 8, h⟩ => absurd h (by omega)

/-! ## The contract -/

/-- The W3 subroutines, bundled with one common constant. -/
theorem subs_of_W3 (hadd : W3_addInt) (hsub : W3_subInt) (hsop : W3_smallOpInt)
    (hsplit : W3_splitAt) (hshl : W3_shlVar) : ∃ (U : Subs) (Cu : ℕ), SubsOK U Cu := by
  obtain ⟨Ca, ha⟩ := hadd
  obtain ⟨ma, Ra, -, Pa, hma, hfa, hna, hca, hsa⟩ := ha ()
  obtain ⟨Cs, hs⟩ := hsub
  obtain ⟨ms, Rs, -, Ps, hms, hfs, hns, hcs, hss⟩ := hs ()
  obtain ⟨Co, ho⟩ := hsop
  obtain ⟨m2, R2, -, P2, hm2, hf2, hn2, hc2, hs2⟩ := ho .mul2
  obtain ⟨md, Rd, -, Pd, hmd, hfd, hnd, hcd, hsd⟩ := ho .div2
  obtain ⟨m3, R3, -, P3, hm3, hf3, hn3, hc3, hs3⟩ := ho .div3
  obtain ⟨Cp, hp⟩ := hsplit
  obtain ⟨mp, Rp, -, Pp, hmp, hfp, hnp, hcp, hsp⟩ := hp ()
  obtain ⟨Ch, hh⟩ := hshl
  obtain ⟨mh, Rh, -, Ph, hmh, hfh, hnh, hch, hsh⟩ := hh ()
  refine ⟨⟨⟨ma, hma, Ra, Pa⟩, ⟨ms, hms, Rs, Ps⟩, ⟨m2, hm2, R2, P2⟩, ⟨md, hmd, Rd, Pd⟩,
    ⟨m3, hm3, R3, P3⟩, ⟨mp, hmp, Rp, Pp⟩, ⟨mh, hmh, Rh, Ph⟩⟩, Ca + Cs + Co + Cp + Ch,
    ⟨hca, fun a b rx ry S h1 h2 h3 h4 => Triple.cost_mono (hsa a b rx ry S h1 h2 h3 h4)
      (Nat.mul_le_mul_right _ (by omega)),
    hcs, fun a b rx ry S h1 h2 h3 h4 => Triple.cost_mono (hss a b rx ry S h1 h2 h3 h4)
      (Nat.mul_le_mul_right _ (by omega)),
    hc2, fun z rx S h1 h2 h3 => Triple.cost_mono (hs2 z rx S h1 h2 h3)
      (Nat.mul_le_mul_right _ (by omega)),
    hcd, fun z rx S h1 h2 h3 => Triple.cost_mono (hsd z rx S h1 h2 h3)
      (Nat.mul_le_mul_right _ (by omega)),
    hc3, fun z rx S h1 h2 h3 => Triple.cost_mono (hs3 z rx S h1 h2 h3)
      (Nat.mul_le_mul_right _ (by omega)),
    hcp, fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (hsp a c rx rc S h1 h2 h3 h4)
      (Nat.mul_le_mul_right _ (by omega)),
    hch, fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (hsh a c rx rc S h1 h2 h3 h4)
      (Nat.mul_le_mul_right _ (by omega)),
    ⟨hfa, hfs, hf2, hfd, hf3, hfp, hfh⟩, ⟨hna, hns, hn2, hnd, hn3, hnp, hnh⟩⟩⟩

theorem SubsOK.finite {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) : Finite U.σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU.fin
  infer_instance

theorem SubsOK.nonempty {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) : Nonempty U.σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU.ne
  infer_instance

/-- **W5 (Toom-3 multiplication on the machine)**, from the W3 contracts it uses. -/
theorem W5_toom3Mul_holds (hadd : W3_addInt) (hsub : W3_subInt) (hsop : W3_smallOpInt)
    (hsplit : W3_splitAt) (hshl : W3_shlVar) : W5_toom3Mul := by
  obtain ⟨U, Cu, hU⟩ := subs_of_W3 hadd hsub hsop hsplit hshl
  refine ⟨3, c1Of Cu, 9, C1Of Cu + 2, fun _ => ⟨8, U.σ, fun _ => (), (mulP U).mapStk skLoc, le_rfl,
    hU.finite, hU.nonempty, closed_mapStk _ (mulP_closed hU), ?_⟩⟩
  intro w a b ra rb S ha hb hra hrb hSa hSb
  have M := mul_spec hU (FOf Cu) (FOf_mono Cu) (FOf_toom Cu) (FOf_school Cu)
    ⟨a, b, fun k => S (skLoc k)⟩
  have R : Runs (mulP U) (fun k => S (skLoc k))
      (Function.update (fun k => S (skLoc k)) Z (intSyms (a * b) ++ S (skLoc Z))) (fun _ => True)
      (FOf Cu (μ ⟨a, b, fun k => S (skLoc k)⟩) + 2) :=
    M.conseq (fun s hs => ⟨hs, ⟨ra, hra, hSa⟩, ⟨rb, hrb, hSb⟩⟩) (fun s hs => ⟨hs, trivial⟩) le_rfl
  have E := Runs.embed skLoc_inj R S (fun _ => rfl)
  refine E.conseq (fun s hs => hs) (fun s hs => ⟨?_, trivial⟩) ?_
  · funext k
    obtain ⟨l, rfl⟩ : ∃ l, skLoc l = k := ⟨locSK k, skLoc_locSK k⟩
    rw [hs.1 l]
    by_cases hl : l = Z
    · subst hl
      rw [Function.update_self]
      exact (Function.update_self (Sum.inl 2 : Loc 3 8) (intSyms (a * b) ++ S (Sum.inl 2)) S).symm
    · rw [Function.update_of_ne hl,
        Function.update_of_ne (fun h => hl (skLoc_inj (h.trans (rfl : (Sum.inl 2 : Loc 3 8) = skLoc Z))))]
  · have hμ : μ ⟨a, b, fun k => S (skLoc k)⟩ ≤ w := max_le ha hb
    have h1 := Nat.mul_le_mul_left (C1Of Cu) (T3_mono 3 (c1Of Cu) 9 hμ)
    have h2 := Nat.mul_le_mul_right (T3 3 (c1Of Cu) 9 w) (show C1Of Cu ≤ C1Of Cu + 2 by omega)
    unfold FOf
    omega

#assert_std_axioms body_spec mul_spec FOf_toom FOf_school mulP_closed skLoc_inj skLoc_locSK
  subs_of_W3 W5_toom3Mul_holds

end WP.W5
