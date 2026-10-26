import WP.W7k2.B.Step2
import WP.W7k2.B.LevelSum

/-!
# WP.W7k2.B.Fix — the level recursion of the table builder

* `stopTest` (`2^K` on `y0`, `4p²` on `y1`), `dropTest`, `lvBody`, `levels := fix lvBody`
  (the recursive level-builder programs of `WP.W7k2.B`).
* `levels_spec`: from the level state `LS S Lc p K pIn blk tr`, `levels` builds the canonical tape
  `tapeFromC pIn Lc p K` on `TR` above the staged pre segments, within
  `levelSum (stepLvG C KM) (leafLvG C KM) pIn Lc p K + 3·|blk| + 2`. Proof: `Triple.fix` with measure
  `Lc`; invariant `8 ≤ p, Lc ≤ p + K, K ≤ 2^(Lc+1), pIn ≤ 2p, mark ∉ blk`.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-! ## Programs -/

/-- `y0 += 2^K`, `y1 += 4p²`. -/
def stopTest (I : BI) : BP I :=
  (bp2 I vK y0).seq <| (bnm I vp vp y2 y3 y1).seq <| (bs1 I y1).seq (bs1 I y1)

/-- Drop the two test values. -/
def dropTest (I : BI) : BP I := (bdr I y1).seq (bdr I y0)

/-- One level: leaf at `Lc = 0` or `K = 0` or when `2^K ≤ 4p²`, else a step and the recursive call. -/
def lvBody (I : BI) : BP I :=
  (biz I vL).seq (.ite (fun s => I.iz.obs (I.liz.get s)) (leafPart I)
    ((biz I vK).seq (.ite (fun s => I.iz.obs (I.liz.get s)) (leafPart I)
      ((stopTest I).seq ((bcm I y0 y1).seq
        (.ite (fun s => decide (I.cm.obs (I.lcm.get s) ≠ .gt))
          ((dropTest I).seq (leafPart I))
          ((dropTest I).seq ((stepPart I).seq (.recur 0)))))))))

/-- The level recursion. -/
def levels (I : BI) : BP I := .fix (lvBody I)

theorem stopTest_closed (I : BI) : (stopTest I).Closed :=
  ⟨bp2_closed I _ _, bnm_closed I _ _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem dropTest_closed (I : BI) : (dropTest I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem levels_closed (I : BI) : (levels I).Closed := by
  have h : ∀ q : BP I, q.Closed → q.FreeBelow 1 := fun q hq => freeBelow_mono q hq (Nat.zero_le 1)
  exact ⟨h _ (callI_closed _ _ _ _), h _ (leafPart_closed I), h _ (callI_closed _ _ _ _),
    h _ (leafPart_closed I), h _ (stopTest_closed I), h _ (callI_closed _ _ _ _),
    ⟨h _ (dropTest_closed I), h _ (leafPart_closed I)⟩, h _ (dropTest_closed I),
    h _ (stepPart_closed I), Nat.zero_lt_one⟩

/-! ## Pure facts -/

/-- The column divisors of a step level of the snapshot schedule are positive. -/
theorem fix_colDiv_pos (Lc p K : ℕ) (hp : 8 ≤ p) (hK : K ≤ 2 ^ (Lc + 1 + 1))
    (hstop : ¬ 2 ^ K ≤ 4 * p * p) :
    ∀ u2 < 2 ^ (K - K / 2), 0 < IntMulTM.Contracts.W8.columnDivisor (2 ^ (K - K / 2)) u2
      (c0V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)
      (c1V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2) := by
  have hf := W7.snapshotSchedule.ref_faithful (Lc + 1) p K hp hK
  have hv := IntMul.buildQuantizedSpecPaperStop_valid (Lc + 1) p K hp
  have hpos := IntMulTM.Contracts.W8_columnDivisor_pos_of_faithful_holds _ _ hv hf
  rw [buildQuantizedSpecPaperStop_succ, if_neg hstop] at hpos
  simp only [W7.snapshotSchedule, quantizedBoxGaussianStepSpec, build_step] at hpos
  intro u2 hu2
  have h := hpos.1 u2 hu2
  rwa [stepC0_read p K _ _ u2 hu2, stepC1_read p K _ _ u2 hu2] at h

/-- `stepCostE` is monotone in its level-counter argument. -/
theorem fix_stepCostE_mono (C KM p K pIn Lc Lc' : ℕ) (h : Lc ≤ Lc') :
    stepCostE C KM p K pIn Lc ≤ stepCostE C KM p K pIn Lc' := by
  have hb : C * (bitLen Lc + 1) ≤ C * (bitLen Lc' + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (bitLen_mono h) 1)
  simp only [stepCostE]
  omega

/-! ## The stop test -/

/-- Cost of `stopTest` (`HT.bp2`, `HT.bnm`, two `HT.bs1`). -/
def stopTestCost (C : ℕ) (Mul : ℕ → ℕ) (p K : ℕ) : ℕ :=
  (2 + C * (K + bitLen K + 1)) + ((2 * (C * (bitLen p + 1)) + 2 * (C * (bitLen p + 1)) +
    (C * Mul (max (bitLen p) (bitLen p)) + C) + 5) + (C * (1 + 1) + C * (1 + 1)))

/-- The stop test, the compare and the drops fit `stopCost`. -/
theorem stop_le {Mul : ℕ → ℕ} (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2) (C p K : ℕ) :
    stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + 1) +
      (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1)) ≤ stopCost C KM p K := by
  have h := Nat.mul_le_mul_left C (hMul (bitLen p))
  unfold stopTestCost stopCost
  rw [max_self]
  omega

/-- Cost of the leaf part at the canonical `Qb`, `Qk` (`leafPart_spec`). -/
def leafCostL (C p K pIn Lc : ℕ) (blk : List Sym) : ℕ :=
  leafSegCost C (bitLen (2 * p + K + 8) + 5) (2 * p + 2 * K + 40) p K pIn +
    (3 * blk.length + 2 + (C * (bitLen Lc + 1) + (C * (bitLen p + 1) + (C * (bitLen K + 1) +
      C * (bitLen pIn + 1)))))

section Test

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem stopTest_spec (hI : I.Spec Mul C) (p K : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hvp : NatAt B vp p) (hvK : NatAt B vK K) (h0 : TermOK (B y0)) (h1 : TermOK (B y1))
    (h2 : TermOK (B y2)) (h3 : TermOK (B y3)) :
    HT ρ B (stopTest I)
      (Function.update (Function.update B y0 (natSyms (2 ^ K) ++ B y0)) y1
        (natSyms (4 * p * p) ++ B y1)) (stopTestCost C Mul p K) := by
  obtain ⟨rp, hrp, ep⟩ := hvp
  obtain ⟨rK, hrK, eK⟩ := hvK
  have e1 := HT.bp2 hI vK y0 (by decide) B K rK hrK eK h0 ρ
  have e2 := HT.bnm hI vp vp y2 y3 y1 (by decide) (by decide)
    (Function.update B y0 (natSyms (2 ^ K) ++ B y0)) p p rp rp hrp hrp
    (by rw [Function.update_of_ne (by decide)]; exact ep)
    (by rw [Function.update_of_ne (by decide)]; exact ep)
    (by rw [Function.update_of_ne (by decide)]; exact h2)
    (by rw [Function.update_of_ne (by decide)]; exact h3) ρ
  have e3 := HT.bs1 hI y1 (Function.update (Function.update B y0 (natSyms (2 ^ K) ++ B y0)) y1
      (natSyms (p * p) ++ Function.update B y0 (natSyms (2 ^ K) ++ B y0) y1)) (p * p) (B y1) h1
    (by rw [Function.update_self, Function.update_of_ne (by decide)]) ρ
  have e4 := HT.bs1 hI y1 (Function.update (Function.update (Function.update B y0
      (natSyms (2 ^ K) ++ B y0)) y1
      (natSyms (p * p) ++ Function.update B y0 (natSyms (2 ^ K) ++ B y0) y1)) y1
      (natSyms (p * p * 2 ^ 1) ++ B y1)) (p * p * 2 ^ 1) (B y1) h1
    (by rw [Function.update_self]) ρ
  refine (HT.seq e1 (HT.seq e2 (HT.seq e3 e4))).of_eq ?_ le_rfl
  rw [Function.update_idem, Function.update_idem, show p * p * 2 ^ 1 * 2 ^ 1 = 4 * p * p by ring]

theorem dropTest_spec (hI : I.Spec Mul C) (a b : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (h0 : TermOK (B y0)) (h1 : TermOK (B y1)) :
    HT ρ (Function.update (Function.update B y0 (natSyms a ++ B y0)) y1 (natSyms b ++ B y1))
      (dropTest I) B (C * (bitLen b + 1) + C * (bitLen a + 1)) := by
  refine (HT.seq (HT.bdr hI y1 _ b (B y1) h1 (by rw [Function.update_self]) ρ)
    (HT.bdr hI y0 _ a (B y0) h0
      (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]) ρ)).of_eq ?_ le_rfl
  funext k
  by_cases hk0 : k = y0
  · subst hk0
    rw [Function.update_self]
  · rw [Function.update_of_ne hk0]
    by_cases hk1 : k = y1
    · subst hk1
      rw [Function.update_self]
    · rw [Function.update_of_ne hk1, Function.update_of_ne hk1, Function.update_of_ne hk0]

end Test

/-! ## The level state -/

section Body

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem LS_vL (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) :
    LS S Lc p K pIn blk tr vL = natSyms Lc ++ Sym.mark :: S vL := by
  simp (config := { failIfUnchanged := false }) (disch := decide) only [LS,
    Function.update_self, Function.update_of_ne]

theorem LS_vp (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) :
    LS S Lc p K pIn blk tr vp = natSyms p ++ Sym.mark :: S vp := by
  simp (config := { failIfUnchanged := false }) (disch := decide) only [LS,
    Function.update_self, Function.update_of_ne]

theorem LS_vK (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) :
    LS S Lc p K pIn blk tr vK = natSyms K ++ Sym.mark :: S vK := by
  simp (config := { failIfUnchanged := false }) (disch := decide) only [LS,
    Function.update_self, Function.update_of_ne]

theorem LS_y (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) (y : BL)
    (hy : inNamed floorSlots y = true) (h1 : y ≠ sTR) (h2 : y ≠ vL) (h3 : y ≠ vp) (h4 : y ≠ vK)
    (h5 : y ≠ vpI) (h6 : y ≠ sSTG) : TermOK (LS S Lc p K pIn blk tr y) := by
  simp only [LS]
  rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
    Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1, Bf_floor S y hy]
  exact termOK_mark _

theorem leafPart_LS (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym)
    (ρ : List (BP I)) (hblk : Sym.mark ∉ blk) :
    HT ρ (LS S Lc p K pIn blk tr) (leafPart I) (FS S (blk.reverse ++ (leafSegC pIn p K ++ tr)))
      (leafCostL C p K pIn Lc blk) :=
  leafPart_spec hI S Lc p K pIn blk tr _ _ ρ hblk le_rfl le_rfl

/-- `Lc = 0`: the first test sends the level to the leaf part. -/
theorem body_leaf0 (hI : I.Spec Mul C) (S : BL → List Sym) (p K pIn : ℕ) (blk tr : List Sym)
    (ρ : List (BP I)) (hblk : Sym.mark ∉ blk) :
    HT ρ (LS S 0 p K pIn blk tr) (lvBody I) (FS S (blk.reverse ++ (leafSegC pIn p K ++ tr)))
      (C + (leafCostL C p K pIn 0 blk + 1)) := by
  unfold lvBody
  refine (HT.bizIte hI vL _ _ 0 (Sym.mark :: S vL) (termOK_mark _) (LS_vL S 0 p K pIn blk tr) _ _
    ρ (T₁ := leafCostL C p K pIn 0 blk) (T₂ := leafCostL C p K pIn 0 blk)
    (fun _ => leafPart_LS hI S 0 p K pIn blk tr ρ hblk) (fun h => absurd rfl h)).mono ?_
  simp only [max_self, le_refl]

/-- `Lc ≠ 0`, `K = 0`: the second test sends the level to the leaf part. -/
theorem body_leafK0 (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p pIn : ℕ) (blk tr : List Sym)
    (ρ : List (BP I)) (hblk : Sym.mark ∉ blk) :
    HT ρ (LS S (Lc + 1) p 0 pIn blk tr) (lvBody I)
      (FS S (blk.reverse ++ (leafSegC pIn p 0 ++ tr)))
      (2 * C + leafCostL C p 0 pIn (Lc + 1) blk + 2) := by
  unfold lvBody
  refine (HT.bizIte hI vL _ _ (Lc + 1) (Sym.mark :: S vL) (termOK_mark _)
    (LS_vL S (Lc + 1) p 0 pIn blk tr) _ _ ρ
    (T₁ := C + (leafCostL C p 0 pIn (Lc + 1) blk + 1))
    (T₂ := C + (leafCostL C p 0 pIn (Lc + 1) blk + 1))
    (fun h => absurd h (Nat.succ_ne_zero Lc)) (fun _ => ?_)).mono (by simp only [max_self]; omega)
  refine (HT.bizIte hI vK _ _ 0 (Sym.mark :: S vK) (termOK_mark _)
    (LS_vK S (Lc + 1) p 0 pIn blk tr) _ _ ρ
    (T₁ := leafCostL C p 0 pIn (Lc + 1) blk) (T₂ := leafCostL C p 0 pIn (Lc + 1) blk)
    (fun _ => leafPart_LS hI S (Lc + 1) p 0 pIn blk tr ρ hblk) (fun h => absurd rfl h)).mono
    (by simp only [max_self, le_refl])

/-- `Lc ≠ 0`, `K ≠ 0`, `2^K ≤ 4p²`: the stop test sends the level to the leaf part. -/
theorem body_stop (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym)
    (ρ : List (BP I)) (hblk : Sym.mark ∉ blk) (hK0 : K ≠ 0) (hstop : 2 ^ K ≤ 4 * p * p) :
    HT ρ (LS S (Lc + 1) p K pIn blk tr) (lvBody I)
      (FS S (blk.reverse ++ (leafSegC pIn p K ++ tr)))
      (2 * C + 2 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + leafCostL C p K pIn (Lc + 1) blk + 1)))) := by
  have h0 := LS_y S (Lc + 1) p K pIn blk tr y0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1 := LS_y S (Lc + 1) p K pIn blk tr y1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hT := stopTest_spec hI p K (LS S (Lc + 1) p K pIn blk tr) ρ
    ⟨_, termOK_mark _, LS_vp S (Lc + 1) p K pIn blk tr⟩
    ⟨_, termOK_mark _, LS_vK S (Lc + 1) p K pIn blk tr⟩ h0 h1
    (LS_y S (Lc + 1) p K pIn blk tr y2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (LS_y S (Lc + 1) p K pIn blk tr y3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
  have hD := dropTest_spec hI (2 ^ K) (4 * p * p) (LS S (Lc + 1) p K pIn blk tr) ρ h0 h1
  have hL := leafPart_LS hI S (Lc + 1) p K pIn blk tr ρ hblk
  have htrue : decide (Lib.ordOf (2 ^ K) (4 * p * p) ≠ Ordering.gt) = true :=
    decide_eq_true ((ordOf_ne_gt_iff _ _).mpr hstop)
  have hC := HT.bcmIte hI y0 y1 (by decide) _ (FS S (blk.reverse ++ (leafSegC pIn p K ++ tr)))
    (2 ^ K) (4 * p * p) _ _ h0 h1
    (by rw [Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_self]) (fun o => decide (o ≠ Ordering.gt))
    ((dropTest I).seq (leafPart I)) ((dropTest I).seq ((stepPart I).seq (.recur 0))) ρ
    (T₁ := C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) +
      leafCostL C p K pIn (Lc + 1) blk)
    (T₂ := C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) +
      leafCostL C p K pIn (Lc + 1) blk)
    (fun _ => HT.seq hD hL) (fun h => by simp [htrue] at h)
  unfold lvBody
  refine (HT.bizIte hI vL _ _ (Lc + 1) (Sym.mark :: S vL) (termOK_mark _)
    (LS_vL S (Lc + 1) p K pIn blk tr) _ _ ρ
    (T₁ := C + 1 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + leafCostL C p K pIn (Lc + 1) blk + 1)))) (T₂ := C + 1 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + leafCostL C p K pIn (Lc + 1) blk + 1))))
    (fun h => absurd h (Nat.succ_ne_zero Lc)) (fun _ => ?_)).mono (by simp only [max_self]; omega)
  refine (HT.bizIte hI vK _ _ K (Sym.mark :: S vK) (termOK_mark _)
    (LS_vK S (Lc + 1) p K pIn blk tr) _ _ ρ
    (T₁ := stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + leafCostL C p K pIn (Lc + 1) blk + 1))) (T₂ := stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + leafCostL C p K pIn (Lc + 1) blk + 1)))
    (fun h => absurd h hK0) (fun _ => (HT.seq hT hC).mono (by simp only [max_self]; omega))).mono
    (by simp only [max_self]; omega)

/-- `Lc ≠ 0`, `K ≠ 0`, `¬ 2^K ≤ 4p²`: the step part and the recursive call. -/
theorem body_step (hI : I.Spec Mul C) (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) (ρ : List (BP I)) (hK0 : K ≠ 0)
    (hstop : ¬ 2 ^ K ≤ 4 * p * p)
    (hdiv : ∀ u2 < 2 ^ (K - K / 2), 0 < IntMulTM.Contracts.W8.columnDivisor (2 ^ (K - K / 2)) u2
      (c0V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)
      (c1V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2))
    (Bfin : BL → List Sym) (Tc : ℕ)
    (hrec : HT ρ (LS S Lc (pChild p K) (K - K / 2) (2 * pChild p K)
      ((preSegC pIn p K).reverse ++ blk) (postSegC p K ++ tr)) (.recur 0) Bfin Tc) :
    HT ρ (LS S (Lc + 1) p K pIn blk tr) (lvBody I) Bfin
      (2 * C + 2 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + (stepCostE C KM p K pIn (Lc + 1) + Tc) + 1)))) := by
  have h0 := LS_y S (Lc + 1) p K pIn blk tr y0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1 := LS_y S (Lc + 1) p K pIn blk tr y1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hT := stopTest_spec hI p K (LS S (Lc + 1) p K pIn blk tr) ρ
    ⟨_, termOK_mark _, LS_vp S (Lc + 1) p K pIn blk tr⟩
    ⟨_, termOK_mark _, LS_vK S (Lc + 1) p K pIn blk tr⟩ h0 h1
    (LS_y S (Lc + 1) p K pIn blk tr y2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (LS_y S (Lc + 1) p K pIn blk tr y3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
  have hD := dropTest_spec hI (2 ^ K) (4 * p * p) (LS S (Lc + 1) p K pIn blk tr) ρ h0 h1
  have hS := stepPart_spec hI KM hMul S Lc p K pIn blk tr ρ hdiv
  have hfalse : decide (Lib.ordOf (2 ^ K) (4 * p * p) ≠ Ordering.gt) = false :=
    decide_eq_false (fun h => hstop ((ordOf_ne_gt_iff _ _).mp h))
  have hC := HT.bcmIte hI y0 y1 (by decide) _ Bfin (2 ^ K) (4 * p * p) _ _ h0 h1
    (by rw [Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_self]) (fun o => decide (o ≠ Ordering.gt))
    ((dropTest I).seq (leafPart I)) ((dropTest I).seq ((stepPart I).seq (.recur 0))) ρ
    (T₁ := C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) +
      (stepCostE C KM p K pIn (Lc + 1) + Tc))
    (T₂ := C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) +
      (stepCostE C KM p K pIn (Lc + 1) + Tc))
    (fun h => by simp [hfalse] at h) (fun _ => HT.seq hD (HT.seq hS hrec))
  unfold lvBody
  refine (HT.bizIte hI vL _ _ (Lc + 1) (Sym.mark :: S vL) (termOK_mark _)
    (LS_vL S (Lc + 1) p K pIn blk tr) _ _ ρ
    (T₁ := C + 1 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + (stepCostE C KM p K pIn (Lc + 1) + Tc) + 1)))) (T₂ := C + 1 + (stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + (stepCostE C KM p K pIn (Lc + 1) + Tc) + 1))))
    (fun h => absurd h (Nat.succ_ne_zero Lc)) (fun _ => ?_)).mono (by simp only [max_self]; omega)
  refine (HT.bizIte hI vK _ _ K (Sym.mark :: S vK) (termOK_mark _)
    (LS_vK S (Lc + 1) p K pIn blk tr) _ _ ρ
    (T₁ := stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + (stepCostE C KM p K pIn (Lc + 1) + Tc) + 1))) (T₂ := stopTestCost C Mul p K + (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1) + (stepCostE C KM p K pIn (Lc + 1) + Tc) + 1)))
    (fun h => absurd h hK0) (fun _ => (HT.seq hT hC).mono (by simp only [max_self]; omega))).mono
    (by simp only [max_self]; omega)

/-- **The level recursion.** From the level state of a level with fuel `Lc`, `levels` puts the
canonical tape of the remaining levels on `TR` above the staged pre segments. -/
theorem levels_spec (hI : I.Spec Mul C) (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (S : BL → List Sym) (ρ : List (BP I)) :
    ∀ (Lc p K pIn : ℕ) (blk tr : List Sym), 8 ≤ p → Lc ≤ p + K → K ≤ 2 ^ (Lc + 1) →
      pIn ≤ 2 * p → Sym.mark ∉ blk →
      HT ρ (LS S Lc p K pIn blk tr) (levels I) (FS S (blk.reverse ++ (tapeFromC pIn Lc p K ++ tr)))
        (levelSum (stepLvG C KM) (leafLvG C KM) pIn Lc p K + 3 * blk.length + 2) := by
  intro Lc0 p0 K0 pIn0 blk0 tr0 hp0 hLK0 hK0 hpIn0 hblk0
  have key := Triple.fix (ρ := ρ) (b := lvBody I) (X := ℕ × ℕ × ℕ × ℕ × List Sym × List Sym)
    (P := fun x s => (8 ≤ x.2.1 ∧ x.1 ≤ x.2.1 + x.2.2.1 ∧ x.2.2.1 ≤ 2 ^ (x.1 + 1) ∧
        x.2.2.2.1 ≤ 2 * x.2.1 ∧ Sym.mark ∉ x.2.2.2.2.1) ∧
      s.stk = LS S x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (Q := fun x s => s.stk = FS S (x.2.2.2.2.1.reverse ++
      (tapeFromC x.2.2.2.1 x.1 x.2.1 x.2.2.1 ++ x.2.2.2.2.2)))
    (T := fun x => levelSum (stepLvG C KM) (leafLvG C KM) x.2.2.2.1 x.1 x.2.1 x.2.2.1 +
      3 * x.2.2.2.2.1.length)
    (fun x => x.1) ?_ (Lc0, p0, K0, pIn0, blk0, tr0)
  · exact key.pre (fun s hs => ⟨⟨hp0, hLK0, hK0, hpIn0, hblk0⟩, hs⟩)
  rintro ⟨Lc, p, K, pIn, blk, tr⟩ ih
  refine Triple.pure_pre (fun hinv => ?_)
  obtain ⟨hp, hLK, hK, hpIn, hblk⟩ := hinv
  dsimp only at hp hLK hK hpIn hblk ih
  show HT (lvBody I :: ρ) (LS S Lc p K pIn blk tr) (lvBody I)
    (FS S (blk.reverse ++ (tapeFromC pIn Lc p K ++ tr)))
    (levelSum (stepLvG C KM) (leafLvG C KM) pIn Lc p K + 3 * blk.length)
  have h4p : 1 ≤ 4 * p * p :=
    Nat.pos_of_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (by omega)) (by omega))
  rcases Lc with _ | Lc
  · -- the fuel is exhausted: the leaf
    refine (body_leaf0 hI S p K pIn blk tr _ hblk).of_eq rfl ?_
    rw [levelSum_zero, show leafLvG C KM pIn 0 p K = leafLvCost C KM 0 p K pIn from
      if_pos ⟨hpIn, by omega⟩]
    simp only [leafCostL, leafLvCost, leafSegCost]
    split_ifs <;> omega
  · by_cases hKz : K = 0
    · -- `K = 0`: the leaf
      subst hKz
      have h1 : 2 ^ 0 ≤ 4 * p * p := by rw [Nat.pow_zero]; exact h4p
      refine (body_leafK0 hI S Lc p pIn blk tr _ hblk).of_eq
        (by rw [tapeFromC_succ, if_pos h1]) ?_
      rw [levelSum_succ, if_pos h1, show leafLvG C KM pIn (Lc + 1) p 0 =
        leafLvCost C KM (Lc + 1) p 0 pIn from if_pos ⟨hpIn, hLK⟩]
      simp only [leafCostL, leafLvCost, leafSegCost]
      split_ifs <;> omega
    · by_cases hstop : 2 ^ K ≤ 4 * p * p
      · -- the stop test fires: the leaf
        refine (body_stop hI S Lc p K pIn blk tr _ hblk hKz hstop).of_eq
          (by rw [tapeFromC_succ, if_pos hstop]) ?_
        rw [levelSum_succ, if_pos hstop, show leafLvG C KM pIn (Lc + 1) p K =
          leafLvCost C KM (Lc + 1) p K pIn from if_pos ⟨hpIn, hLK⟩]
        have hs := stop_le KM hMul C p K
        simp only [leafCostL, leafLvCost, leafSegCost, if_neg hKz]
        omega
      · -- a step level and the recursive call
        have hc : pChild p K = p + 2 * K + 12 := by unfold pChild pWork; omega
        have hpow : 2 ^ (Lc + 1 + 1) = 2 * 2 ^ (Lc + 1) := by rw [Nat.pow_succ]; ring
        have hrec : HT (lvBody I :: ρ) (LS S Lc (pChild p K) (K - K / 2) (2 * pChild p K)
            ((preSegC pIn p K).reverse ++ blk) (postSegC p K ++ tr)) (.recur 0)
            (FS S (((preSegC pIn p K).reverse ++ blk).reverse ++
              (tapeFromC (2 * pChild p K) Lc (pChild p K) (K - K / 2) ++ (postSegC p K ++ tr))))
            (levelSum (stepLvG C KM) (leafLvG C KM) (2 * pChild p K) Lc (pChild p K) (K - K / 2) +
              3 * ((preSegC pIn p K).reverse ++ blk).length + 2) :=
          (ih (Lc, pChild p K, K - K / 2, 2 * pChild p K, (preSegC pIn p K).reverse ++ blk,
            postSegC p K ++ tr) (Nat.lt_succ_self Lc)).pre (fun s hs =>
              ⟨⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, le_rfl,
                by simp only [List.mem_append, List.mem_reverse, not_or]
                   exact ⟨mark_not_mem_preSegC pIn p K, hblk⟩⟩, hs⟩)
        refine (body_step hI KM hMul S Lc p K pIn blk tr _ hKz hstop
          (fix_colDiv_pos Lc p K hp hK hstop) _ _ hrec).of_eq ?_ ?_
        · rw [tapeFromC_succ, if_neg hstop, List.reverse_append, List.reverse_reverse]
          simp only [List.append_assoc]
        · rw [levelSum_succ, if_neg hstop, show stepLvG C KM pIn p K = stepLvCost C KM p K pIn from
            if_pos hpIn]
          have hs := stop_le KM hMul C p K
          have hm := fix_stepCostE_mono C KM p K pIn (Lc + 1) (p + K) hLK
          simp only [stepLvCost, List.length_append, List.length_reverse]
          omega

end Body

#assert_std_axioms stopTest_closed dropTest_closed levels_closed fix_colDiv_pos fix_stepCostE_mono
  stop_le stopTest_spec dropTest_spec LS_vL LS_vp LS_vK LS_y leafPart_LS body_leaf0 body_leafK0
  body_stop body_step levels_spec

end WP.W7k2
