/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFPass
import SubNLogN.Machine.FFT.DIFMath

/-!
# K4-DIF, the composite (`Machine/FFT/DIFLevel.lean`): stacks, sub-kernel calls, one DIF level

**Scope (honest summary).** Proved (no `sorry`), conditional on the two arithmetic sub-kernels,
which enter only as hypotheses `HSDSpec …` / `CMSpec …` on *given* programs (these are exactly the
`spec` bodies of `HalfSumDiffStmt` and of `CMulTruncStmt` after `MulBigContract`,
`Contracts/Arith.lean`):
* the private stack type `DS` of the kernel and its stack layout `KD Eh Ec`
  (`KLoc (Fin 3) (DS ⊕ (Eh ⊕ Ec))`: the three named stacks, the kernel's own stacks, and the
  sub-kernels' private scratch);
* `runs_hsdCall`, `runs_cmCall`: the embedded sub-kernels (`callInj`) as `Runs` on the big layout;
* `levelBody` and `runs_levelBody`: one DIF level (stage table, split, `HalfSumDiffStmt`,
  `CMulTruncStmt`, record interleave, counter updates) from `levelState s` to `levelState (s+1)`.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Common SubNLogN.Math.Walsh

/-- The kernel's own private stacks. -/
inductive DS
  | T | U | L | X | Y | Z | TH | P | Q | ST | ACC | TT | TMP | TMP2 | RC | RA | HF | HC | HA
  | QC | QA | LC | W1 | W2 | W3 | QS
  deriving DecidableEq

instance : Fintype DS :=
  Fintype.ofList [.T, .U, .L, .X, .Y, .Z, .TH, .P, .Q, .ST, .ACC, .TT, .TMP, .TMP2, .RC, .RA, .HF,
    .HC, .HA, .QC, .QA, .LC, .W1, .W2, .W3, .QS] (by intro x; cases x <;> simp)

/-- The full stack layout: named stacks `0` (data), `1` (header), `2` (table); the kernel's
stacks; the half-sum kernel's scratch; the product kernel's scratch. -/
abbrev KD (Eh Ec : Type) : Type := KLoc (Fin 3) (DS ⊕ (Eh ⊕ Ec))

section Layout

variable {Eh Ec : Type}

/-- A kernel stack. -/
def ds (d : DS) : KD Eh Ec := .inr (.inl d)

/-- The data stack, the header stack, the table stack. -/
def nD : KD Eh Ec := .inl 0
def nH : KD Eh Ec := .inl 1
def nTB : KD Eh Ec := .inl 2

/-- Stacks of the half-sum kernel: `0 ↦ U`, `1 ↦ L`, `2 ↦ X`, `3 ↦ Y`, `4 ↦ W1`. -/
def ιh : KLoc (Fin 5) Eh → KD Eh Ec
  | .inl i => ![ds .U, ds .L, ds .X, ds .Y, ds .W1] i
  | .inr e => .inr (.inr (.inl e))

/-- Stacks of the product kernel: `0 ↦ Y`, `1 ↦ TH`, `2 ↦ Z`, `3 ↦ W1`, `4 ↦ W2`, `5 ↦ W3`,
`6 ↦ QS`. -/
def ιc : KLoc (Fin 7) Ec → KD Eh Ec
  | .inl i => ![ds .Y, ds .TH, ds .Z, ds .W1, ds .W2, ds .W3, ds .QS] i
  | .inr e => .inr (.inr (.inr e))

theorem ιh_injective : Function.Injective (ιh : KLoc (Fin 5) Eh → KD Eh Ec) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιh, ds]
  · fin_cases i <;> simp [ιh, ds] at h
  · fin_cases j <;> simp [ιh, ds] at h
  · simp only [ιh, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιc_injective : Function.Injective (ιc : KLoc (Fin 7) Ec → KD Eh Ec) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιc, ds]
  · fin_cases i <;> simp [ιc, ds] at h
  · fin_cases j <;> simp [ιc, ds] at h
  · simp only [ιc, Sum.inr.injEq] at h
    rw [h]

end Layout

/-! ## The arithmetic sub-kernels as hypotheses on given programs -/

/-- The `spec` body of `HalfSumDiffStmt` (`Contracts/Arith.lean`), for a given program. -/
def HSDSpec (Eh : Type) [DecidableEq Eh] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) R) : Prop :=
  ∀ (w : ℕ) (u v : List (List CInt)) (ru rv r4 : List Sym) (S : KLoc (Fin 5) Eh → List Sym),
    1 ≤ w → CArrFits w u → CArrFits w v → CAligned u v →
    BlkTerm ru → BlkTerm rv → TermOK r4 →
    S (.inl 0) = carrSyms w u ++ ru → S (.inl 1) = carrSyms w v ++ rv →
    S (.inl 4) = natSyms w ++ r4 →
    Runs P S
      (Function.update (Function.update (Function.update (Function.update S (.inl 0) ru)
        (.inl 1) rv) (.inl 2) (carrSyms w (zipC halfSumC u v) ++ S (.inl 2)))
        (.inl 3) (carrSyms w (zipC halfDiffC u v) ++ S (.inl 3)))
      (fun _ => True) (C * (cvol w u + cvol w v + w + 1))

/-- The `spec` body of `CMulTruncStmt` after its `MulBigContract` premise, for a given program. -/
def CMSpec (Ec : Type) [DecidableEq Ec] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 s : ℕ) (z θ : List (List CInt)) (rz rθ r3 r4 r5 r6 : List Sym)
    (S : KLoc (Fin 7) Ec → List Sym),
    KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 θ → CAligned z θ →
    CArrFits w3 (zipC (cmulTruncC s) z θ) →
    BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
    S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 θ ++ rθ →
    S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
    S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
    Runs P S
      (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
        (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2)))
      (fun _ => True)
      (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 θ + cvol w3 z +
        (ncoef z + 1) * (bitLen s + 1) + w1 + w2 + w3))

section Calls

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ Rh Rc : Type}

theorem runs_hsdCall (lh : Lens σ Rh) {Ch : ℕ} {Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh}
    (hP : HSDSpec Eh Rh Ch Ph) (B : KD Eh Ec → List Sym) (w : ℕ) (u v : List (List CInt))
    (hw : 1 ≤ w) (hu : CArrFits w u) (hv : CArrFits w v) (huv : CAligned u v)
    (hU : B (ds .U) = carrSyms w u) (hL : B (ds .L) = carrSyms w v)
    (hW : B (ds .W1) = natSyms w) :
    Runs (callInj ιh lh Ph) B
      (Function.update (Function.update (Function.update (Function.update B (ds .U) [])
        (ds .L) []) (ds .X) (carrSyms w (zipC halfSumC u v) ++ B (ds .X)))
        (ds .Y) (carrSyms w (zipC halfDiffC u v) ++ B (ds .Y)))
      (fun _ => True) (Ch * (cvol w u + cvol w v + w + 1)) := by
  have h := hP w u v [] [] [] (B ∘ ιh) hw hu hv huv (fun _ h => by simp at h)
    (fun _ h => by simp at h) TermOK.nil
    (by simp [ιh, hU]) (by simp [ιh, hL]) (by simp [ιh, hW])
  refine runs_callInj ιh_injective lh (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιh, ds, Function.update_apply]
    · simp [ιh, ds, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ds .U := fun h => hk (.inl 0) (by simp [ιh, h])
    have h2 : k ≠ ds .L := fun h => hk (.inl 1) (by simp [ιh, h])
    have h3 : k ≠ ds .X := fun h => hk (.inl 2) (by simp [ιh, h])
    have h4 : k ≠ ds .Y := fun h => hk (.inl 3) (by simp [ιh, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]

theorem runs_cmCall (lc : Lens σ Rc) {Cc : ℕ} {Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc}
    (hP : CMSpec Ec Rc Cc Pc) (B : KD Eh Ec → List Sym) (w q : ℕ) (z θ : List (List CInt))
    (hclean : ∀ e : Ec, B (.inr (.inr (.inr e))) = []) (hw : 1 ≤ w) (hz : CArrFits w z)
    (hθ : CArrFits w θ) (hzθ : CAligned z θ) (hout : CArrFits w (zipC (cmulTruncC q) z θ))
    (hY : B (ds .Y) = carrSyms w z) (hTH : B (ds .TH) = carrSyms w θ)
    (hW1 : B (ds .W1) = natSyms w) (hW2 : B (ds .W2) = natSyms w) (hW3 : B (ds .W3) = natSyms w)
    (hQS : B (ds .QS) = natSyms q) :
    Runs (callInj ιc lc Pc) B
      (Function.update (Function.update (Function.update B (ds .Y) []) (ds .TH) []) (ds .Z)
        (carrSyms w (zipC (cmulTruncC q) z θ) ++ B (ds .Z)))
      (fun _ => True)
      (Cc * (ncoef z * mulW (w + w + 1) + cvol w z + cvol w θ + cvol w z +
        (ncoef z + 1) * (bitLen q + 1) + w + w + w)) := by
  have h := hP w w w q z θ [] [] [] [] [] [] (B ∘ ιc) (fun e => by simp [ιc, hclean]) hw hw hw
    hz hθ hzθ hout (fun _ h => by simp at h) (fun _ h => by simp at h) TermOK.nil TermOK.nil
    TermOK.nil TermOK.nil
    (by simp [ιc, hY]) (by simp [ιc, hTH]) (by simp [ιc, hW1]) (by simp [ιc, hW2])
    (by simp [ιc, hW3]) (by simp [ιc, hQS])
  refine runs_callInj ιc_injective lc (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιc, ds, Function.update_apply]
    · simp [ιc, ds, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ds .Y := fun h => hk (.inl 0) (by simp [ιc, h])
    have h2 : k ≠ ds .TH := fun h => hk (.inl 1) (by simp [ιc, h])
    have h3 : k ≠ ds .Z := fun h => hk (.inl 2) (by simp [ιc, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

end Calls


/-! ## Layout facts -/

section LayoutFacts

variable {Eh Ec : Type}

@[simp] theorem ds_inj {a b : DS} : (ds a : KD Eh Ec) = ds b ↔ a = b := by simp [ds]
@[simp] theorem ds_ne_nTB (d : DS) : (ds d : KD Eh Ec) ≠ nTB := by simp [ds, nTB]
@[simp] theorem nTB_ne_ds (d : DS) : (nTB : KD Eh Ec) ≠ ds d := by simp [ds, nTB]
@[simp] theorem ds_ne_nD (d : DS) : (ds d : KD Eh Ec) ≠ nD := by simp [ds, nD]
@[simp] theorem nD_ne_ds (d : DS) : (nD : KD Eh Ec) ≠ ds d := by simp [ds, nD]
@[simp] theorem ds_ne_nH (d : DS) : (ds d : KD Eh Ec) ≠ nH := by simp [ds, nH]
@[simp] theorem nH_ne_ds (d : DS) : (nH : KD Eh Ec) ≠ ds d := by simp [ds, nH]
@[simp] theorem nD_ne_nH : (nD : KD Eh Ec) ≠ nH := by simp [nD, nH]
@[simp] theorem nH_ne_nD : (nH : KD Eh Ec) ≠ nD := by simp [nD, nH]
@[simp] theorem nD_ne_nTB : (nD : KD Eh Ec) ≠ nTB := by simp [nD, nTB]
@[simp] theorem nTB_ne_nD : (nTB : KD Eh Ec) ≠ nD := by simp [nD, nTB]
@[simp] theorem nH_ne_nTB : (nH : KD Eh Ec) ≠ nTB := by simp [nH, nTB]
@[simp] theorem nTB_ne_nH : (nTB : KD Eh Ec) ≠ nH := by simp [nH, nTB]

end LayoutFacts

/-! ## Pure facts about record payloads -/

theorem crecBits_append (w : ℕ) (a b : List CInt) :
    crecBits w (a ++ b) = crecBits w a ++ crecBits w b := by
  simp [crecBits, List.flatMap_append]

theorem carrSyms_eq (w : ℕ) (B : List (List CInt)) :
    carrSyms w B = arrSyms (B.map (crecBits w)) := rfl

theorem crecBits_length' (w : ℕ) (cs : List CInt) : (crecBits w cs).length = 2 * w * cs.length :=
  crecBits_length w cs

/-- The interleave commutes with a map. -/
theorem inter_map {α β : Type} (f : α → β) :
    ∀ (as bs : List α), inter (as.map f) (bs.map f) = (inter as bs).map f
  | [], _ => by simp [inter]
  | _ :: _, [] => by simp [inter]
  | a :: as, b :: bs => by simp [inter, inter_map f as bs]

/-- The gathered stage payload is the encoding of `stageB`. -/
theorem stageBits_map (w : ℕ) (tab : List CInt) (k m : ℕ) (hk : k * (m + 1) ≤ tab.length) :
    stageBits (tab.map fun c => crecBits w [c]) k m = crecBits w (stageB tab k (m + 1)) := by
  unfold stageBits stageB crecBits
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  have hj' : j * (m + 1) < tab.length := by
    have := List.mem_range.1 hj
    have : (j + 1) * (m + 1) ≤ k * (m + 1) := Nat.mul_le_mul_right _ this
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by
    rw [Nat.mul_comm]; exact hj')]
  simp [Nat.mul_comm]

/-! ## The level state -/

section Level

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ Rh Rc : Type}

/-- The base state: the counters and widths in place, every other private stack empty. -/
structure BaseOK (S0 : KD Eh Ec → List Sym) (w q : ℕ) (tabP : List (List Bool))
    (trest : List Sym) : Prop where
  tb : S0 nTB = arrSyms tabP ++ trest
  rc : S0 (ds .RC) = List.replicate (2 * w) .mark
  w1 : S0 (ds .W1) = natSyms w
  w2 : S0 (ds .W2) = natSyms w
  w3 : S0 (ds .W3) = natSyms w
  qs : S0 (ds .QS) = natSyms q
  empty : ∀ d : DS, d ≠ .RC → d ≠ .W1 → d ≠ .W2 → d ≠ .W3 → d ≠ .QS → S0 (ds d) = []
  clean : ∀ e : Ec, S0 (.inr (.inr (.inr e))) = []

/-- The state at the start of a level: the reversed blocked array on `T`, the counters. -/
def lvState (S0 : KD Eh Ec → List Sym) (w : ℕ) (B : List (List CInt)) (hc qc s : ℕ) :
    KD Eh Ec → List Sym :=
  upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) (carrSyms w B).reverse (List.replicate hc .mark)
    (List.replicate qc .mark) (List.replicate s .mark)

/-- One DIF level. -/
def levelBody (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc)
    (Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh) (Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc) :
    Prog (KD Eh Ec) (fun _ => Sym) σ :=
  .seq (gather lO nTB (ds .TT) (ds .ACC) (ds .ST) (ds .QC) (ds .QA) (ds .HC) (ds .HA))
  (.seq (split lO (ds .T) (ds .U) (ds .L) (ds .TH) (ds .ST) (ds .TMP) (ds .HC) (ds .HA) (ds .RC)
    (ds .RA))
  (.seq (callInj ιh lh Ph)
  (.seq (callInj ιc lc Pc)
  (.seq (rmerge lO (ds .X) (ds .Z) (ds .T))
  (.seq (drain lO (ds .ST))
  (.seq (halveTo lO (ds .HC) (ds .HA))
  (.seq (movePrefix lO (ds .HA) (ds .HC) Option.isSome)
  (.seq (dbl1 lO (ds .QC) (ds .QA))
  (pushK (ds .LC) .mark)))))))))

theorem closed_levelBody (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc)
    {Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh} {Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc}
    (hPh : Ph.Closed) (hPc : Pc.Closed) : (levelBody lO lh lc Ph Pc).Closed :=
  ⟨closed_gather lO _ _ _ _ _ _ _ _, closed_split lO _ _ _ _ _ _ _ _ _ _,
    closed_callInj ιh lh hPh, closed_callInj ιc lc hPc, closed_rmerge lO _ _ _,
    closed_drain lO _, closed_halveTo lO _ _, closed_movePrefix lO _ _ _, closed_dbl1 lO _ _,
    closed_pushK _ _⟩

/-- The cost of one level (the sum of its steps), in terms of the level's shape. -/
def levelCost (Ch Cc w q N h qc : ℕ) (u v z θ : List (List CInt)) : ℕ :=
  (h * (5 * (2 * w) + qc * (4 * (2 * w) + 8) + 4 * qc + 12 + 2) + 2 + (4 * h + 2) +
    (4 * (h * (qc + 1) * (2 * w + 1)) + 2) + 1 + (4 * (h * (2 * w)) + 2)) +
  (N * (h * (10 * (2 * w) + 8) + 4 * h + 4 * (h * (2 * w)) + 9 * (2 * w * h) + 16) + 2) +
  (Ch * (cvol w u + cvol w v + w + 1)) +
  (Cc * (ncoef z * mulW (w + w + 1) + cvol w z + cvol w θ + cvol w z +
    (ncoef z + 1) * (bitLen q + 1) + w + w + w)) +
  (N * (8 * (2 * w * h) + 10) + 2) + (3 * (2 * w * h + 1) + 2) + (3 * h + 5) +
  (4 * (h / 2) + 2) + (13 * qc + 9) + 1

end Level

/-! ## Shapes of the zipped halves -/

theorem zipC_halves_eq (f : CInt → CInt → CInt) (B : List (List CInt)) (h : ℕ) :
    zipC f (B.map (List.take h)) (B.map (List.drop h)) =
      B.map fun blk => List.zipWith f (blk.take h) (blk.drop h) := by
  induction B with
  | nil => rfl
  | cons blk B ih => simp [zipC] at ih ⊢ <;> exact ih

theorem zipC_halves_shape (f : CInt → CInt → CInt) (B : List (List CInt)) (h : ℕ)
    (hB : ∀ blk ∈ B, blk.length = 2 * h) :
    (zipC f (B.map (List.take h)) (B.map (List.drop h))).length = B.length ∧
      ∀ row ∈ zipC f (B.map (List.take h)) (B.map (List.drop h)), row.length = h := by
  rw [zipC_halves_eq]
  refine ⟨by simp, fun row hrow => ?_⟩
  obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hrow
  simp [hB blk hb] <;> omega

theorem zipC_rep_shape (f : CInt → CInt → CInt) (st : List CInt) :
    ∀ (Y : List (List CInt)) (n : ℕ), Y.length = n → (∀ row ∈ Y, row.length = st.length) →
      CAligned Y (List.replicate n st) ∧ (zipC f Y (List.replicate n st)).length = n ∧
        ∀ row ∈ zipC f Y (List.replicate n st), row.length = st.length
  | [], n, hn, _ => by
    subst hn
    exact ⟨List.Forall₂.nil, rfl, fun _ h => by simp [zipC] at h⟩
  | row :: Y, n, hn, hr => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    have ih := zipC_rep_shape f st Y n' (by simpa using hn)
      (fun r h => hr r (List.mem_cons_of_mem _ h))
    have hrow := hr row List.mem_cons_self
    refine ⟨List.Forall₂.cons hrow ih.1, ?_, ?_⟩
    · simp only [zipC, List.replicate_succ, List.zipWith_cons_cons, List.length_cons] at ih ⊢
      rw [ih.2.1]
    · intro r hr'
      simp only [zipC, List.replicate_succ, List.zipWith_cons_cons, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · simp [hrow]
      · exact ih.2.2 r hr'

section LevelRuns

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ Rh Rc : Type}

set_option maxHeartbeats 4000000 in
/-- **One DIF level** (Theorem 6.5, `thm:direct-fft`, Section 6.4): from the blocked array `B` (`N` blocks
of `2h` coefficients), the stage table `stageB tab h (qc + 1)` is gathered, the blocks are split,
`HalfSumDiffStmt` and `CMulTruncStmt` are applied, the results interleaved: the next level state
holds `levelB q h stage B`, `⌊h/2⌋`, `2·qc + 1`, `s + 1`. The width guards are hypotheses. -/
theorem runs_levelBody (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc)
    {Ch Cc : ℕ} {Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh}
    {Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc} (hHSD : HSDSpec Eh Rh Ch Ph)
    (hCM : CMSpec Ec Rc Cc Pc) (S0 : KD Eh Ec → List Sym) (w q : ℕ) (tab : List CInt)
    (trest : List Sym) (hbase : BaseOK S0 w q (tab.map fun c => crecBits w [c]) trest)
    (hw : 1 ≤ w) (B : List (List CInt)) (N h qc s : ℕ) (hN : B.length = N)
    (hBrow : ∀ blk ∈ B, blk.length = 2 * h) (hk : h * (qc + 1) ≤ tab.length)
    (hfB : CArrFits w B) (hfT : ∀ c ∈ stageB tab h (qc + 1), FitsTwos w c.1 ∧ FitsTwos w c.2)
    (hfY : CArrFits w (zipC halfDiffC (B.map (List.take h)) (B.map (List.drop h))))
    (hfZ : CArrFits w (zipC (cmulTruncC q) (zipC halfDiffC (B.map (List.take h))
      (B.map (List.drop h))) (List.replicate N (stageB tab h (qc + 1))))) :
    Runs (levelBody lO lh lc Ph Pc) (lvState S0 w B h qc s)
      (lvState S0 w (levelB q h (stageB tab h (qc + 1)) B) (h / 2) (2 * qc + 1) (s + 1))
      (fun _ => True)
      (levelCost Ch Cc w q N h qc (B.map (List.take h)) (B.map (List.drop h))
        (zipC halfDiffC (B.map (List.take h)) (B.map (List.drop h)))
        (List.replicate N (stageB tab h (qc + 1)))) := by
  -- names and base facts
  set stage := stageB tab h (qc + 1) with hstage
  set ups := B.map (List.take h) with hups
  set lows := B.map (List.drop h) with hlows
  set tabP := tab.map fun c => crecBits w [c] with htabP
  have e0 : ∀ d : DS, d ≠ .RC → d ≠ .W1 → d ≠ .W2 → d ≠ .W3 → d ≠ .QS → S0 (ds d) = [] :=
    hbase.empty
  have eU := e0 .U (by decide) (by decide) (by decide) (by decide) (by decide)
  have eL := e0 .L (by decide) (by decide) (by decide) (by decide) (by decide)
  have eX := e0 .X (by decide) (by decide) (by decide) (by decide) (by decide)
  have eY := e0 .Y (by decide) (by decide) (by decide) (by decide) (by decide)
  have eZ := e0 .Z (by decide) (by decide) (by decide) (by decide) (by decide)
  have eTH := e0 .TH (by decide) (by decide) (by decide) (by decide) (by decide)
  have eST := e0 .ST (by decide) (by decide) (by decide) (by decide) (by decide)
  have eACC := e0 .ACC (by decide) (by decide) (by decide) (by decide) (by decide)
  have eTT := e0 .TT (by decide) (by decide) (by decide) (by decide) (by decide)
  have eTMP := e0 .TMP (by decide) (by decide) (by decide) (by decide) (by decide)
  have eRA := e0 .RA (by decide) (by decide) (by decide) (by decide) (by decide)
  have eHA := e0 .HA (by decide) (by decide) (by decide) (by decide) (by decide)
  have eQA := e0 .QA (by decide) (by decide) (by decide) (by decide) (by decide)
  have htabl : ∀ p ∈ tabP, p.length = 2 * w := by
    intro p hp
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
    simp [crecBits_length']
  have hstg : stageBits tabP h qc = crecBits w stage := stageBits_map w tab h qc hk
  set LS := lvState S0 w B h qc s with hLS
  -- 1. gather the stage table
  have e1 := runs_gather lO (TB := nTB) (TT := ds .TT) (ACC := ds .ACC) (ST := ds .ST)
    (QC := ds .QC) (QA := ds .QA) (H := ds .HC) (HA := ds .HA) (by simp [ds, nTB]) LS tabP trest (2 * w) h
    qc htabl (by simpa [htabP] using hk)
    (by simp [hLS, lvState, upd4, Function.update_apply, hbase.tb])
    (by simp [hLS, lvState, upd4, Function.update_apply, eTT])
    (by simp [hLS, lvState, upd4, Function.update_apply, eACC])
    (by simp [hLS, lvState, upd4, Function.update_apply])
    (by simp [hLS, lvState, upd4, Function.update_apply, eHA])
    (by simp [hLS, lvState, upd4, Function.update_apply])
    (by simp [hLS, lvState, upd4, Function.update_apply, eQA])
  have hLSST : LS (ds .ST) = [] := by simp [hLS, lvState, upd4, Function.update_apply, eST]
  rw [hLSST, List.append_nil, hstg] at e1
  set S1 := Function.update LS (ds .ST) (recSyms (crecBits w stage)) with hS1
  -- 2. split the blocks into halves
  set ps := B.map fun blk => (crecBits w (blk.take h), crecBits w (blk.drop h)) with hps
  have hpsj : ps.map (fun p => p.1 ++ p.2) = B.map (crecBits w) := by
    simp only [hps, List.map_map]
    apply List.map_congr_left
    intro blk _
    simp [← crecBits_append]
  have e2 := runs_split lO (T := ds .T) (U := ds .U) (L := ds .L) (TH := ds .TH) (ST := ds .ST)
    (TMP := ds .TMP) (H := ds .HC) (HA := ds .HA) (R := ds .RC) (A := ds .RA) (by simp [ds]) S1 ps
    (crecBits w stage) (2 * w) h
    (by
      intro p hp
      obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hp
      rw [crecBits_length', List.length_take, hBrow blk hb, Nat.min_eq_left (by omega)]
      ring)
    (by
      intro p hp
      obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hp
      rw [crecBits_length', List.length_drop, hBrow blk hb, show 2 * h - h = h by omega]
      ring)
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply, hpsj, carrSyms_eq])
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply])
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply, eHA])
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply, hbase.rc])
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply, eRA])
    (by simp [hS1])
    (by simp [hS1, hLS, lvState, upd4, Function.update_apply, eTMP])
  have hS1U : S1 (ds .U) = [] := by simp [hS1, hLS, lvState, upd4, Function.update_apply, eU]
  have hS1L : S1 (ds .L) = [] := by simp [hS1, hLS, lvState, upd4, Function.update_apply, eL]
  have hS1TH : S1 (ds .TH) = [] := by simp [hS1, hLS, lvState, upd4, Function.update_apply, eTH]
  have hpsf : arrSyms (ps.map Prod.fst) = carrSyms w ups := by
    simp [hps, hups, carrSyms_eq, List.map_map, Function.comp_def]
  have hpss : arrSyms (ps.map Prod.snd) = carrSyms w lows := by
    simp [hps, hlows, carrSyms_eq, List.map_map, Function.comp_def]
  have hpsl : ps.length = N := by simp [hps, hN]
  have hrepst : arrSyms (List.replicate ps.length (crecBits w stage)) =
      carrSyms w (List.replicate N stage) := by
    simp [carrSyms_eq, hpsl, List.map_replicate]
  rw [hS1U, hS1L, hS1TH, List.append_nil, List.append_nil, List.append_nil, hpsf, hpss,
    hrepst] at e2
  set S2 := upd4 S1 (ds .T) (ds .U) (ds .L) (ds .TH) [] (carrSyms w ups) (carrSyms w lows)
    (carrSyms w (List.replicate N stage)) with hS2
  -- 3. half-sums and half-differences
  have hfu : CArrFits w ups := by
    intro cs hcs c hc
    obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hcs
    exact hfB blk hb c (List.mem_of_mem_take hc)
  have hfl : CArrFits w lows := by
    intro cs hcs c hc
    obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hcs
    exact hfB blk hb c (List.mem_of_mem_drop hc)
  have hal : CAligned ups lows := by
    simp only [hups, hlows, CAligned]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro blk hb
    simp [hBrow blk hb]
    omega
  have e3 := runs_hsdCall lh hHSD S2 w ups lows hw hfu hfl hal
    (by simp [hS2, upd4, Function.update_apply])
    (by simp [hS2, upd4, Function.update_apply])
    (by simp [hS2, hS1, hLS, lvState, upd4, Function.update_apply, hbase.w1])
  have hS2X : S2 (ds .X) = [] := by simp [hS2, hS1, hLS, lvState, upd4, Function.update_apply, eX]
  have hS2Y : S2 (ds .Y) = [] := by simp [hS2, hS1, hLS, lvState, upd4, Function.update_apply, eY]
  rw [hS2X, hS2Y, List.append_nil, List.append_nil] at e3
  set S3 := Function.update (Function.update (Function.update (Function.update S2 (ds .U) [])
    (ds .L) []) (ds .X) (carrSyms w (zipC halfSumC ups lows))) (ds .Y)
    (carrSyms w (zipC halfDiffC ups lows)) with hS3
  -- 4. differences times the stage table
  have hfst : CArrFits w (List.replicate N stage) := by
    intro cs hcs c hc
    rw [List.eq_of_mem_replicate hcs] at hc
    exact hfT c hc
  have hYsh := zipC_halves_shape halfDiffC B h hBrow
  have hXsh := zipC_halves_shape halfSumC B h hBrow
  have hstlen : stage.length = h := by simp [hstage, stageB]
  have hZsh := zipC_rep_shape (cmulTruncC q) stage (zipC halfDiffC ups lows) N
    (by rw [hYsh.1, hN]) (fun row hr => by rw [hYsh.2 row hr, hstlen])
  have halz : CAligned (zipC halfDiffC ups lows) (List.replicate N stage) := hZsh.1
  have e4 := runs_cmCall lc hCM S3 w q (zipC halfDiffC ups lows) (List.replicate N stage)
    (fun e => by simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, ds,
      hbase.clean e]) hw hfY hfst halz hfZ
    (by simp [hS3])
    (by simp [hS3, hS2, upd4, Function.update_apply])
    (by simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, hbase.w1])
    (by simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, hbase.w2])
    (by simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, hbase.w3])
    (by simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, hbase.qs])
  have hS3Z : S3 (ds .Z) = [] := by
    simp [hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, eZ]
  rw [hS3Z, List.append_nil] at e4
  set S4 := Function.update (Function.update (Function.update S3 (ds .Y) []) (ds .TH) []) (ds .Z)
    (carrSyms w (zipC (cmulTruncC q) (zipC halfDiffC ups lows) (List.replicate N stage)))
    with hS4
  -- 5. interleave the two result arrays onto `T`
  have e5 := runs_rmerge lO (X := ds .X) (Z := ds .Z) (T := ds .T) (by simp) (by simp)
    (by simp) S4 ((zipC halfSumC ups lows).map (crecBits w))
    ((zipC (cmulTruncC q) (zipC halfDiffC ups lows) (List.replicate N stage)).map (crecBits w))
    (2 * w * h) (by simp only [List.length_map]; rw [hXsh.1, hZsh.2.1, hN])
    (by
      intro p hp
      obtain ⟨row, hr, rfl⟩ := List.mem_map.1 hp
      rw [crecBits_length', hXsh.2 row hr])
    (by
      intro p hp
      obtain ⟨row, hr, rfl⟩ := List.mem_map.1 hp
      rw [crecBits_length', hZsh.2.2 row hr, hstlen])
    (by simp [hS4, hS3, carrSyms_eq]) (by simp [hS4, carrSyms_eq])
  have hS4T : S4 (ds .T) = [] := by simp [hS4, hS3, hS2, upd4, Function.update_apply]
  have hlev : arrSyms ((inter (zipC halfSumC ups lows) (zipC (cmulTruncC q)
      (zipC halfDiffC ups lows) (List.replicate N stage))).map (crecBits w)) =
      carrSyms w (levelB q h stage B) := by
    rw [carrSyms_eq, levelB, ← hups, ← hlows, hN]
  rw [hS4T, List.append_nil, inter_map, hlev] at e5
  set S5 := Function.update (Function.update (Function.update S4 (ds .X) []) (ds .Z) []) (ds .T)
    (carrSyms w (levelB q h stage B)).reverse with hS5
  -- 6. clear the stage table
  have e6 := runs_drain lO (ds .ST) S5
  have hS5ST : S5 (ds .ST) = recSyms (crecBits w stage) := by
    simp [hS5, hS4, hS3, hS2, hS1, upd4, Function.update_apply]
  rw [hS5ST] at e6
  set S6 := Function.update S5 (ds .ST) [] with hS6
  -- 7-8. halve the half-size counter
  have e7 := runs_halveTo lO (src := ds .HC) (dst := ds .HA) (by simp) S6 h
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply])
  have hS6HA : S6 (ds .HA) = [] := by
    simp [hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply, eHA]
  rw [hS6HA, List.append_nil] at e7
  set S7 := Function.update (Function.update S6 (ds .HC) []) (ds .HA)
    (List.replicate (h / 2) .mark) with hS7
  have e8 := runs_movePrefix lO (src := ds .HA) (dst := ds .HC) (by simp) Option.isSome S7
    (List.replicate (h / 2) .mark) [] (by simp [hS7]) (by simp) rfl
  have hS7HC : S7 (ds .HC) = [] := by simp [hS7]
  rw [hS7HC, List.append_nil, List.reverse_replicate] at e8
  set S8 := Function.update (Function.update S7 (ds .HA) []) (ds .HC)
    (List.replicate (h / 2) .mark) with hS8
  -- 9. the stride counter
  have e9 := runs_dbl1 lO (src := ds .QC) (aux := ds .QA) (by simp) S8 qc
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply,
      eQA])
  set S9 := Function.update S8 (ds .QC) (List.replicate (2 * qc + 1) .mark) with hS9
  -- 10. the level counter
  have e10 := runs_pushK (σ := σ) (ds .LC) .mark S9
  have hS9LC : S9 (ds .LC) = List.replicate s .mark := by
    simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4, Function.update_apply]
  rw [hS9LC] at e10
  have hcost : h * (5 * (2 * w) + qc * (4 * (2 * w) + 8) + 4 * qc + 12 + 2) + 2 + (4 * h + 2) +
        (4 * (h * (qc + 1) * (2 * w + 1)) + 2) + 1 + (4 * (h * (2 * w)) + 2) +
      (ps.length * (h * (10 * (2 * w) + 8) + 4 * h + 4 * (h * (2 * w)) +
        9 * (crecBits w stage).length + 16) + 2 +
      (Ch * (cvol w ups + cvol w lows + w + 1) +
      (Cc * (ncoef (zipC halfDiffC ups lows) * mulW (w + w + 1) +
        cvol w (zipC halfDiffC ups lows) + cvol w (List.replicate N stage) +
        cvol w (zipC halfDiffC ups lows) + (ncoef (zipC halfDiffC ups lows) + 1) * (bitLen q + 1) +
        w + w + w) +
      (((zipC halfSumC ups lows).map (crecBits w)).length * (8 * (2 * w * h) + 10) + 2 +
      (3 * (recSyms (crecBits w stage)).length + 2 +
      (3 * h + 5 + (4 * (List.replicate (h / 2) Sym.mark).length + 2 +
      (13 * qc + 9 + 1)))))))) =
      levelCost Ch Cc w q N h qc ups lows (zipC halfDiffC ups lows) (List.replicate N stage) := by
    have hrl : (recSyms (crecBits w stage)).length = 2 * w * h + 1 := by
      simp [recSyms, crecBits_length', hstlen]
    rw [hpsl, crecBits_length', hstlen, List.length_map, hXsh.1, hN, hrl, List.length_replicate]
    unfold levelCost
    ring
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
    (runs_seq' e5 (runs_seq' e6 (runs_seq' e7 (runs_seq' e8 (runs_seq' e9 e10)))))))))
    (fun _ _ => trivial) (le_of_eq hcost)) ?_
  -- the final state is the next level state
  simp only [ds] at eU eL eX eY eZ eTH eST eACC eTT eTMP eRA eHA eQA
  funext x
  rcases x with (i | (d | (e | e)))
  · fin_cases i <;>
      simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4,
        Function.update_apply, nD, nH, nTB, ds]
  · cases d <;>
      simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4,
        Function.update_apply, ds, eU, eL, eX, eY, eZ, eTH, eST, eACC, eTT, eTMP, eRA, eHA, eQA,
        List.replicate_succ]
  · simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4,
      Function.update_apply, ds]
  · simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hLS, lvState, upd4,
      Function.update_apply, ds]

end LevelRuns

end SubNLogN.Machine.FFT.DIF
