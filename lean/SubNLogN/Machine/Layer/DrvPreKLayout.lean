/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreKMath
import SubNLogN.Machine.Calculus.FramePass
import SubNLogN.Machine.Calculus.ParkAll
import WP.W3.Basic

/-!
# Driver pre-phase kernel: layout, states, steps (`Machine/Layer/DrvPreKLayout.lean`)

**Scope (honest summary).** Machine infrastructure for the individual kernel pass
`DrvCKernelStmt` (`Machine/Layer/DrvPreDefs.lean`). Everything is proved.
* `KS`: the kernel's own stacks; `KK Z`: the stack layout (named `Fin 3`, own stacks, the
  sub-kernels' scratch `Z`); `st S a0 pre`: the kernel state (array `a0`; own stack `d` holds `pre d`
  above its guard `mark` and its old content).
* Steps on states, each a `Runs` lemma from `st S a0 pre` to `st S a0' pre'`:
  `runs_copyArr` (FramePass `passC`), `runs_copyCtr` (`Lib.copyBlock`), `runs_incCtr` (`Lib.inc`),
  `runs_pushOne`, `runs_dropCtr` (`WP.W3.dropNum`).
* Embedded sub-kernels (`callInj`): the `spec` bodies `BinSpec` (`CAddStmt`/`CSubStmt`), `TSpec`
  (`TruncShiftStmt`), `RSpec` (`RotIPowStmt`), `DSpec` (`K2DistributeBlkStmt 2`), `MSpec`
  (`K2MergeBlkStmt 2 (Equiv.refl _)`), and the call lemmas `runs_binCall`, `runs_tCall`,
  `runs_rCall`, `runs_distCall`, `runs_mergeCall`.
-/

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

/-! ## Layout and states -/

/-- The kernel's own stacks: the role streams `U`, `V` and their copies `U2`, `V2`; the arrays
`SS = U + V`, `DD = U - V`, `RR = i·DD` and the copies `SS2`, `RR2`; `EE = SS + RR`, `FF = SS - RR`;
the output streams `C0`, `C1`; the copy buffer `TMP`; the counters `w` (twice), `w + 1` (twice),
`w + 2` and `1`. -/
inductive KS
  | U | V | U2 | V2 | SS | DD | RR | SS2 | RR2 | EE | FF | C0 | C1 | TMP
  | Cw | Cw' | Cw1 | Cw1' | Cw2 | Cs
  deriving DecidableEq

instance : Fintype KS where
  elems := {.U, .V, .U2, .V2, .SS, .DD, .RR, .SS2, .RR2, .EE, .FF, .C0, .C1, .TMP, .Cw, .Cw', .Cw1,
    .Cw1', .Cw2, .Cs}
  complete x := by cases x <;> simp

/-- All own stacks, as a list. -/
def KS.all : List KS :=
  [.U, .V, .U2, .V2, .SS, .DD, .RR, .SS2, .RR2, .EE, .FF, .C0, .C1, .TMP, .Cw, .Cw', .Cw1, .Cw1',
    .Cw2, .Cs]

theorem KS.mem_all (d : KS) : d ∈ KS.all := by cases d <;> decide

theorem KS.nodup_all : KS.all.Nodup := by decide

/-- Stacks: named `0` (the array), `1` (the counter `W`), `2` (the counter `w`); the own stacks; the
sub-kernels' scratch `Z`. -/
abbrev KK (Z : Type) : Type := KLoc (Fin 3) (KS ⊕ Z)

/-- An own stack. -/
abbrev ds {Z : Type} (d : KS) : KK Z := .inr (.inl d)

/-- **The kernel state.** The array stack holds `a0`; own stack `d` holds `pre d` above its guard
`mark` and its old content; all other stacks are as in `S`. -/
def st {Z : Type} (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym) : KK Z → List Sym
  | .inl i => if i = 0 then a0 else S (.inl i)
  | .inr (.inl d) => pre d ++ .mark :: S (.inr (.inl d))
  | .inr (.inr z) => S (.inr (.inr z))

section States

variable {Z : Type} (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym)

@[simp] theorem st_inl0 : st S a0 pre (.inl 0) = a0 := rfl
@[simp] theorem st_inl1 : st S a0 pre (.inl 1) = S (.inl 1) := rfl
@[simp] theorem st_inl2 : st S a0 pre (.inl 2) = S (.inl 2) := rfl
@[simp] theorem st_ds (d : KS) : st S a0 pre (ds d) = pre d ++ .mark :: S (ds d) := rfl
@[simp] theorem st_inr (z : Z) : st S a0 pre (.inr (.inr z)) = S (.inr (.inr z)) := rfl

variable [DecidableEq Z]

theorem st_update_pre (d : KS) (x : List Sym) :
    Function.update (st S a0 pre) (ds d) (x ++ .mark :: S (ds d)) =
      st S a0 (Function.update pre d x) := by
  funext k
  rcases k with i | e | z
  · simp [st, Function.update_apply]
  · by_cases h : e = d
    · subst h; simp [st]
    · simp [st, Function.update_apply, h]
  · simp [st, Function.update_apply]

theorem st_update_a0 (y : List Sym) :
    Function.update (st S a0 pre) (.inl 0) y = st S y pre := by
  funext k
  rcases k with i | e | z
  · by_cases h : i = 0
    · subst h; simp [st]
    · simp [st, Function.update_apply, h]
  · simp [st, Function.update_apply]
  · simp [st, Function.update_apply]

end States

/-! ## Guard facts -/

theorem mark_not_mem_carrSyms (k : ℕ) (x : List (List CInt)) : Sym.mark ∉ carrSyms k x := by
  intro h
  simp only [carrSyms, arrSyms, blk, recSyms, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨_, ⟨cs, _, rfl⟩, rfl⟩, h⟩ := h
  simp at h

theorem blkTerm_mark (L : List Sym) : BlkTerm (Sym.mark :: L) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by decide⟩

theorem termOK_mark (L : List Sym) : TermOK (Sym.mark :: L) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

/-! ## Runs helpers -/

section RunsHelpers

variable {K : Type} [DecidableEq K]

theorem runs_lift {σ τ : Type} (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  obtain ⟨v', S''⟩ := s'
  change S'' = S' at hs'
  subst hs'
  exact ⟨⟨l.set v v', S''⟩, t, Eval.liftRegs l e v rfl, ⟨rfl, trivial⟩, ht⟩

theorem runsCongr {σ : Type} {P : Prog K (fun _ => Sym) σ} {S S' S'' : K → List Sym}
    {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (he : S' = S'') : Runs P S S'' Q T := he ▸ h

theorem runsSeq {σ : Type} {P P' : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym}
    {Q1 Q2 : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs P' S2 S3 Q2 T2) :
    Runs (.seq P P') S1 S3 Q2 (T1 + T2) :=
  WP.W9comp.runs_seq h1 h2

theorem runsMono {σ : Type} {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym}
    {Q Q' : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') :
    Runs P S S' Q' T' :=
  WP.W9comp.runs_mono h hQ hT

theorem runs_of_eval' {σ : Type} {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ v, ∃ v' t, Eval [] P ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) : Runs P S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h v
  exact ⟨⟨v', S'⟩, t, e, ⟨rfl, trivial⟩, ht⟩

end RunsHelpers

theorem ones_le_bitLen (n : ℕ) : ones (encodeNat n) ≤ bitLen n := by
  unfold bitLen
  induction (encodeNat n) with
  | nil => simp [ones]
  | cons b l ih => cases b <;> simp [ones] <;> omega

/-! ## Steps on own stacks (register `Option Sym`, lifted through a lens) -/

section Steps

variable {Z : Type} [DecidableEq Z] {σ : Type} (l : Lens σ (Option Sym))
  (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym)

theorem ds_ne {d e : KS} (h : d ≠ e) : (ds d : KK Z) ≠ ds e := fun h' => h (by simpa using h')

theorem st_update_nil (d : KS) :
    Function.update (st S a0 pre) (ds d) (.mark :: S (ds d)) =
      st S a0 (Function.update pre d []) :=
  st_update_pre S a0 pre d []

/-- Copy the array on own stack `src` onto own stack `dst` (FramePass `passC`, buffer `TMP`). -/
def copyArr (src dst : KS) : Prog (KK Z) (fun _ => Sym) σ :=
  (passC .mark (ds src) (ds .TMP) (ds dst)).liftRegs l

theorem runs_copyArr {src dst : KS} (hsd : src ≠ dst) (hsT : src ≠ .TMP) (hdT : dst ≠ .TMP)
    (k : ℕ) (x : List (List CInt)) (hsrc : pre src = carrSyms k x) (hT : pre .TMP = []) :
    Runs (copyArr l src dst) (st S a0 pre)
      (st S a0 (Function.update pre dst (carrSyms k x ++ pre dst))) (fun _ => True)
      (9 * cvol k x + 4) := by
  have h := runs_passC (g := Sym.mark) (ds_ne (Z := Z) hsT) (ds_ne (Ne.symm hdT)) (ds_ne hsd)
    (carrSyms k x) (S (ds src)) (S (ds .TMP)) (mark_not_mem_carrSyms k x) (st S a0 pre)
    (by simp [hsrc]) (by simp [hT])
  refine runs_lift l (runsCongr h ?_)
  rw [st_ds, ← List.append_assoc, st_update_pre]

theorem runs_copyCtr {src : KK Z} {dst : KS} (h1 : src ≠ ds dst) (h2 : src ≠ ds .TMP)
    (h3 : dst ≠ .TMP) (n : ℕ) (r : List Sym) (hr : TermOK r)
    (hsrc : st S a0 pre src = natSyms n ++ r) :
    Runs ((copyBlock src (ds dst) (ds .TMP)).liftRegs l) (st S a0 pre)
      (st S a0 (Function.update pre dst (natSyms n ++ pre dst))) (fun _ => True)
      (7 * bitLen n + 7) := by
  refine runs_lift l (runs_of_eval' fun v => ?_)
  have e := copyBlock_eval h1 h2 (ds_ne h3) [] v (encodeNat n) r (st S a0 pre) hr hsrc
  rw [st_ds, ← List.append_assoc, st_update_pre] at e
  exact ⟨_, _, e, by unfold bitLen; omega⟩

theorem runs_incCtr {d : KS} (hd : d ≠ .TMP) (n : ℕ) (hpre : pre d = natSyms n) :
    Runs ((inc (ds d) (ds .TMP)).liftRegs l) (st S a0 pre)
      (st S a0 (Function.update pre d (natSyms (n + 1)))) (fun _ => True) (6 * bitLen n + 9) := by
  refine runs_lift l (runs_of_eval' fun v => ?_)
  obtain ⟨c, hc, e⟩ := inc_eval (ds_ne hd) [] v (encodeNat n) (.mark :: S (ds d)) (st S a0 pre)
    (termOK_mark _) (by simp [hpre, natSyms])
  rw [← encodeNat_succ, st_update_pre] at e
  exact ⟨_, _, e, by have := ones_le_bitLen n; omega⟩

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by decide

theorem runs_pushOne {d : KS} (hpre : pre d = []) :
    Runs ((pushC (ds d) (.bit true)).liftRegs l) (st S a0 pre)
      (st S a0 (Function.update pre d (natSyms 1))) (fun _ => True) 1 := by
  refine runs_lift l (runs_of_eval' fun v => ⟨v, 1, ?_, le_refl _⟩)
  have e := Eval.push ([] : List (SProg (KK Z))) (ds d) (fun _ => Sym.bit true) v (st S a0 pre)
  have h2 : Sym.bit true :: st S a0 pre (ds d) = natSyms 1 ++ Sym.mark :: S (ds d) := by
    rw [st_ds, hpre, natSyms_one]; rfl
  rw [h2, st_update_pre] at e
  exact e

theorem runs_dropCtr {d : KS} (n : ℕ) (hpre : pre d = natSyms n) :
    Runs ((WP.W3.dropNum (ds d)).liftRegs l) (st S a0 pre) (st S a0 (Function.update pre d []))
      (fun _ => True) (2 * bitLen n + 4) := by
  refine runs_lift l (runs_of_eval' fun v => ?_)
  have e := WP.W3.dropNum_eval (k := ds d) [] v (encodeNat n) (.mark :: S (ds d)) (st S a0 pre)
    (termOK_mark _) (by simp [hpre, natSyms])
  rw [st_update_nil] at e
  exact ⟨_, _, e, by unfold bitLen; omega⟩

end Steps

/-! ## Embedded sub-kernels -/

/-- Embedding of a sub-kernel whose named stacks are own stacks `names i` and whose scratch is
`j e` inside `Z`. -/
def emb {Z E : Type} {n : ℕ} (names : Fin n → KS) (j : E → Z) : KLoc (Fin n) E → KK Z
  | .inl i => ds (names i)
  | .inr e => .inr (.inr (j e))

theorem emb_injective {Z E : Type} {n : ℕ} {names : Fin n → KS} {j : E → Z}
    (hn : Function.Injective names) (hj : Function.Injective j) :
    Function.Injective (emb names j) := by
  rintro (i | e) (i' | e') h <;> simp only [emb, ds, Sum.inr.injEq, Sum.inl.injEq,
    reduceCtorEq] at h
  · rw [hn h]
  · rw [hj h]

theorem runs_embCall {Z E : Type} [DecidableEq Z] [DecidableEq E] {n : ℕ} {names : Fin n → KS}
    {j : E → Z} (hn : Function.Injective names) (hj : Function.Injective j) {σ R : Type}
    (l : Lens σ R) {P : Prog (KLoc (Fin n) E) (fun _ => Sym) R} {S : KK Z → List Sym}
    {a0 : List Sym} {pre pre' : KS → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P ((st S a0 pre) ∘ emb names j) ((st S a0 pre') ∘ emb names j) Q T)
    (hout : ∀ d, (∀ i, names i ≠ d) → pre' d = pre d) :
    Runs (callInj (emb names j) l P) (st S a0 pre) (st S a0 pre') (fun _ => True) T := by
  refine runs_callInj (emb_injective hn hj) l hP ?_
  rintro (i | d | z) hk
  · rfl
  · have h : ∀ i, names i ≠ d := fun i h => hk (.inl i) (by simp [emb, h])
    simp only [st, hout d h]
  · rfl

/-! ## Sub-kernel specifications (the `spec` bodies of the contracts) -/

/-- The `spec` body of `CAddStmt` (`f = caddC`) and `CSubStmt` (`f = csubC`). -/
def BinSpec (f : CInt → CInt → CInt) (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) E → List Sym),
    1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
    CArrFits w3 (zipC f u v) →
    BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
    S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
    S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
    S (.inl 5) = natSyms w3 ++ r5 →
    Runs P S
      (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
        (carrSyms w3 (zipC f u v) ++ S (.inl 2)))
      (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

/-- The `spec` body of `TruncShiftStmt`. -/
def TSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 5) E) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) E → List Sym),
    1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (truncShiftC s) v) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
    S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (truncShiftC s) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- The `spec` body of `RotIPowStmt` at the parameter `e`. -/
def RSpec (e : ℕ) (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
    1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC e) v) → BlkTerm rest → TermOK r2 →
    S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w v + w + 1))

/-- The `spec` body of `K2DistributeBlkStmt 2`. -/
def DSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 2 ⊕ Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (Rr s : ℕ) (v : List (List Bool)) (rest r1 : List Sym)
    (S : KLoc (Fin 2 ⊕ Fin 2) E → List Sym),
    v.length = Rr * s → BlkTerm rest → TermOK r1 →
    S (.inl (.inl 0)) = arrSyms v ++ rest → S (.inl (.inl 1)) = natSyms s ++ r1 →
    Runs P S (distBlkPost s v rest S) (fun _ => True) (C * (vol v + 1))

/-- The `spec` body of `K2MergeBlkStmt 2 (Equiv.refl _)`. -/
def MSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 2 ⊕ Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (g s : ℕ) (us : Fin 2 → List (List Bool)) (rests : Fin 2 → List Sym) (r1 : List Sym)
    (S : KLoc (Fin 2 ⊕ Fin 2) E → List Sym),
    (∀ w, (us w).length = g * s) → (∀ w, BlkTerm (rests w)) → TermOK r1 →
    (∀ w, S (.inl (.inr w)) = arrSyms (us w) ++ rests w) →
    S (.inl (.inl 1)) = natSyms s ++ r1 →
    Runs P S (mergeBlkPost (Equiv.refl (Fin 2)) g s us rests S) (fun _ => True)
      (C * (((List.finRange 2).map fun w => vol (us w)).sum + 1))

/-! ## Calls of the arithmetic sub-kernels -/

section Calls

variable {Z : Type} [DecidableEq Z] {σ : Type}

theorem runs_binCall {f : CInt → CInt → CInt} {E : Type} [DecidableEq E] {R : Type} {C : ℕ}
    {P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R} (hP : BinSpec f E R C P) {j : E → Z}
    (hj : Function.Injective j) (l : Lens σ R) (names : Fin 6 → KS)
    (hn : Function.Injective names) (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym)
    (w1 w2 w3 : ℕ) (u v : List (List CInt)) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hw3 : 1 ≤ w3)
    (hu : CArrFits w1 u) (hv : CArrFits w2 v) (huv : CAligned u v)
    (hf : CArrFits w3 (zipC f u v))
    (ha : pre (names 0) = carrSyms w1 u) (hb : pre (names 1) = carrSyms w2 v)
    (h3 : pre (names 3) = natSyms w1) (h4 : pre (names 4) = natSyms w2)
    (h5 : pre (names 5) = natSyms w3) :
    Runs (callInj (emb names j) l P) (st S a0 pre)
      (st S a0 (Function.update (Function.update (Function.update pre (names 0) []) (names 1) [])
        (names 2) (carrSyms w3 (zipC f u v) ++ pre (names 2))))
      (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1)) := by
  refine runs_embCall (Q := fun _ => True) hn hj l ?_ ?_
  · have h := hP w1 w2 w3 u v (.mark :: S (ds (names 0))) (.mark :: S (ds (names 1)))
      (.mark :: S (ds (names 3))) (.mark :: S (ds (names 4))) (.mark :: S (ds (names 5)))
      ((st S a0 pre) ∘ emb names j) hw1 hw2 hw3 hu hv huv hf (blkTerm_mark _) (blkTerm_mark _)
      (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp [emb, ha]) (by simp [emb, hb]) (by simp [emb, h3]) (by simp [emb, h4])
      (by simp [emb, h5])
    refine runsCongr h ?_
    funext x
    rcases x with i | e
    · fin_cases i <;> simp [emb, Function.update_apply, hn.eq_iff]
    · simp [emb, Function.update_apply]
  · intro d hd
    simp [Function.update_apply, Ne.symm (hd 0), Ne.symm (hd 1), Ne.symm (hd 2)]

theorem runs_tCall {E : Type} [DecidableEq E] {R : Type} {C : ℕ}
    {P : Prog (KLoc (Fin 5) E) (fun _ => Sym) R} (hP : TSpec E R C P) {j : E → Z}
    (hj : Function.Injective j) (l : Lens σ R) (names : Fin 5 → KS)
    (hn : Function.Injective names) (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym)
    (w1 w2 s : ℕ) (v : List (List CInt)) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hv : CArrFits w1 v) (hf : CArrFits w2 (mapC (truncShiftC s) v))
    (ha : pre (names 0) = carrSyms w1 v) (h2 : pre (names 2) = natSyms w1)
    (h3 : pre (names 3) = natSyms w2) (h4 : pre (names 4) = natSyms s) :
    Runs (callInj (emb names j) l P) (st S a0 pre)
      (st S a0 (Function.update (Function.update pre (names 0) [])
        (names 1) (carrSyms w2 (mapC (truncShiftC s) v) ++ pre (names 1))))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1)) := by
  refine runs_embCall (Q := fun _ => True) hn hj l ?_ ?_
  · have h := hP w1 w2 s v (.mark :: S (ds (names 0))) (.mark :: S (ds (names 2)))
      (.mark :: S (ds (names 3))) (.mark :: S (ds (names 4)))
      ((st S a0 pre) ∘ emb names j) hw1 hw2 hv hf (blkTerm_mark _)
      (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp [emb, ha]) (by simp [emb, h2]) (by simp [emb, h3]) (by simp [emb, h4])
    refine runsCongr h ?_
    funext x
    rcases x with i | e
    · fin_cases i <;> simp [emb, Function.update_apply, hn.eq_iff]
    · simp [emb, Function.update_apply]
  · intro d hd
    simp [Function.update_apply, Ne.symm (hd 0), Ne.symm (hd 1)]

theorem runs_rCall {e : ℕ} {E : Type} [DecidableEq E] {R : Type} {C : ℕ}
    {P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R} (hP : RSpec e E R C P) {j : E → Z}
    (hj : Function.Injective j) (l : Lens σ R) (names : Fin 3 → KS)
    (hn : Function.Injective names) (S : KK Z → List Sym) (a0 : List Sym) (pre : KS → List Sym)
    (w : ℕ) (v : List (List CInt)) (hw : 1 ≤ w)
    (hv : CArrFits w v) (hf : CArrFits w (mapC (rotIPowC e) v))
    (ha : pre (names 0) = carrSyms w v) (h2 : pre (names 2) = natSyms w) :
    Runs (callInj (emb names j) l P) (st S a0 pre)
      (st S a0 (Function.update (Function.update pre (names 0) [])
        (names 1) (carrSyms w (mapC (rotIPowC e) v) ++ pre (names 1))))
      (fun _ => True) (C * (cvol w v + w + 1)) := by
  refine runs_embCall (Q := fun _ => True) hn hj l ?_ ?_
  · have h := hP w v (.mark :: S (ds (names 0))) (.mark :: S (ds (names 2)))
      ((st S a0 pre) ∘ emb names j) hw hv hf (blkTerm_mark _) (termOK_mark _)
      (by simp [emb, ha]) (by simp [emb, h2])
    refine runsCongr h ?_
    funext x
    rcases x with i | e
    · fin_cases i <;> simp [emb, Function.update_apply, hn.eq_iff]
    · simp [emb, Function.update_apply]
  · intro d hd
    simp [Function.update_apply, Ne.symm (hd 0), Ne.symm (hd 1)]

/-! ## Calls of the distribution and the merge -/

/-- Embedding of `K2DistributeBlk 2` / `K2MergeBlk 2`: named `0`, `1` to the array and the counter
`W`, role stacks to own stacks `r0`, `r1`. -/
def embR {E : Type} (r0 r1 : KS) (j : E → Z) : KLoc (Fin 2 ⊕ Fin 2) E → KK Z
  | .inl (.inl i) => .inl (Fin.castSucc i)
  | .inl (.inr r) => ds (if r = 0 then r0 else r1)
  | .inr e => .inr (.inr (j e))

theorem embR_injective {E : Type} {r0 r1 : KS} {j : E → Z} (h01 : r0 ≠ r1)
    (hj : Function.Injective j) : Function.Injective (embR r0 r1 j) := by
  rintro ((i | r) | e) ((i' | r') | e') h <;>
    simp only [embR, ds, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h
  · rw [Fin.castSucc_inj.1 h]
  · fin_cases r <;> fin_cases r' <;> simp_all
  · rw [hj h]

theorem embR_out {E : Type} {r0 r1 : KS} {j : E → Z} (S S' : KK Z → List Sym)
    (h2 : S' (.inl 2) = S (.inl 2)) (hd : ∀ d, d ≠ r0 → d ≠ r1 → S' (ds d) = S (ds d))
    (hz : ∀ z, S' (.inr (.inr z)) = S (.inr (.inr z))) :
    ∀ k, (∀ x, embR r0 r1 j x ≠ k) → S' k = S k := by
  rintro (i | d | z) hk
  · fin_cases i
    · exact absurd rfl (hk (.inl (.inl 0)))
    · exact absurd rfl (hk (.inl (.inl 1)))
    · exact h2
  · refine hd d (fun h => hk (.inl (.inr 0)) (by simp [embR, h])) (fun h => hk (.inl (.inr 1))
      (by simp [embR, h]))
  · exact hz z

theorem runs_distCall {E : Type} [DecidableEq E] {R : Type} {C : ℕ}
    {P : Prog (KLoc (Fin 2 ⊕ Fin 2) E) (fun _ => Sym) R} (hP : DSpec E R C P) {j : E → Z}
    (hj : Function.Injective j) (l : Lens σ R) (S : KK Z → List Sym) (pre : KS → List Sym)
    (W w : ℕ) (blks : List (List (List CInt))) (rest r1 : List Sym)
    (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (hrest : BlkTerm rest) (hr1 : TermOK r1)
    (hW : S (.inl 1) = natSyms W ++ r1) (hU : pre .U = []) (hV : pre .V = []) :
    Runs (callInj (embR .U .V j) l P) (st S (carrSyms w blks.flatten ++ rest) pre)
      (st S rest (Function.update (Function.update pre .U (carrSyms w (halvesU W blks))) .V
        (carrSyms w (halvesV W blks))))
      (fun _ => True) (C * (cvol w blks.flatten + 1)) := by
  have hd := dist_halves hblk (crecBits w)
  have h := hP (2 * blks.length) W (blks.flatten.map (crecBits w)) rest r1
    ((st S (carrSyms w blks.flatten ++ rest) pre) ∘ embR .U .V j)
    (length_flatten_map hblk _) hrest hr1 (by simp [embR, carrSyms]) (by simp [embR, hW])
  rw [List.map_flatten] at hd
  refine runs_callInj (embR_injective (by decide) hj) l (runsCongr h ?_)
    (embR_out _ _ rfl (fun d h0 h1 => by simp [Function.update_apply, h0, h1]) (fun _ => rfl))
  funext x
  rcases x with ((i | r) | e)
  · fin_cases i <;> simp [distBlkPost, embR]
  · fin_cases r
    · simp [distBlkPost, embR, hU, hd.1, carrSyms]
    · simp [distBlkPost, embR, hV, hd.2, carrSyms]
  · simp [distBlkPost, embR]

theorem runs_mergeCall {E : Type} [DecidableEq E] {R : Type} {C : ℕ}
    {P : Prog (KLoc (Fin 2 ⊕ Fin 2) E) (fun _ => Sym) R} (hP : MSpec E R C P) {j : E → Z}
    (hj : Function.Injective j) (l : Lens σ R) (S : KK Z → List Sym) (a0 : List Sym)
    (pre : KS → List Sym) (W w : ℕ) (blks : List (List (List CInt))) (r1 : List Sym)
    (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (hr1 : TermOK r1)
    (hW : S (.inl 1) = natSyms W ++ r1)
    (h0 : pre .C0 = carrSyms w (zipC cgate0 (halvesU W blks) (halvesV W blks)))
    (h1 : pre .C1 = carrSyms w (zipC cgate1 (halvesU W blks) (halvesV W blks))) :
    Runs (callInj (embR .C0 .C1 j) l P) (st S a0 pre)
      (st S (carrSyms w (blks.map (cgateBlock W)).flatten ++ a0)
        (Function.update (Function.update pre .C0 []) .C1 []))
      (fun _ => True)
      (C * (cvol w (zipC cgate0 (halvesU W blks) (halvesV W blks)) +
        cvol w (zipC cgate1 (halvesU W blks) (halvesV W blks)) + 1)) := by
  have hm := merge_out hblk (crecBits w)
  rw [Equiv.coe_refl] at hm
  have h := hP blks.length W
    ![(zipC cgate0 (halvesU W blks) (halvesV W blks)).map (crecBits w),
      (zipC cgate1 (halvesU W blks) (halvesV W blks)).map (crecBits w)]
    ![.mark :: S (ds .C0), .mark :: S (ds .C1)] r1 ((st S a0 pre) ∘ embR .C0 .C1 j)
    (fun r => by fin_cases r <;> simp [length_zip0 hblk, length_zip1 hblk])
    (fun r => by fin_cases r <;> exact blkTerm_mark _) hr1
    (fun r => by fin_cases r <;> simp [embR, h0, h1, carrSyms]) (by simp [embR, hW])
  have hc : ((List.finRange 2).map fun r => vol
      (![(zipC cgate0 (halvesU W blks) (halvesV W blks)).map (crecBits w),
        (zipC cgate1 (halvesU W blks) (halvesV W blks)).map (crecBits w)] r)).sum =
      cvol w (zipC cgate0 (halvesU W blks) (halvesV W blks)) +
        cvol w (zipC cgate1 (halvesU W blks) (halvesV W blks)) := by
    simp [List.finRange_succ, vol, cvol, carrSyms]
  rw [hc] at h
  refine runs_callInj (embR_injective (by decide) hj) l (runsCongr h ?_)
    (embR_out _ _ rfl (fun d h0 h1 => by simp [Function.update_apply, h0, h1]) (fun _ => rfl))
  funext x
  rcases x with ((i | r) | e)
  · fin_cases i
    · simp [mergeBlkPost, embR, hm, carrSyms]
    · simp [mergeBlkPost, embR]
  · fin_cases r <;> simp [mergeBlkPost, embR]
  · simp [mergeBlkPost, embR]

end Calls

end SubNLogN.Machine.Layer.DrvPreK
