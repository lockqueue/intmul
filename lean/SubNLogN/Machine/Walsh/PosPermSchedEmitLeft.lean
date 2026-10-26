/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitLeftDefs

/-!
# Schedule compiler emitter, the leftover pass: proof (`PosPermSchedEmitLeft.lean`)

`leftPass_holds : LeftPassStmt`: the program `lLoop IT stA` (`PosPermSchedEmitLeftDefs.lean`) pushes
the single flips of the stage's pairs with target `≥ JK`, in increasing position order, onto the
accumulator (`ACC` gains `(schedSyms L).reverse`), and leaves every register and every other stack
as it found them.

Proof: one position `X` (`runs_lBody`) looks up `Y = I X`; if `X < Y` it sets the stage pair
`(c, t)` (`lcv`, `ltv`), tests `t < JK`, and otherwise emits `tag 1, t, c, 1, sep2` (the accumulator
gains `(cmdSyms (.one c t)).reverse`, `one_acc`). The counted loop (`runs_loopR`) runs the positions
`0, …, m-1` with the invariant `ACC = (schedSyms ((prePairs Q i).map one)).reverse ++ acc`
(`prePairs_map_succ`, `schedSyms_append_reverse`). Helpers live in `…PosPermSchedAux.Emit.LeftT1`.

**Scope (honest summary).** Proves the frozen contract `LeftPassStmt`; adds no new contract.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

namespace LeftT1

/-! ## Values and register maps -/

/-- The control of the stage pair at `(X, Y = I X)`: `Y` (stage A) or `X` (stage B). -/
def lcv (stA : Bool) (X Y : ℕ) : ℕ := if stA then Y else X

/-- The target of the stage pair at `(X, Y = I X)`: `X` (stage A) or `Y` (stage B). -/
def ltv (stA : Bool) (X Y : ℕ) : ℕ := if stA then X else Y

/-- The registers at position `X` with loop counter `L` (the other pass registers cleared). -/
def lb (v : RegN → ℕ) (X L : ℕ) : RegN → ℕ :=
  Function.update (Function.update (lz v) .xu X) .len L

/-- The registers at a leftover candidate: `lb v X L` with `y = Y` and `f = 1`. -/
def lp (v : RegN → ℕ) (X L Y : ℕ) : RegN → ℕ :=
  Function.update (Function.update (lb v X L) .y Y) .f 1

/-- The accumulator after emitting the single flip `(c, t)` on top of `A`. -/
def oneAcc (c t : ℕ) (A : List Sym) : List Sym :=
  Sym.sep2 :: (natSyms 1 ++ Sym.mark :: (natSyms c ++ Sym.mark :: (natSyms t ++ Sym.mark ::
    Sym.tag 1 :: A)))

theorem fvLength {m : ℕ} (I : Fin m → Fin m) : (finVals I).length = m := by
  simp [finVals]

/-! ## Blocks -/

section Blocks

variable (S₀ : Stk → List Sym) {V : ℕ}

/-- `lookR IT .xu .y` at position `X` (with `y = 0`): `y := I X`. -/
theorem runs_lookI (IT : RawN) (hIT : IT = .I0T ∨ IT = .I1T) {m : ℕ} (I : Fin m → Fin m)
    (u : RegN → ℕ) (A : List Sym) (X : ℕ) (hX : X < m) (Y : ℕ) (hY : (I ⟨X, hX⟩ : ℕ) = Y)
    (hT : S₀ (rs IT) = utab (finVals I)) (hU : S₀ (rs .U) = []) (hxu : u .xu = X)
    (hy : u .y = 0) (hXV : X ≤ V) (hL : (utab (finVals I)).length ≤ V) :
    Runs (lookR IT .xu .y) (st S₀ u A []) (st S₀ (Function.update u .y Y) A [])
      (fun _ => True) (opW V) := by
  subst hxu hY
  have hj : u .xu < (finVals I).length := by rw [fvLength]; exact hX
  have h := runs_lookR0 S₀ u A [] IT hIT .xu .y (finVals I) hT hU hj hXV hL hy
  have he : (finVals I)[u .xu]'hj = (I ⟨u .xu, hX⟩ : ℕ) := by simp [finVals]
  rw [he] at h
  exact h

/-- `ctSet stA .xu` (with `c = t = 0`): the stage pair of `(X, Y)`. -/
theorem runs_ctSet_xu (stA : Bool) (u : RegN → ℕ) (A : List Sym) (X Y : ℕ) (hx : u .xu = X)
    (hy : u .y = Y) (hc : u .c = 0) (ht : u .t = 0) (hX : X ≤ V) (hY : Y ≤ V) :
    Runs (ctSet stA .xu) (st S₀ u A [])
      (st S₀ (Function.update (Function.update u .c (lcv stA X Y)) .t (ltv stA X Y)) A [])
      (fun _ => True) (2 * opW V) := by
  subst hx hy
  cases stA with
  | true =>
    exact runs_weak (runs_seq' (runs_copyR0 S₀ u A [] .y .c hY hc)
      (runs_copyR0 S₀ (Function.update u .c (u .y)) A [] .xu .t hX ht) le_rfl) rfl (by omega)
  | false =>
    exact runs_weak (runs_seq' (runs_copyR0 S₀ u A [] .xu .c hX hc)
      (runs_copyR0 S₀ (Function.update u .c (u .xu)) A [] .y .t hY ht) le_rfl) rfl (by omega)

/-- `emitOne` (with `b = 0`): the accumulator gains `oneAcc c t` for the values `c`, `t` of the
registers `c`, `t`; the registers end as they started. -/
theorem runs_emitOne (hB1 : S₀ (rs .B1) = []) (u : RegN → ℕ) (A : List Sym) (hb : u .b = 0)
    (hV1 : 1 ≤ V) (hc : u .c ≤ V) (ht : u .t ≤ V) :
    Runs emitOne (st S₀ u A []) (st S₀ u (oneAcc (u .c) (u .t) A) []) (fun _ => True)
      (8 * opW V) := by
  have hW := one_le_opW V
  have hfin : ∀ k₁ k₂ k₃ k₄ k₅ : ℕ,
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update u .b k₁) .b k₂) .b k₃) .b k₄) .b k₅) .b 0 = u := by
    intro k₁ k₂ k₃ k₄ k₅
    simp only [Function.update_idem]
    exact Function.update_eq_self_iff.mpr hb.symm
  refine runs_weak (runs_seq' (runs_pushA (V := V) S₀ u A [] (Sym.tag 1))
    (runs_seq' (runs_copyR0 S₀ u (Sym.tag 1 :: A) [] .t .b ht hb)
    (runs_seq' (runs_emitA S₀ _ _ [] .b hB1 (by exact ht))
    (runs_seq' (runs_copyR0 S₀ _ _ [] .c .b (by exact hc) (by rfl))
    (runs_seq' (runs_emitA S₀ _ _ [] .b hB1 (by exact hc))
    (runs_seq' (runs_inc (V := V) S₀ _ _ [] .b)
    (runs_seq' (runs_emitA S₀ _ _ [] .b hB1 (by exact hV1))
      (runs_pushA (V := V) S₀ _ _ [] Sym.sep2) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    le_rfl) ?_ (by omega)
  rw [hfin]
  try rfl

end Blocks

section Pair

variable (S₀ : Stk → List Sym) {V : ℕ}

/-- **A leftover candidate** `(X, Y)` (registers `lp v X L Y`): the accumulator gains
`oneAcc cv tv` iff `JK ≤ tv`; the registers end as they started. -/
theorem runs_lPair (hB1 : S₀ (rs .B1) = []) (stA : Bool) (v : RegN → ℕ) (X L Y : ℕ)
    (A : List Sym) (hV1 : 1 ≤ V) (hX : X ≤ V) (hY : Y ≤ V) (hJV : v .JK ≤ V) :
    Runs (lPair stA) (st S₀ (lp v X L Y) A [])
      (st S₀ (lp v X L Y)
        (if v .JK ≤ ltv stA X Y then oneAcc (lcv stA X Y) (ltv stA X Y) A else A) [])
      (fun _ => True) (20 * opW V) := by
  have hW := one_le_opW V
  have hcv : lcv stA X Y ≤ V := by unfold lcv; split <;> omega
  have htv : ltv stA X Y ≤ V := by unfold ltv; split <;> omega
  have h1 := runs_ctSet_xu S₀ stA (lp v X L Y) A X Y rfl rfl rfl rfl hX hY
  have h2 : Runs (ltR .t .JK .e0)
      (st S₀ (Function.update (Function.update (lp v X L Y) .c (lcv stA X Y)) .t (ltv stA X Y))
        A [])
      (st S₀ (Function.update (Function.update (Function.update (lp v X L Y) .c (lcv stA X Y))
        .t (ltv stA X Y)) .e0 (if ltv stA X Y < v .JK then 1 else 0)) A [])
      (fun _ => True) (opW V) :=
    runs_ltR0 S₀ (Function.update (Function.update (lp v X L Y) .c (lcv stA X Y)) .t
      (ltv stA X Y)) A [] .t .JK .e0 htv hJV rfl
  by_cases hq : v .JK ≤ ltv stA X Y
  · rw [if_pos hq]
    rw [if_neg (show ¬ ltv stA X Y < v .JK by omega)] at h2
    have h3 := runs_emitOne S₀ hB1 (Function.update (Function.update (Function.update
      (lp v X L Y) .c (lcv stA X Y)) .t (ltv stA X Y)) .e0 0) A rfl hV1 hcv htv
    exact runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq'
      (runs_ifR_neg (q := .e0) (p := skip) S₀ _ A [] (by rfl) h3)
      (runs_seq' (runs_clr S₀ _ _ [] .c (by exact hcv))
        (runs_seq' (runs_clr S₀ _ _ [] .t (by exact htv))
          (runs_clr S₀ _ _ [] .e0 (by exact Nat.zero_le V)) le_rfl) le_rfl) le_rfl) le_rfl)
      le_rfl) (st_congr fun r => by cases r <;> rfl) (by omega)
  · rw [if_neg hq]
    rw [if_pos (show ltv stA X Y < v .JK by omega)] at h2
    exact runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq'
      (runs_ifR_pos (q := .e0) (r := emitOne) S₀ _ A [] (by show (1 : ℕ) ≠ 0; omega)
        (runs_skip_st (V := V) S₀ _ A []))
      (runs_seq' (runs_clr S₀ _ _ [] .c (by exact hcv))
        (runs_seq' (runs_clr S₀ _ _ [] .t (by exact htv))
          (runs_clr S₀ _ _ [] .e0 (by exact hV1)) le_rfl) le_rfl) le_rfl) le_rfl)
      le_rfl) (st_congr fun r => by cases r <;> rfl) (by omega)

/-- **One position** `X` of the leftover pass (registers `lb v X L`, `Y = I X`). -/
theorem runs_lBody (IT : RawN) (hIT : IT = .I0T ∨ IT = .I1T) {m : ℕ} (I : Fin m → Fin m)
    (stA : Bool) (v : RegN → ℕ) (A : List Sym) (hT : S₀ (rs IT) = utab (finVals I))
    (hU : S₀ (rs .U) = []) (hB1 : S₀ (rs .B1) = []) (hV1 : 1 ≤ V) (hmV : m ≤ V)
    (hL : (utab (finVals I)).length ≤ V) (hJV : v .JK ≤ V) (X : ℕ) (hX : X < m) (Y : ℕ)
    (hY : (I ⟨X, hX⟩ : ℕ) = Y) (L : ℕ) :
    Runs (lBody IT stA) (st S₀ (lb v X L) A [])
      (st S₀ (lb v (X + 1) L)
        (if X < Y ∧ v .JK ≤ ltv stA X Y then oneAcc (lcv stA X Y) (ltv stA X Y) A else A) [])
      (fun _ => True) (50 * opW V) := by
  have hW := one_le_opW V
  have hYm : Y < m := by rw [← hY]; exact (I ⟨X, hX⟩).2
  have hXV : X ≤ V := by omega
  have hYV : Y ≤ V := by omega
  have h1 := runs_lookI S₀ IT hIT I (lb v X L) A X hX Y hY hT hU rfl rfl hXV hL
  have h2 : Runs (ltR .xu .y .f) (st S₀ (Function.update (lb v X L) .y Y) A [])
      (st S₀ (Function.update (Function.update (lb v X L) .y Y) .f (if X < Y then 1 else 0)) A
        []) (fun _ => True) (opW V) :=
    runs_ltR0 S₀ (Function.update (lb v X L) .y Y) A [] .xu .y .f hXV hYV rfl
  by_cases hlt : X < Y
  · rw [if_pos hlt] at h2
    have h3 := runs_lPair S₀ hB1 stA v X L Y A hV1 hXV hYV hJV
    have key : ∀ A' : List Sym,
        Runs (lPair stA) (st S₀ (lp v X L Y) A []) (st S₀ (lp v X L Y) A' []) (fun _ => True)
          (20 * opW V) →
        Runs (lBody IT stA) (st S₀ (lb v X L) A []) (st S₀ (lb v (X + 1) L) A' [])
          (fun _ => True) (50 * opW V) := fun A' hP =>
      runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq'
        (runs_ifR_pos (q := .f) (r := skip) S₀ _ A [] (by show (1 : ℕ) ≠ 0; omega) hP)
        (runs_seq' (runs_clr S₀ _ _ [] .f (by exact hV1))
          (runs_seq' (runs_clr S₀ _ _ [] .y (by exact hYV)) (runs_inc (V := V) S₀ _ _ [] .xu)
            le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
        (st_congr fun r => by cases r <;> rfl) (by omega)
    by_cases hq : v .JK ≤ ltv stA X Y
    · rw [if_pos (And.intro hlt hq)]
      rw [if_pos hq] at h3
      exact key _ h3
    · rw [if_neg (fun h : X < Y ∧ v .JK ≤ ltv stA X Y => hq h.2)]
      rw [if_neg hq] at h3
      exact key _ h3
  · rw [if_neg hlt] at h2
    rw [if_neg (fun h : X < Y ∧ v .JK ≤ ltv stA X Y => hlt h.1)]
    exact runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq'
      (runs_ifR_neg (q := .f) (p := lPair stA) S₀ _ A [] (by rfl)
        (runs_skip_st (V := V) S₀ _ A []))
      (runs_seq' (runs_clr S₀ _ _ [] .f (by exact Nat.zero_le V))
        (runs_seq' (runs_clr S₀ _ _ [] .y (by exact hYV)) (runs_inc (V := V) S₀ _ _ [] .xu)
          le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      (st_congr fun r => by cases r <;> rfl) (by omega)

end Pair

/-! ## The leftover candidates of a position, as lists -/

theorem pairOf_lt' {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (x : Fin m)
    (h : (x : ℕ) < (I x : ℕ)) : pairOf stA I x = some (if stA then (I x, x) else (x, I x)) := by
  unfold pairOf
  exact if_pos h

theorem pairOf_nlt' {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (x : Fin m)
    (h : ¬ (x : ℕ) < (I x : ℕ)) : pairOf stA I x = none := by
  unfold pairOf
  exact if_neg h

theorem pair_fst' {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (x : Fin m) :
    (((if stA then (I x, x) else (x, I x)).1 : Fin m) : ℕ) = lcv stA x (I x) := by
  cases stA <;> rfl

theorem pair_snd' {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (x : Fin m) :
    (((if stA then (I x, x) else (x, I x)).2 : Fin m) : ℕ) = ltv stA x (I x) := by
  cases stA <;> rfl

theorem schedSyms_one {m K : ℕ} (p : Fin m × Fin m) :
    schedSyms ([p].map fun p => (PosCmd.one p.1 p.2 : PosCmd m K)) =
      cmdSyms (PosCmd.one p.1 p.2 : PosCmd m K) := by
  simp [schedSyms]

/-- The leftover command option of position `x`. -/
def lq {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K : ℕ) (x : Fin m) : Option (Fin m × Fin m) :=
  (pairOf stA I x).filter (leftQ K)

theorem lq_toList_pos {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K JK : ℕ) (x : Fin m)
    (hlt : (x : ℕ) < (I x : ℕ)) (hq : JK ≤ ltv stA x (I x)) (hJK : JK = numChunks m K * K) :
    (lq stA I K x).toList = [if stA then (I x, x) else (x, I x)] := by
  have h : numChunks m K * K ≤ (((if stA then (I x, x) else (x, I x)).2 : Fin m) : ℕ) := by
    rw [pair_snd', ← hJK]
    exact hq
  have hq' : leftQ K (if stA then (I x, x) else (x, I x)) = true := by
    unfold leftQ
    exact decide_eq_true h
  unfold lq
  rw [pairOf_lt' stA I x hlt]
  simp [Option.filter, hq']

theorem lq_toList_negq {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K JK : ℕ) (x : Fin m)
    (hlt : (x : ℕ) < (I x : ℕ)) (hq : ¬ JK ≤ ltv stA x (I x)) (hJK : JK = numChunks m K * K) :
    (lq stA I K x).toList = [] := by
  have h : ¬ numChunks m K * K ≤ (((if stA then (I x, x) else (x, I x)).2 : Fin m) : ℕ) := by
    rw [pair_snd', ← hJK]
    exact hq
  have hq' : leftQ K (if stA then (I x, x) else (x, I x)) = false := by
    unfold leftQ
    exact decide_eq_false h
  unfold lq
  rw [pairOf_lt' stA I x hlt]
  simp [Option.filter, hq']

theorem lq_toList_neglt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K : ℕ) (x : Fin m)
    (hlt : ¬ (x : ℕ) < (I x : ℕ)) : (lq stA I K x).toList = [] := by
  unfold lq
  rw [pairOf_nlt' stA I x hlt]
  all_goals rfl

/-- The accumulator invariant of the pass after `i` positions. -/
def accAt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K : ℕ) (acc : List Sym) (i : ℕ) : List Sym :=
  (schedSyms ((prePairs (lq stA I K) i).map fun p => (PosCmd.one p.1 p.2 : PosCmd m K))).reverse ++
    acc

theorem accAt_zero {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K : ℕ) (acc : List Sym) :
    accAt stA I K acc 0 = acc := by
  unfold accAt
  rw [prePairs_zero]
  all_goals rfl

/-- One position of the invariant. -/
theorem accAt_succ {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K JK : ℕ)
    (hJK : JK = numChunks m K * K) (acc : List Sym) (i : ℕ) (hi : i < m) :
    accAt stA I K acc (i + 1) =
      if i < (I ⟨i, hi⟩ : ℕ) ∧ JK ≤ ltv stA i (I ⟨i, hi⟩) then
        oneAcc (lcv stA i (I ⟨i, hi⟩)) (ltv stA i (I ⟨i, hi⟩)) (accAt stA I K acc i)
      else accAt stA I K acc i := by
  unfold accAt
  rw [prePairs_map_succ (lq stA I K) hi, schedSyms_append_reverse, List.append_assoc]
  by_cases hlt : i < (I ⟨i, hi⟩ : ℕ)
  · by_cases hq : JK ≤ ltv stA i (I ⟨i, hi⟩)
    · rw [if_pos (And.intro hlt hq), lq_toList_pos stA I K JK ⟨i, hi⟩ hlt hq hJK,
        schedSyms_one, one_acc, pair_fst', pair_snd']
      all_goals rfl
    · rw [if_neg (fun h : i < (I ⟨i, hi⟩ : ℕ) ∧ JK ≤ ltv stA i (I ⟨i, hi⟩) => hq h.2),
        lq_toList_negq stA I K JK ⟨i, hi⟩ hlt hq hJK]
      all_goals rfl
  · rw [if_neg (fun h : i < (I ⟨i, hi⟩ : ℕ) ∧ JK ≤ ltv stA i (I ⟨i, hi⟩) => hlt h.1),
      lq_toList_neglt stA I K ⟨i, hi⟩ hlt]
    all_goals rfl

end LeftT1

/-- **The leftover pass of one stage** (`LeftPassStmt`, `PosPermSchedEmitLeftDefs.lean`):
proved. -/
theorem leftPass_holds : LeftPassStmt := by
  unfold LeftPassStmt
  intro S₀ IT hIT m I stA v acc V hT hU hB1 hm _hK hJK hV1 hmV hL hJV
  have hW := one_le_opW V
  have s1 : Runs (copyR .m .len) (st S₀ (lz v) acc [])
      (st S₀ (Function.update (Function.update (lz v) .xu 0) .len m)
        (LeftT1.accAt stA I (v .K) acc 0) []) (fun _ => True) (opW V) := by
    rw [LeftT1.accAt_zero]
    exact runs_weak (runs_copyR0 S₀ (lz v) acc [] .m .len (show v .m ≤ V by omega) rfl)
      (st_congr fun r => by cases r <;> first | rfl | exact hm) le_rfl
  have hstep : ∀ i < m, Runs (lBody IT stA)
      (st S₀ (Function.update (Function.update (lz v) .xu i) .len (m - 1 - i))
        (LeftT1.accAt stA I (v .K) acc i) [])
      (st S₀ (Function.update (Function.update (lz v) .xu (i + 1)) .len (m - 1 - i))
        (LeftT1.accAt stA I (v .K) acc (i + 1)) []) (fun _ => True) (50 * opW V) := by
    intro i hi
    rw [LeftT1.accAt_succ stA I (v .K) (v .JK) hJK acc i hi]
    exact LeftT1.runs_lBody S₀ IT hIT I stA v _ hT hU hB1 hV1 hmV hL hJV i hi _ rfl (m - 1 - i)
  have s2 := runs_loopR S₀ .len rfl (p := lBody IT stA) (fun i => Function.update (lz v) .xu i)
    (fun i => LeftT1.accAt stA I (v .K) acc i) (fun _ => []) (50 * opW V) m hstep
  have s3 := runs_clr S₀ (Function.update (Function.update (lz v) .xu m) .len 0)
    (LeftT1.accAt stA I (v .K) acc m) [] .xu (show m ≤ V from hmV)
  have hacc : LeftT1.accAt stA I (v .K) acc m = (schedSyms (((List.finRange m).filterMap
      (fun x => (pairOf stA I x).filter (leftQ (v .K)))).map
        (fun p => (PosCmd.one p.1 p.2 : PosCmd m (v .K))))).reverse ++ acc := by
    unfold LeftT1.accAt
    rw [prePairs_full]
    all_goals rfl
  refine runs_weak (runs_seq' s1 (runs_seq' s2 s3 le_rfl) le_rfl) ?_ ?_
  · rw [hacc]
    exact st_congr fun r => by cases r <;> rfl
  · have h1 : m * 3 ≤ m * (50 * opW V) := Nat.mul_le_mul_left _ (by omega)
    have h2 : m * (50 * opW V + 3) = m * (50 * opW V) + m * 3 := by ring
    have h3 : (m + 1) * (100 * opW V) = 2 * (m * (50 * opW V)) + 100 * opW V := by ring
    omega

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
