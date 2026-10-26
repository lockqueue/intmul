/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelDefs

/-!
# C-core phase leaf, record-wise sign selection: the parity table (`LeafPhaseMaskSelVal.lean`)

Proves the two parts of `MaskSelStmt` stated in `CCore/LeafPhaseMaskSelDefs.lean`:
* `tabProg_holds : PhaseMaskAux.TabProgStmt` (machine): the table builder `tabProg` refines the
  table on `Tb` once per mask bit on `Msk` (inner `while` over the table with `refStep`, then the
  reversal `moveBlock`), via `runs_while`, `runs_moveBlock`, `runs_liftRegs`;
* `maskTab_holds : PhaseMaskAux.MaskTabStmt` (value): `tab` has `2^{KD}` entries, and entry `q`
  is the parity of the mask bits at the `1` bits of `q`; for the mask bits of `selBit`, this is
  `selBit` at any record `i` with `q = (i / S) mod 2^{KD}`.
No `sorry`.
-/

namespace SubNLogN.Machine.CCore.MaskSelValAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
open SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Machine.CCore.PhaseMaskAux

/-! ## 1. List facts of the refinement -/

theorem refineT_append (m : Bool) (L L' : List Bool) :
    refineT m (L ++ L') = refineT m L ++ refineT m L' := by
  simp [refineT, List.flatMap_append]

theorem refineT_singleton (m x : Bool) : refineT m [x] = [x, xor x m] := by
  simp [refineT]

theorem length_refineT (m : Bool) (L : List Bool) : (refineT m L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [show y :: L = [y] ++ L from rfl, refineT_append, List.length_append, ih,
      refineT_singleton]
    simp
    omega

theorem foldl_refineT_append (ms : List Bool) (x : Bool) (L : List Bool) :
    (ms ++ [x]).foldl (fun L m => refineT m L) L = refineT x (ms.foldl (fun L m => refineT m L) L) := by
  rw [List.foldl_append]
  rfl

theorem length_foldl_refineT (ms L : List Bool) :
    (ms.foldl (fun L m => refineT m L) L).length = 2 ^ ms.length * L.length := by
  induction ms generalizing L with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, length_refineT, pow_succ]
    ring

/-! ## 2. The table builder (machine) -/

section Machine

variable {K : Type} [DecidableEq K]

theorem runs_pre' {σ : Type} {P : Prog K (fun _ => Sym) σ} {S0 S S' : K → List Sym}
    {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (e : S0 = S) : Runs P S0 S' Q T := e ▸ h

theorem runs_post' {σ : Type} {P : Prog K (fun _ => Sym) σ} {S S' S'' : K → List Sym}
    {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (e : S' = S'') : Runs P S S'' Q T := e ▸ h

theorem runs_mono' {σ : Type} {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym}
    {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T ≤ T') : Runs P S S' Q T' :=
  Triple.cost_mono h hT

theorem runs_peekT_bits (k : K) (rest : List Bool) (S : K → List Sym)
    (hS : S k = rest.map Sym.bit) :
    Runs (peekT k) S S (fun v => isBitO v.t = !rest.isEmpty) 1 :=
  Triple.post (runs_peekT k S) (fun s hs => ⟨hs.1, by
    show isBitO s.var.t = !rest.isEmpty
    have h2 : s.var.t = (S k).head? := hs.2
    rw [h2, hS]; cases rest <;> rfl⟩)

theorem runs_refStep {Tb Tb2 : K} (h : Tb ≠ Tb2) (m x : Bool) (rest : List Bool)
    (S : K → List Sym) (hS : S Tb = (x :: rest).map Sym.bit) :
    Runs (refStep m Tb Tb2) S
      (Function.update (Function.update S Tb (rest.map Sym.bit)) Tb2
        (Sym.bit (xor x m) :: Sym.bit x :: S Tb2)) (fun _ => True) 3 := by
  refine Runs.of_eval fun v => ⟨{ v with o := some (Sym.bit x) }, 3, ?_, trivial, le_refl _⟩
  have e1 : Eval [] (popO Tb) ⟨v, S⟩
      ⟨{ v with o := some (Sym.bit x) }, Function.update S Tb (rest.map Sym.bit)⟩ 1 := by
    refine (Eval.pop [] Tb (fun v o => { v with o := o }) v S).of_eq ?_ rfl
    rw [hS]; rfl
  refine (Eval.seq e1 (Eval.seq (Eval.push _ _ _ _ _) (Eval.push _ _ _ _ _))).of_eq ?_ rfl
  simp [Function.update_of_ne h.symm]

/-- The inner state of a refinement pass: `done` refined onto `Tb2`, `rest` left on `Tb`. -/
def stIn (S : K → List Sym) (Tb Tb2 : K) (m : Bool) (done rest : List Bool) : K → List Sym :=
  Function.update (Function.update S Tb (rest.map Sym.bit)) Tb2
    ((refineT m done).reverse.map Sym.bit)

theorem runs_refPass {Tb Tb2 : K} (h : Tb ≠ Tb2) (m : Bool) (L : List Bool) (S : K → List Sym)
    (hTb : S Tb = L.map Sym.bit) (hTb2 : S Tb2 = []) :
    Runs (refPass m Tb Tb2) S (Function.update S Tb ((refineT m L).map Sym.bit)) (fun _ => True)
      (11 * L.length + 6) := by
  have hw := runs_while (pk := peekT Tb) (c := fun v => isBitO v.t) (body := refStep m Tb Tb2)
    (stIn S Tb Tb2 m) 1 (fun _ _ _ => 3)
    (fun done rest => runs_peekT_bits Tb rest _ (by simp [stIn, Function.update_of_ne h]))
    (fun done x rest => runs_post' (runs_refStep h m x rest _
        (by simp [stIn, Function.update_of_ne h])) (by
      funext k
      by_cases h1 : k = Tb2
      · subst h1
        simp [stIn, refineT_append, refineT_singleton]
      · by_cases h2 : k = Tb
        · subst h2
          simp [stIn, h1]
        · simp [stIn, h1, h2]))
    L []
  have hpre : S = stIn S Tb Tb2 m [] L := by
    funext k
    by_cases h1 : k = Tb2
    · subst h1; simp [stIn, hTb2, refineT]
    · by_cases h2 : k = Tb
      · subst h2; simp [stIn, h1, hTb]
      · simp [stIn, h1, h2]
  have hmv := runs_liftRegs lensPO (runs_moveBlock (Ne.symm h) ((refineT m L).reverse) []
    (stIn S Tb Tb2 m ([] ++ L) []) TermOK.nil (by simp [stIn]))
  unfold refPass
  refine runs_pre' (runs_post' (runs_mono' (WP.W9comp.runs_seq hw hmv) ?_) ?_) hpre
  · have hc := whileCost_const 1 3 (fun _ _ _ => 3) (fun _ _ _ => le_refl _) L []
    simp only [List.length_reverse, length_refineT]
    omega
  · funext k
    by_cases h1 : k = Tb
    · subst h1; simp [stIn, h]
    · by_cases h2 : k = Tb2
      · subst h2; simp [stIn, h1, hTb2]
      · simp [stIn, h1, h2]

theorem runs_tabBody {Msk Tb Tb2 : K} (h1 : Msk ≠ Tb) (h2 : Msk ≠ Tb2) (h3 : Tb ≠ Tb2)
    (x : Bool) (rest Lc : List Bool) (S : K → List Sym) (hM : S Msk = (x :: rest).map Sym.bit)
    (hT : S Tb = Lc.map Sym.bit) (hT2 : S Tb2 = []) :
    Runs (.seq (popO Msk) (.ite (fun v => bitOf v.o) (refPass true Tb Tb2) (refPass false Tb Tb2)))
      S (Function.update (Function.update S Msk (rest.map Sym.bit)) Tb
        ((refineT x Lc).map Sym.bit)) (fun _ => True) (11 * Lc.length + 8) := by
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (popO Msk) ⟨v, S⟩
      ⟨{ v with o := some (Sym.bit x) }, Function.update S Msk (rest.map Sym.bit)⟩ 1 := by
    refine (Eval.pop [] Msk (fun v o => { v with o := o }) v S).of_eq ?_ rfl
    rw [hM]; rfl
  have hR := runs_refPass h3 x Lc (Function.update S Msk (rest.map Sym.bit))
    (by rw [Function.update_of_ne (Ne.symm h1)]; exact hT)
    (by rw [Function.update_of_ne (Ne.symm h2)]; exact hT2)
  obtain ⟨⟨v2, S2⟩, t2, e2, ⟨hs2, -⟩, ht2⟩ := hR ⟨{ v with o := some (Sym.bit x) }, _⟩ rfl
  change S2 = _ at hs2
  subst hs2
  refine ⟨v2, 1 + (t2 + 1), ?_, trivial, by omega⟩
  cases x
  · exact Eval.seq e1 (Eval.ite_false rfl e2)
  · exact Eval.seq e1 (Eval.ite_true rfl e2)

/-- The outer state of the table builder: `done` mask bits consumed, `rest` left on `Msk`. -/
def stOut (S : K → List Sym) (Msk Tb : K) (L : List Bool) (done rest : List Bool) :
    K → List Sym :=
  Function.update (Function.update S Msk (rest.map Sym.bit)) Tb
    ((done.foldl (fun L m => refineT m L) L).map Sym.bit)

theorem whileCost_tab (L : List Bool) : ∀ (rest done : List Bool),
    whileCost 1 (fun done _ _ => 11 * (2 ^ done.length * L.length) + 8) done rest +
      11 * (2 ^ done.length * L.length) ≤
    11 * (2 ^ (done.length + rest.length) * L.length) + 10 * rest.length + 1
  | [], done => by simp only [whileCost, List.length_nil, Nat.add_zero]; omega
  | x :: rest, done => by
    have ih := whileCost_tab L rest (done ++ [x])
    simp only [whileCost, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add] at ih ⊢
    have e1 : 2 ^ (done.length + 1) * L.length = 2 * (2 ^ done.length * L.length) := by ring
    have e2 : done.length + 1 + rest.length = done.length + (rest.length + 1) := by ring
    rw [e2] at ih
    omega

end Machine

/-- **The table builder** (`TabProgStmt`). -/
theorem tabProg_holds : PhaseMaskAux.TabProgStmt := by
  intro K _ Msk Tb Tb2 h1 h2 h3 ms L S hM hT hT2
  have hw := runs_while (pk := peekT Msk) (c := fun v => isBitO v.t)
    (body := .seq (popO Msk) (.ite (fun v => bitOf v.o) (refPass true Tb Tb2)
      (refPass false Tb Tb2)))
    (stOut S Msk Tb L) 1 (fun done _ _ => 11 * (2 ^ done.length * L.length) + 8)
    (fun done rest => runs_peekT_bits Msk rest _ (by simp [stOut, Function.update_of_ne h1]))
    (fun done x rest => runs_mono' (runs_post' (runs_tabBody h1 h2 h3 x rest
        (done.foldl (fun L m => refineT m L) L) _
        (by simp [stOut, Function.update_of_ne h1])
        (by simp [stOut])
        (by simp [stOut, Function.update_of_ne (Ne.symm h2), Function.update_of_ne (Ne.symm h3),
          hT2]))
      (by
        funext k
        by_cases k1 : k = Tb
        · subst k1; simp [stOut]
        · by_cases k2 : k = Msk
          · subst k2; simp [stOut, k1]
          · simp [stOut, k1, k2]))
      (by rw [length_foldl_refineT]))
    ms []
  have hpre : S = stOut S Msk Tb L [] ms := by
    funext k
    by_cases k1 : k = Tb
    · subst k1; simp [stOut, hT]
    · by_cases k2 : k = Msk
      · subst k2; simp [stOut, k1, hM]
      · simp [stOut, k1, k2]
  unfold tabProg
  refine runs_pre' (runs_post' (runs_mono' hw ?_) ?_) hpre
  · have hc := whileCost_tab L ms []
    simp only [List.length_nil, pow_zero, one_mul, Nat.zero_add] at hc
    have h4 : 1 ≤ 2 ^ ms.length := Nat.one_le_two_pow
    have h5 : 2 ^ ms.length * L.length ≤ 2 ^ ms.length * (L.length + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · simp [stOut]

/-! ## 3. The parity table (value) -/

theorem tab_append (ms : List Bool) (m : Bool) : tab (ms ++ [m]) = refineT m (tab ms) :=
  foldl_refineT_append ms m [false]

theorem length_tab (ms : List Bool) : (tab ms).length = 2 ^ ms.length := by
  unfold tab; rw [length_foldl_refineT]; simp

theorem getD_refineT (m : Bool) (L : List Bool) : ∀ q, q < 2 * L.length →
    (refineT m L).getD q false = xor (L.getD (q / 2) false) (decide (q % 2 = 1) && m) := by
  induction L with
  | nil => intro q hq; simp at hq
  | cons y L ih =>
    intro q hq
    rw [show y :: L = [y] ++ L from rfl, refineT_append, refineT_singleton]
    rcases q with _ | _ | q
    · simp
    · simp
    · have hq' : q < 2 * L.length := by simp at hq; omega
      rw [List.getD_append_right _ _ _ _ (by simp), show q + 2 - [y, xor y m].length = q by simp,
        ih q hq', show (q + 2) / 2 = q / 2 + 1 by omega, show (q + 2) % 2 = q % 2 by omega]
      simp

/-- The number of mask bits at the `1` bits of `q` (the first mask bit is the MSB of `q`). -/
def cntSel (ms : List Bool) (q : ℕ) : ℕ :=
  ∑ r ∈ Finset.range ms.length, if ms.getD r false && q.testBit (ms.length - 1 - r) then 1 else 0

theorem decide_odd_add_ite (a : ℕ) (b : Bool) :
    decide (Odd (a + if b then 1 else 0)) = xor (decide (Odd a)) b := by
  rcases Nat.even_or_odd a with h | h
  · cases b <;> simp [h, Nat.odd_add_one]
  · have h' : ¬ Even a := Nat.not_even_iff_odd.mpr h
    cases b <;> simp [h, h', Nat.odd_add_one]

theorem cntSel_append (ms : List Bool) (m : Bool) (q : ℕ) :
    cntSel (ms ++ [m]) q = cntSel ms (q / 2) + if m && q.testBit 0 then 1 else 0 := by
  unfold cntSel
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [List.getD_append _ _ _ _ hr, show ms.length + 1 - 1 - r = (ms.length - 1 - r) + 1 by omega,
      Nat.testBit_succ]
  · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, show ms.length + 1 - 1 - ms.length = 0
      by omega]
    rfl

/-- **Entry `q` of the table** is the parity of the mask bits at the `1` bits of `q`. -/
theorem tab_getD (ms : List Bool) : ∀ q, q < 2 ^ ms.length →
    (tab ms).getD q false = decide (Odd (cntSel ms q)) := by
  induction ms using List.reverseRecOn with
  | nil =>
    intro q hq
    simp at hq
    subst hq
    simp [tab, cntSel]
  | append_singleton ms m ih =>
    intro q hq
    rw [List.length_append, List.length_singleton, pow_succ] at hq
    rw [tab_append, getD_refineT m (tab ms) q (by rw [length_tab]; omega),
      ih (q / 2) (by omega), cntSel_append, decide_odd_add_ite, Nat.testBit_zero]
    cases m <;> simp [Bool.and_comm]

/-! ## 4. The mask bits -/

theorem length_flatMap_const {α β : Type} (l : List α) (g : α → List β) (n : ℕ)
    (hg : ∀ a, (g a).length = n) : (l.flatMap g).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, hg, ih, Nat.succ_mul]; omega

theorem getD_flatMap_const {α β : Type} (l : List α) (g : α → List β) (n : ℕ)
    (hg : ∀ a, (g a).length = n) (a0 : α) (d : β) :
    ∀ x, x < l.length * n → (l.flatMap g).getD x d = (g (l.getD (x / n) a0)).getD (x % n) d := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hx
      · exact h
    rw [List.flatMap_cons]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hg]; exact hxn), Nat.div_eq_of_lt hxn,
        Nat.mod_eq_of_lt hxn]
      rfl
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + n := ⟨x - n, by omega⟩
      rw [List.getD_append_right _ _ _ _ (by rw [hg]; omega), hg, Nat.add_sub_cancel,
        ih y (by simp [Nat.succ_mul] at hx; omega), Nat.add_div_right _ hn, Nat.add_mod_right]
      rfl

theorem getD_block (K ρ : ℕ) (b : Bool) (u : ℕ) (hu : u < K) (hρ : ρ < K) :
    (List.replicate (K - 1 - ρ) false ++ b :: List.replicate ρ false).getD u false =
      (decide (u = K - 1 - ρ) && b) := by
  rcases Nat.lt_trichotomy u (K - 1 - ρ) with h | h | h
  · rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, h, Nat.ne_of_lt h]
  · subst h
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    obtain ⟨w, hw⟩ : ∃ w, u - (K - 1 - ρ) = w + 1 := ⟨u - (K - 1 - ρ) - 1, by omega⟩
    rw [List.length_replicate, hw]
    simp [List.getD_eq_getElem?_getD, Nat.ne_of_gt h]

theorem length_maskMSB (K ρ : ℕ) (hρ : ρ < K) (mem : List Bool) :
    (maskMSB K ρ mem).length = K * mem.length := by
  unfold maskMSB
  rw [length_flatMap_const _ _ K (fun b => by simp; omega), Nat.mul_comm]

theorem getD_maskMSB (K ρ : ℕ) (hρ : ρ < K) (mem : List Bool) (r : ℕ)
    (hr : r < K * mem.length) :
    (maskMSB K ρ mem).getD r false = (decide (r % K = K - 1 - ρ) && mem.getD (r / K) false) := by
  unfold maskMSB
  rw [getD_flatMap_const _ _ K (fun b => by simp; omega) false false r
    (by rw [Nat.mul_comm]; exact hr)]
  exact getD_block K ρ _ _ (Nat.mod_lt _ (by omega)) hρ

theorem length_membList_pre (ss : Finset (Fin mn)) (j0 f : ℕ) :
    (List.replicate j0 false ++
      (List.finRange mn).flatMap (fun s => List.replicate f (decide (s ∈ ss)))).length =
      j0 + mn * f := by
  rw [List.length_append, List.length_replicate,
    length_flatMap_const _ _ f (fun s => by rw [List.length_replicate]), List.length_finRange]

theorem length_membList (ss : Finset (Fin mn)) (j0 f D : ℕ) (h : j0 + mn * f ≤ D) :
    (membList ss j0 f D).length = D := by
  unfold membList
  rw [List.length_append, length_membList_pre, List.length_replicate]
  omega

theorem getD_replicate_false (n i : ℕ) : (List.replicate n false).getD i false = false := by
  induction n generalizing i with
  | zero => simp
  | succ n ih => cases i <;> simp [List.replicate_succ, ih]

theorem getD_replicate_of_lt (n i : ℕ) (b d : Bool) (h : i < n) :
    (List.replicate n b).getD i d = b := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [List.replicate_succ]
    | succ i => simp only [List.replicate_succ, List.getD_cons_succ]; exact ih i (by omega)

theorem getD_membList_lt (ss : Finset (Fin mn)) (j0 f D j : ℕ) (hj : j < j0) :
    (membList ss j0 f D).getD j false = false := by
  unfold membList
  rw [List.getD_append _ _ _ _ (by rw [length_membList_pre]; omega),
    List.getD_append _ _ _ _ (by rw [List.length_replicate]; exact hj)]
  exact getD_replicate_false _ _

theorem getD_membList_ge (ss : Finset (Fin mn)) (j0 f D j : ℕ) (hj : j0 + mn * f ≤ j) :
    (membList ss j0 f D).getD j false = false := by
  unfold membList
  rw [List.getD_append_right _ _ _ _ (by rw [length_membList_pre]; exact hj)]
  exact getD_replicate_false _ _

/-- Membership of the slot `s` (as a number) in `ss`. -/
def inSS (ss : Finset (Fin mn)) (s : ℕ) : Bool := if h : s < mn then decide (⟨s, h⟩ ∈ ss) else false

theorem getD_membList_mid (ss : Finset (Fin mn)) (j0 f D x : ℕ) (hx : x < mn * f) :
    (membList ss j0 f D).getD (j0 + x) false = inSS ss (x / f) := by
  have hmn : 0 < mn := Nat.pos_of_ne_zero (fun h => by
    rw [h, Nat.zero_mul] at hx; exact absurd hx (Nat.not_lt_zero _))
  have hf : 0 < f := Nat.pos_of_ne_zero (fun h => by
    rw [h, Nat.mul_zero] at hx; exact absurd hx (Nat.not_lt_zero _))
  have hxf : x / f < mn := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  unfold membList
  rw [List.getD_append _ _ _ _ (by rw [length_membList_pre]; omega),
    List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; omega), List.length_replicate,
    Nat.add_sub_cancel_left,
    getD_flatMap_const _ _ f (fun s => by rw [List.length_replicate]) ⟨0, hmn⟩ false x
      (by rw [List.length_finRange]; exact hx),
    getD_replicate_of_lt _ _ _ _ (Nat.mod_lt _ hf)]
  have hg : (List.finRange mn).getD (x / f) ⟨0, hmn⟩ = ⟨x / f, hxf⟩ := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_finRange]; exact hxf), List.getElem_finRange]
    rfl
  rw [hg]
  unfold inSS
  rw [dif_pos hxf]

theorem sum_range_blocks (D K : ℕ) (g : ℕ → ℕ) :
    ∑ r ∈ Finset.range (D * K), g r = ∑ j ∈ Finset.range D, ∑ u ∈ Finset.range K, g (j * K + u) := by
  induction D with
  | zero => simp
  | succ D ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem cntSel_maskMSB (K ρ D : ℕ) (hρ : ρ < K) (mem : List Bool) (hm : mem.length = D)
    (q : ℕ) :
    cntSel (maskMSB K ρ mem) q = ∑ j ∈ Finset.range D,
      (if mem.getD j false && q.testBit (K * (D - 1 - j) + ρ) then 1 else 0) := by
  unfold cntSel
  rw [length_maskMSB K ρ hρ, hm, Nat.mul_comm K D, sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hK : 0 < K := by omega
  have hmod : ∀ u, u < K → (j * K + u) % K = u := fun u hu => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  have hdiv : ∀ u, u < K → (j * K + u) / K = j := fun u hu => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hu, Nat.zero_add]
  have hjK : ∀ u, u < K → j * K + u < K * mem.length := fun u hu => by
    have := Nat.mul_le_mul_right K (show j + 1 ≤ D by omega)
    rw [hm, Nat.mul_comm K D]; rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [Finset.sum_eq_single (K - 1 - ρ)]
  · have e : D * K = K * (D - 1 - j) + j * K + K := by
      have : D = (D - 1 - j) + j + 1 := by omega
      conv_lhs => rw [this]
      ring
    rw [getD_maskMSB K ρ hρ mem _ (hjK _ (by omega)), hmod _ (by omega), hdiv _ (by omega),
      show D * K - 1 - (j * K + (K - 1 - ρ)) = K * (D - 1 - j) + ρ by omega]
    simp
  · intro u hu hne
    rw [Finset.mem_range] at hu
    rw [getD_maskMSB K ρ hρ mem _ (hjK u hu), hmod u hu]
    simp [hne]
  · intro h
    simp at h
    omega

theorem sum_ss (ss : Finset (Fin mn)) (H : ℕ → ℕ) :
    ∑ s ∈ ss, H s.val = ∑ s ∈ Finset.range mn, if inSS ss s then H s else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun s => if inSS ss s then H s else 0)]
  have e : ∀ s : Fin mn, inSS ss s.val = decide (s ∈ ss) := fun s => by
    unfold inSS; rw [dif_pos s.isLt]
  simp only [e, decide_eq_true_eq]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_membList (ss : Finset (Fin mn)) (j0 f D : ℕ) (h : j0 + mn * f ≤ D) (g : ℕ → Bool) :
    ∑ j ∈ Finset.range D, (if (membList ss j0 f D).getD j false && g j then 1 else 0) =
      ∑ s ∈ ss, ∑ c ∈ Finset.range f, (if g (j0 + s.val * f + c) then 1 else 0) := by
  rw [show Finset.range D = Finset.range (j0 + (mn * f + (D - (j0 + mn * f)))) by congr 1; omega,
    Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ Finset.range j0,
      (if (membList ss j0 f D).getD j false && g j then 1 else 0) = 0 :=
    Finset.sum_eq_zero (fun j hj => by
      rw [Finset.mem_range] at hj; rw [getD_membList_lt _ _ _ _ _ hj, Bool.false_and]; rfl)
  have h3 : ∑ y ∈ Finset.range (D - (j0 + mn * f)),
      (if (membList ss j0 f D).getD (j0 + (mn * f + y)) false && g (j0 + (mn * f + y))
        then 1 else 0) = 0 :=
    Finset.sum_eq_zero (fun y _ => by
      rw [getD_membList_ge _ _ _ _ _ (by omega), Bool.false_and]; rfl)
  have hmid : ∑ x ∈ Finset.range (mn * f),
      (if (membList ss j0 f D).getD (j0 + x) false && g (j0 + x) then 1 else 0) =
      ∑ x ∈ Finset.range (mn * f), (if inSS ss (x / f) && g (j0 + x) then 1 else 0) :=
    Finset.sum_congr rfl (fun x hx => by
      rw [Finset.mem_range] at hx; rw [getD_membList_mid _ _ _ _ _ hx])
  rw [h1, h3, hmid, Nat.zero_add, Nat.add_zero, sum_ss ss (fun s => ∑ c ∈ Finset.range f,
      (if g (j0 + s * f + c) then 1 else 0)), sum_range_blocks]
  apply Finset.sum_congr rfl
  intro s _
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf; simp
  · have hin : ∀ c ∈ Finset.range f,
        (if inSS ss ((s * f + c) / f) && g (j0 + (s * f + c)) then 1 else 0) =
        (if inSS ss s && g (j0 + s * f + c) then 1 else 0) := fun c hc => by
      rw [Finset.mem_range] at hc
      rw [Nat.add_comm (s * f) c, Nat.add_mul_div_right _ _ hf, Nat.div_eq_of_lt hc,
        Nat.zero_add, Nat.add_comm c (s * f), ← Nat.add_assoc]
    rw [Finset.sum_congr rfl hin]
    by_cases hs' : inSS ss s
    · simp [hs']
    · simp [hs']

theorem testBit_chunk (K D S i j ρ : ℕ) (hρ : ρ < K) :
    ((i / S) % 2 ^ (K * D)).testBit (K * (D - 1 - j) + ρ) = chunkBit K D S i j ρ := by
  unfold chunkBit
  conv_rhs => rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hρ, Nat.add_comm]

/-- **The parity table computes `selBit`** (`MaskTabStmt`). -/
theorem maskTab_holds : PhaseMaskAux.MaskTabStmt := by
  intro ss K D S j0 k ρ i hk hρ hD
  have hf : j0 + mn * mn ^ (k - 1) ≤ D := by
    have : mn * mn ^ (k - 1) = mn ^ k := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hlenM := length_membList ss j0 (mn ^ (k - 1)) D hf
  have hlenS : (maskMSB K ρ (membList ss j0 (mn ^ (k - 1)) D)).length = K * D := by
    rw [length_maskMSB K ρ hρ, hlenM]
  refine ⟨by rw [length_tab, hlenS], ?_⟩
  have hq : (i / S) % 2 ^ (K * D) < 2 ^ (K * D) := Nat.mod_lt _ (by positivity)
  rw [tab_getD _ _ (by rw [hlenS]; exact hq), cntSel_maskMSB K ρ D hρ _ hlenM,
    sum_membList ss j0 (mn ^ (k - 1)) D hf
      (fun j => ((i / S) % 2 ^ (K * D)).testBit (K * (D - 1 - j) + ρ))]
  unfold selBit
  simp only [testBit_chunk K D S i _ ρ hρ]

end SubNLogN.Machine.CCore.MaskSelValAux
