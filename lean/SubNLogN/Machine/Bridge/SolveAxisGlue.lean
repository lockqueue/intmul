/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisCalls

/-!
# K5-SOLVE driver (5): list and width glue of the driver (`Bridge/SolveAxisGlue.lean`)

Small facts used by the driver run: `2 ≤ A_i` for `i ≠ 0`, the encodings of the input and of the
parameter rows in the forms read by the sweep (`encVec_eq_map`, `rowF_eq`, `rowB_eq`), lengths of
one-coefficient arrays, membership of the half/reindexed entries in the input (for the width
premises), the widths of the parameter rows (`TablesFit`, with the extra bit for `-â`), and the
final state (`mk_eV`).

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
  SubNLogN.Math.Common SubNLogN.Math.Bridge
open SubNLogN.Machine.Bridge.SolveAux (Fits2 rec1s sweepHalfI)

variable {d : ℕ}

theorem two_le_prefixProd {t : Fin d → ℕ} (hshape : ShapeOK t) (i : Fin d) (hi : (i : ℕ) ≠ 0) :
    2 ≤ prefixProd t i := by
  have hd : 0 < d := by have := i.isLt; omega
  have h0 : (⟨0, hd⟩ : Fin d) ∈ Finset.univ.filter (fun l : Fin d => (l : ℕ) < (i : ℕ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hdv := Finset.dvd_prod_of_mem t h0
  have hpos := LemmaBInverse.prefixProd_pos hshape (i : ℕ)
  unfold prefixProd at hpos ⊢
  exact le_trans (hshape _).1 (Nat.le_of_dvd hpos hdv)

theorem len_solveYs (q : ℕ) {t : Fin d → ℕ} (Y : Fin (totalLen t) → ℂ) :
    (solveYs q Y).length = totalLen t := by
  simp [solveYs]

theorem encVec_eq_map (q : ℕ) {t : Fin d → ℕ} (Y : Fin (totalLen t) → ℂ) :
    encVec q Y = (solveYs q Y).map fun c => [c] := by
  simp only [encVec, solveYs, List.map_map]
  rfl

theorem rowF_eq (b : BrPar) (i : Fin b.d) (w : ℕ) (g : ℕ → ℤ) :
    carrSyms w (solParamRow b i 0 g) = rec1s w ((solveRowF b.t i g).map fun m => (m, 0)) := by
  simp only [rec1s, solParamRow, solveRowF, List.map_map, solU0, Nat.zero_mul, Nat.zero_add]
  rfl

theorem rowB_eq (b : BrPar) (i : Fin b.d) (w : ℕ) (g : ℕ → ℤ) :
    carrSyms w (solParamRow b i 1 g) = rec1s w ((solveRowB b.t i g).map fun m => (m, 0)) := by
  simp only [rec1s, solParamRow, solveRowB, List.map_map, solU0, Nat.one_mul]
  rfl

theorem len_solveRowF {t : Fin d → ℕ} (i : Fin d) (g : ℕ → ℤ) :
    (solveRowF t i g).length = solveM t i := by simp [solveRowF]

theorem len_solveRowB {t : Fin d → ℕ} (i : Fin d) (g : ℕ → ℤ) :
    (solveRowB t i g).length = solveM t i := by simp [solveRowB]

theorem len_natSyms (n : ℕ) : (natSyms n).length = bitLen n := List.length_map _

theorem natSyms_one' : natSyms 1 = [Sym.bit true] := by
  rw [natSyms, show (1 : ℕ) = 0 + 1 from rfl, TMFw.encodeNat_succ, TMFw.encodeNat_zero]; rfl

theorem len_crecBits_one' (w : ℕ) (c : CInt) : (crecBits w [c]).length = 2 * w := by
  simp [crecBits, coefBits, twosBits, bitsLE]; ring

/-- An array of one-coefficient records of width `w` has `|v|·(2w+1)` symbols. -/
theorem len_carrSyms_one (w : ℕ) : ∀ v : List (List CInt), (∀ cs ∈ v, cs.length = 1) →
    (carrSyms w v).length = v.length * (2 * w + 1)
  | [], _ => by simp [carrSyms, arrSyms, blk]
  | cs :: v, h => by
    have ih := len_carrSyms_one w v (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
      have h1 := h cs (List.mem_cons_self ..)
      match cs, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at ih ⊢
    rw [ih, recSyms, List.length_append, List.length_map, len_crecBits_one', List.length_singleton]
    ring

theorem forall_len_map_one {α : Type} (f : α → CInt) (l : List α) :
    ∀ cs ∈ l.map (fun a => [f a]), cs.length = 1 := by
  intro cs hcs
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hcs
  rfl

theorem forall_len_map_one' (l : List CInt) : ∀ cs ∈ l.map (fun c => [c]), cs.length = 1 := by
  intro cs hcs
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hcs
  rfl

/-- `∑ (12·|bs| + c)` over records of equal length `k`. -/
theorem sum_map_const_len (k c : ℕ) : ∀ l : List (List Bool), (∀ bs ∈ l, bs.length = k) →
    (l.map fun bs => 12 * bs.length + c).sum = l.length * (12 * k + c)
  | [], _ => by simp
  | bs :: l, h => by
    have ih := sum_map_const_len k c l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, h bs (List.mem_cons_self ..)]
    ring

theorem mem_of_mem_fwdHalf {α : Type} {M L : ℕ} (hM : 0 < M) {v : List α}
    (hv : v.length = L * (2 * M)) {y : α} (hy : y ∈ SolveSplit.fwdHalf M v) : y ∈ v := by
  obtain ⟨x, hx, hxy⟩ := List.getElem_of_mem hy
  have hl := SolveSplit.length_fwdHalf hM hv
  have h := SolveSplit.getElem?_fwdHalf hM hv (x := x) (by omega)
  rw [List.getElem?_eq_getElem hx, hxy] at h
  exact List.mem_of_getElem? h.symm

theorem mem_of_mem_bwdHalf {α : Type} {M L : ℕ} (hM : 0 < M) {v : List α}
    (hv : v.length = L * (2 * M)) {y : α} (hy : y ∈ SolveSplit.bwdHalf M v) : y ∈ v := by
  obtain ⟨x, hx, hxy⟩ := List.getElem_of_mem hy
  have hl := SolveSplit.length_bwdHalf hM hv
  have h := SolveSplit.getElem?_bwdHalf hM hv (x := x) (by omega)
  rw [List.getElem?_eq_getElem hx, hxy] at h
  exact List.mem_of_getElem? h.symm

theorem mem_of_mem_reindexI {α : Type} {M L : ℕ} (hM : 0 < M) {u : List α}
    (hu : u.length = L * M) {y : α} (hy : y ∈ SolveSplit.reindexI M u) : y ∈ u := by
  obtain ⟨x, hx, hxy⟩ := List.getElem_of_mem hy
  have hl := SolveSplit.length_reindexI hM hu
  have hxL : x / M < L := by rw [Nat.div_lt_iff_lt_mul hM]; omega
  have h := SolveSplit.getElem?_reindexI hM hu hxL (Nat.mod_lt x hM)
  rw [Nat.div_add_mod' x M, List.getElem?_eq_getElem hx, hxy] at h
  exact List.mem_of_getElem? h.symm

theorem fits_solveYs {w q : ℕ} {t : Fin d → ℕ} {Y : Fin (totalLen t) → ℂ} (h : ArrFits w q Y) :
    ∀ y ∈ solveYs q Y, Fits2 w y := by
  intro y hy
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hy
  exact h f

theorem fitsTwos_succ {w : ℕ} (hw : 1 ≤ w) {x : ℤ} (h : FitsTwos w x) :
    FitsTwos (w + 1) x ∧ FitsTwos (w + 1) (-x) := by
  unfold FitsTwos at *
  obtain ⟨h1, h2⟩ := h
  have hp : (2 : ℤ) ^ (w - 1) < 2 ^ (w + 1 - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

theorem tab_fits {b : BrPar} {T : BridgeTables b.t} {i : Fin b.d} (hi : (i : ℕ) ≠ 0)
    (htf : TablesFit b.wT b.P b.t T) {u : ℕ} (hu : u < b.t i) :
    FitsTwos b.wT (solveGMu b.P T i u) ∧ FitsTwos b.wT (realInt (b.P + 2) (T.ahat i u)) ∧
      FitsTwos b.wT (solveGGm b.P T i u) := by
  have hmem : i ∈ deconvOrder b.d := by simp [deconvOrder, hi]
  have hf := htf.2 i hmem
  have hrec : solRec b.P T i u ∈ solBlock b.t b.P T i :=
    List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩
  exact ⟨(hf _ hrec (realInt (b.P + 2) (T.mu i u), 0) (by simp [solRec])).1,
    (hf _ hrec (realInt (b.P + 2) (T.ahat i u), 0) (by simp [solRec])).1,
    (hf _ hrec (realInt (b.P + 2) (T.gam i u), 0) (by simp [solRec])).1⟩

theorem digit_lt {b : BrPar} {i : Fin b.d} (hshape : ShapeOK b.t) {s : ℕ}
    (hs : s < solveM b.t i) : s / solveU b.t i < b.t i / 2 ∧ b.t i / 2 + s / solveU b.t i < b.t i := by
  obtain ⟨-, -, -, hMσ, hU, -, ht2⟩ := SolveMathAux.solve_arith hshape i
  have hσ := LemmaBInverse.suffixProd_pos hshape i
  have h : s / solveU b.t i < b.t i / 2 := by
    rw [hU, Nat.div_lt_iff_lt_mul hσ]; rw [hMσ] at hs; exact hs
  exact ⟨h, by omega⟩

theorem fits_rowF {b : BrPar} {T : BridgeTables b.t} {i : Fin b.d} (hshape : ShapeOK b.t)
    (hi : (i : ℕ) ≠ 0) (hwT : 1 ≤ b.wT) (htf : TablesFit b.wT b.P b.t T) :
    (∀ m ∈ solveRowF b.t i (solveGMu b.P T i), FitsTwos (b.wT + 1) m) ∧
    (∀ m ∈ solveRowF b.t i (solveGNa b.P T i), FitsTwos (b.wT + 1) m) ∧
    (∀ m ∈ solveRowF b.t i (solveGGm b.P T i), FitsTwos (b.wT + 1) m) := by
  have key : ∀ s, s < solveM b.t i → s / solveU b.t i < b.t i := fun s hs => by
    have := (digit_lt hshape hs).1; omega
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).1).1
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).2.1).2
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).2.2).1

theorem fits_rowB {b : BrPar} {T : BridgeTables b.t} {i : Fin b.d} (hshape : ShapeOK b.t)
    (hi : (i : ℕ) ≠ 0) (hwT : 1 ≤ b.wT) (htf : TablesFit b.wT b.P b.t T) :
    (∀ m ∈ solveRowB b.t i (solveGMu b.P T i), FitsTwos (b.wT + 1) m) ∧
    (∀ m ∈ solveRowB b.t i (solveGNa b.P T i), FitsTwos (b.wT + 1) m) ∧
    (∀ m ∈ solveRowB b.t i (solveGGm b.P T i), FitsTwos (b.wT + 1) m) := by
  have key : ∀ s, s < solveM b.t i → b.t i / 2 + s / solveU b.t i < b.t i := fun s hs =>
    (digit_lt hshape hs).2
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).1).1
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).2.1).2
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    exact (fitsTwos_succ hwT (tab_fits hi htf (key s (List.mem_range.1 hs))).2.2).1

/-- The final (and initial) driver state: the bridge state with the work array replaced. -/
theorem mk_eV {EP : Type} [DecidableEq EP] (S : DK EP → List Sym) (hS : KClean S)
    (a : List Sym) : mk S (eV (S (kW .ax)) (S (kW .ex)) a) = Function.update S (kW .arr) a := by
  funext k
  rcases k with (n | w) | (y | e)
  · have h : (Sum.inl (Sum.inl n) : DK EP) ≠ kW .arr := by simp
    rw [Function.update_of_ne h] <;> rfl
  · cases w
    · show a = _
      exact (Function.update_self (kW .arr : DK EP) a S).symm
    · have h : (Sum.inl (Sum.inr BrW.ax) : DK EP) ≠ kW .arr := by simp
      rw [Function.update_of_ne h] <;> rfl
    · have h : (Sum.inl (Sum.inr BrW.ex) : DK EP) ≠ kW .arr := by simp
      rw [Function.update_of_ne h] <;> rfl
  · have h : (Sum.inr (Sum.inl y) : DK EP) ≠ kW .arr := by simp
    rw [Function.update_of_ne h]
    exact (hS (.inl y)).symm
  · have h : (Sum.inr (Sum.inr e) : DK EP) ≠ kW .arr := by simp
    rw [Function.update_of_ne h] <;> rfl

end SubNLogN.Machine.Bridge.SolveDrvAux
