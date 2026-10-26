/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Node
import SubNLogN.S1.Params

/-!
# Proposition A.7 skeleton, part 4 (`AppC/C5Final.lean`): from a kit to `C5InterchangeStmt`

Implements the recurrence-to-cost step of Proposition A.7 (`prop:transfer11`). (`AppC` and `C5`/`c5`
retain earlier draft numbering for stability; see Appendix A.) Given a kernel kit for a network
instance `N` with `W = W_b = tripleWb 100` roles and at most `s_b = tripleSb 100` children per node
(`NetFacts`), on `KLoc (Fin 6) E` with the six named contract stacks in place, `c5Prog kit` meets
`C5InterchangeStmt q τ`: `kit_runs` gives cost `powBudget s_b W_b c k V + 2`, and `powBudget_le_ceil`
with `s_b/W_b < m^τ` turns it into `(4c + 2)·(⌈V·(m^k)^τ⌉₊ + 1)`.
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
open SubNLogN.Math.Cost.Recurrence

/-- `V·⌈x⌉₊ ≤ 2·⌈V·x⌉₊` for `x ≥ 1`. -/
theorem ceil_mul_le (V : ℕ) (x : ℝ) (hx : 1 ≤ x) : V * ⌈x⌉₊ ≤ 2 * ⌈(V : ℝ) * x⌉₊ := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one h0
    linarith
  have h2 : (V : ℝ) * x ≤ ⌈(V : ℝ) * x⌉₊ := Nat.le_ceil _
  have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have key : ((V * ⌈x⌉₊ : ℕ) : ℝ) ≤ ((2 * ⌈(V : ℝ) * x⌉₊ : ℕ) : ℝ) := by
    push_cast
    calc (V : ℝ) * ⌈x⌉₊ ≤ V * (2 * x) := mul_le_mul_of_nonneg_left h1 hV
      _ = 2 * (V * x) := by ring
      _ ≤ 2 * ⌈(V : ℝ) * x⌉₊ := by linarith
  exact_mod_cast key

/-- The premise `s_b/W_b < m^τ` forces `τ ≥ 0` (`s_b ≥ W_b`, `m > 1`). -/
theorem tau_nonneg {τ : ℝ} (h : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ) :
    0 ≤ τ := by
  rcases le_or_gt 0 τ with h0 | hneg
  · exact h0
  exfalso
  have hm : (1 : ℝ) < tripleM 100 := by rw [S1.tripleM_100]; norm_num
  have h1 : (tripleM 100 : ℝ) ^ τ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hm hneg
  have h2 : (1 : ℝ) ≤ (tripleSb 100 : ℝ) / tripleWb 100 := by
    rw [S1.tripleSb_100, S1.tripleWb_100, le_div_iff₀ (by norm_num)]
    norm_num
  linarith

/-- **Budget conversion** (Proposition A.7 (`prop:transfer11`)): with `s_b/W_b < m^τ` and
`W_b^k ∣ V`, `powBudget s_b W_b c k V + 2 ≤ (4c + 2)·(⌈V·(m^k)^τ⌉₊ + 1)`. -/
theorem powBudget_le_c5 {c k V : ℕ} {τ : ℝ}
    (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    (hdiv : tripleWb 100 ^ k ∣ V) :
    powBudget (tripleSb 100) (tripleWb 100) c k V + 2 ≤
      (4 * c + 2) * (⌈(V : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ + 1) := by
  have hW : 0 < tripleWb 100 := by rw [S1.tripleWb_100]; norm_num
  have h2 : 2 * tripleWb 100 ≤ tripleSb 100 := by rw [S1.tripleWb_100, S1.tripleSb_100]; norm_num
  have hWr : (0 : ℝ) < tripleWb 100 := by exact_mod_cast hW
  have hdef : (tripleSb 100 : ℝ) ≤ tripleWb 100 * (tripleM 100 : ℝ) ^ τ := by
    rw [div_lt_iff₀ hWr] at hτ
    linarith
  have hb := powBudget_le_ceil (c := c) (k := k) (V := V) hW h2 hdef hdiv
  have hτ0 := tau_nonneg hτ
  have hx : (1 : ℝ) ≤ ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ := by
    apply Real.one_le_rpow _ hτ0
    have : 1 ≤ tripleM 100 ^ k := Nat.one_le_pow _ _ (by rw [S1.tripleM_100]; norm_num)
    exact_mod_cast this
  have hc := ceil_mul_le V _ hx
  have hb2 : 2 * c * V * ⌈((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ ≤
      4 * c * ⌈(V : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ := by
    calc 2 * c * V * ⌈((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ =
          2 * c * (V * ⌈((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊) := by ring
      _ ≤ 2 * c * (2 * ⌈(V : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊) := Nat.mul_le_mul_left _ hc
      _ = 4 * c * ⌈(V : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊ := by ring
  set X := ⌈(V : ℝ) * ((tripleM 100 ^ k : ℕ) : ℝ) ^ τ⌉₊
  have hexp : (4 * c + 2) * (X + 1) = 4 * c * X + 2 * X + 4 * c + 2 := by ring
  rw [hexp]
  omega

/-- **From a kit to the Proposition A.7 contract.** For a network instance `N` with `W_b` roles, at most
`s_b` children per node and `NetFacts`, and a kernel kit on `KLoc (Fin 6) E` whose slots
`io, ck, cN1, cG, cB` are the named stacks `0, 1, 3, 4, 5` of the contract (stack `2`, the row
count `R`, is never read), `c5Prog kit` meets `C5InterchangeStmt q τ` with constant
`4·budgetC kit + 2`. Hypothesis `2 ≤ q` (the base of the digit fields). -/
theorem c5Interchange_of_kit (q : ℕ) (τ : ℝ) (hq2 : 2 ≤ q)
    {N : Net (tripleWb 100) (tripleM 100)} (hNF : NetFacts q N (tripleSb 100))
    {E σ : Type} [Fintype E] [DecidableEq E] [Finite σ] [Nonempty σ]
    (kit : Kit q N (KLoc (Fin 6) E) σ)
    (hio : kit.slot .io = .inl 0) (hck : kit.slot .ck = .inl 1)
    (hN1 : kit.slot .cN1 = .inl 3) (hG : kit.slot .cG = .inl 4) (hB : kit.slot .cB = .inl 5) :
    C5InterchangeStmt q τ := by
  intro hτ
  refine ⟨4 * budgetC kit + 2, fun _ => ⟨E, inferInstance, inferInstance, σ, c5Prog kit,
    inferInstance, inferInstance, closed_c5Prog kit, ?_⟩⟩
  intro k N0 R N1 G B w v rest r1 r2 r3 r4 r5 S hN0 hR hN1' hG' hB' hdiv hvlen hvw hrest
    t1 _ t3 t4 t5 e0 e1 _ e3 e4 e5
  let x : Inst (KLoc (Fin 6) E) := ⟨k, N0, R, N1, G, B, w, v, rest, S⟩
  have hx : Pre kit x := by
    refine ⟨hN0, hR, hN1', hG', hB', hdiv, ?_, hvw, hrest, ?_, ?_⟩
    · show v.length = N0 * R * rowSize q (tripleM 100) k N1 G B
      rw [hvlen, rowSize]
      ring
    · show S (kit.slot .io) = arrSyms v ++ rest
      rw [hio]
      exact e0
    · exact ⟨r1, r3, r4, r5, t1, t3, t4, t5, by rw [hck]; exact e1, by rw [hN1]; exact e3,
        by rw [hG]; exact e4, by rw [hB]; exact e5⟩
  have hW : 0 < tripleWb 100 := by rw [S1.tripleWb_100]; norm_num
  have hm : 2 ≤ tripleM 100 := by rw [S1.tripleM_100]; norm_num
  have h := kit_runs kit hq2 hm hW (tripleSb 100) hNF x hx
  have hpost : post kit x = Function.update S (.inl 0) (arrSyms (permByInv
      (swapFieldsInv (q ^ (tripleM 100 ^ k)) G (q ^ (tripleM 100 ^ k)) B) v) ++ rest) := by
    show Function.update S (kit.slot .io) _ = _
    rw [hio]
    rfl
  rw [hpost] at h
  have hdivV : tripleWb 100 ^ k ∣ vol v := by
    rw [vol_of_widths v w hvw, hvlen]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hdiv _) _) _) _) _) _) _
  exact RunsIn.iff_runs.1 (RunsIn.mono (RunsIn.iff_runs.2 h) (fun _ _ => trivial)
    (powBudget_le_c5 hτ hdivV))

end SubNLogN.Machine.C5
