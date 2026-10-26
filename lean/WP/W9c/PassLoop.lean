import WP.W9c.PassBlock2
import WP.W7k2.Arith

/-!
# WP.W9c.PassLoop — the block loop of a pass

`ht_loop`: by induction on the fuel of `chunks`, the `whileTop` block loop runs every block
(`ht_block`) and leaves the final window `(emitFold …).1` and all emitted buckets
`(emitFold …).2` on the tape. Cost: `nb·(blockK + 2) + 2 + C·(Bc+1)·(p + nb·W)`; the wrap terms
telescope through the cursor bound `cycAdd_cursor`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-! ## Pure facts -/

/-- Final window and emitted buckets of a sequence of window steps. -/
def emitFold (W : ℕ) : List ℤ → List (List ℤ) → List ℤ × List ℤ
  | ws, [] => (ws, [])
  | ws, ds :: dss => ((emitFold W (winStep W ws ds).2 dss).1,
      (winStep W ws ds).1 ++ (emitFold W (winStep W ws ds).2 dss).2)

theorem emitAll_eq_fold (W : ℕ) : ∀ (dss : List (List ℤ)) (ws : List ℤ),
    emitAll W ws dss = (emitFold W ws dss).2 ++ (emitFold W ws dss).1
  | [], ws => rfl
  | ds :: dss, ws => by
    simp only [emitAll, emitFold, List.append_assoc]
    rw [emitAll_eq_fold W dss]

theorem winStep_snd_length (W : ℕ) (ws ds : List ℤ) (hds : W ≤ ds.length)
    (hds2 : ds.length ≤ 2 * W) : (winStep W ws ds).2.length = W := by
  simp [winStep]; omega

/-- The cursor stays in `[0, r]` and the wraps telescope. -/
theorem cycAdd_cursor (r : ℕ) (hr : 0 < r) : ∀ (vs cells : List ℤ) (p : ℕ), p ≤ r →
    (cycAdd r cells p vs).2 ≤ r ∧
      (p + vs.length - 1) / r * r + (cycAdd r cells p vs).2 ≤ p + vs.length
  | [], cells, p, hp => by
    refine ⟨hp, ?_⟩
    have h0 : (p + 0 - 1) / r = 0 := Nat.div_eq_of_lt (by omega)
    simp only [cycAdd, List.length_nil]
    rw [h0]; omega
  | v :: vs, cells, p, hp => by
    simp only [cycAdd, List.length_cons]
    by_cases hpr : p = r
    · rw [if_pos hpr]
      obtain ⟨h1, h2⟩ := cycAdd_cursor r hr vs
        (cells.set 0 (cells.getD 0 0 + v)) (0 + 1) (by omega)
      refine ⟨h1, ?_⟩
      have e : p + (vs.length + 1) - 1 = vs.length + r := by omega
      have e2 : 0 + 1 + vs.length - 1 = vs.length := by omega
      rw [e2] at h2
      rw [e, Nat.add_div_right _ hr, Nat.add_mul, Nat.one_mul]
      omega
    · rw [if_neg hpr]
      obtain ⟨h1, h2⟩ := cycAdd_cursor r hr vs
        (cells.set p (cells.getD p 0 + v)) (p + 1) (by omega)
      refine ⟨h1, ?_⟩
      have e : p + (vs.length + 1) - 1 = p + 1 + vs.length - 1 := by omega
      rw [e]; omega

theorem chunks_nil (W : ℕ) : ∀ n, chunks W n [] = []
  | 0 => rfl
  | _ + 1 => rfl

theorem chunks_cons (W n : ℕ) (v : List ℤ) (hv : v ≠ []) :
    chunks W (n + 1) v = v.take W :: chunks W n (v.drop W) := by
  cases v with
  | nil => exact absurd rfl hv
  | cons x xs => rfl

/-! ## Cost -/

/-- The block-independent part of a block's cost. -/
def blockK (C : ℕ) (Mul : ℕ → ℕ) (k p_in q W ol wd Bin Bd Bv Bc : ℕ) : ℕ :=
  C * (W * (Bin + k + p_in + q + 1) + bitLen W + 1) + (C * Mul wd + C) + 1 + C * (wd + 1) +
    C * (2 * wd + ol * (k + 1) + 1) + C * (W * (Bd + 1) + 1) + C * (W * (Bv + Bc + 1) + 1)

theorem blockT_le (C : ℕ) (Mul : ℕ → ℕ) (nv k p_in q W ol wd Bin Bd Bv Bc p r lPf lP : ℕ)
    (hnv : nv ≤ W) (hPf : lPf ≤ wd) (hP : lP ≤ 2 * wd) :
    blockT C Mul nv k p_in q W ol wd Bin Bd Bv Bc p r lPf lP ≤
      blockK C Mul k p_in q W ol wd Bin Bd Bv Bc + C * (Bc + 1) * ((p + W - 1) / r * r) := by
  have h1 : blockT C Mul nv k p_in q W ol wd Bin Bd Bv Bc p r lPf lP ≤
      blockT C Mul W k p_in q W ol wd Bin Bd Bv Bc p r wd (2 * wd) := by
    unfold blockT
    gcongr
  refine h1.trans (le_of_eq ?_)
  unfold blockT blockK
  ring

/-- Loop cost. -/
def loopT (C : ℕ) (Mul : ℕ → ℕ) (k p_in q W ol wd Bin Bd Bv Bc nb p : ℕ) : ℕ :=
  nb * (blockK C Mul k p_in q W ol wd Bin Bd Bv Bc + 2) + 2 + C * (Bc + 1) * (p + nb * W)

#assert_std_axioms emitAll_eq_fold winStep_snd_length cycAdd_cursor chunks_nil chunks_cons
  blockT_le

end WP.W9c
