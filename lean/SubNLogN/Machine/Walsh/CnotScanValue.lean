/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanRec
import SubNLogN.Machine.Walsh.CnotLeaf

/-!
# `SubNLogN.Machine.Walsh.CnotScanValue`: value level of the CNOT-batch scans (pure)

Paper: Section 5.1 eq. (`eq:walsh-SU`) and Lemma 5.1 (`lem:walsh-select`) (`S_U`, the scalar `2^s[2(1-i)]^{q_sel}`),
Section 5.2 eq. (`eq:walsh-CZ`) (`CZ`), and Proposition 5.5 (`prop:cnot-batch`, `×2^s`).

**Scope (honest summary).** Pure lemmas, all proved (no `sorry`):
* `outCoefBits_twosBits`: the engine's output coefficient is `coefBits W (cZ e mu k · (a, b))`,
  `cZ e mu k = 2^e · i^k · (1 - i)^μ` (Gaussian integers, `cmulC`);
* `gridInt_mul_toC`: on the `F`-grid, multiplying by a Gaussian integer multiplies the stored
  numerators (`cmulC`);
* `encCube_scale`: the stored array of a recordwise Gaussian-integer diagonal is the indexed
  map of the stored array; `arrSyms_outRecs`: the engine's output records are its encoding.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- The Gaussian factor `2^e · i^k · (1 - i)^μ`. -/
def cZ (e : ℕ) (mu : Bool) (k : Fin 4) : CInt := cmulC ((2 : ℤ) ^ e, 0) (gfacZ mu k)

theorem cmulC_assoc (p q c : CInt) : cmulC (cmulC p q) c = cmulC p (cmulC q c) := by
  simp only [cmulC]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem outBits_twosBits (mu : Bool) (k : Fin 4) (im : Bool) (W e : ℕ) (a b : ℤ) :
    outBits mu k im (W - min e W) (min e W) (twosBits W a) (twosBits W b) =
      twosBits W (specVal (fieldSpec mu k im) a b * 2 ^ e) := by
  rw [outBits, rip2_twosBits, twosBits_shift]
  rfl

theorem outCoefBits_twosBits (mu : Bool) (k : Fin 4) (W e : ℕ) (a b : ℤ) :
    outCoefBits mu k (W - min e W) (min e W) (twosBits W a) (twosBits W b) =
      coefBits W (cmulC (cZ e mu k) (a, b)) := by
  rw [outCoefBits, outBits_twosBits, outBits_twosBits, cZ, cmulC_assoc, cmulC_gfacZ, coefBits]
  simp only [cmulC]
  congr 2 <;> ring

/-! ## Grid values -/

/-- A Gaussian integer as a complex number. -/
noncomputable def toC (c : CInt) : ℂ := ⟨(c.1 : ℝ), (c.2 : ℝ)⟩

theorem round_intCast_mul_unit (n : ℤ) (F : ℕ) :
    round ((n : ℝ) * gridUnit F * 2 ^ F) = n := by
  have h : (n : ℝ) * gridUnit F * 2 ^ F = n := by
    rw [gridUnit, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  rw [h, round_intCast]

/-- **Exact Gaussian scaling on the grid.** -/
theorem gridInt_mul_toC {F : ℕ} {v : ℂ} (hv : OnGrid F v) (c : CInt) :
    gridInt F (toC c * v) = cmulC c (gridInt F v) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hv
  have hre : (toC c * v).re = ((c.1 * a - c.2 * b : ℤ) : ℝ) * gridUnit F := by
    simp only [toC, Complex.mul_re, ha, hb]
    push_cast
    ring
  have him : (toC c * v).im = ((c.1 * b + c.2 * a : ℤ) : ℝ) * gridUnit F := by
    simp only [toC, Complex.mul_im, ha, hb]
    push_cast
    ring
  simp only [gridInt, hre, him, ha, hb, round_intCast_mul_unit, cmulC]

/-! ## Indexed maps and the engine's output -/

/-- Map with the index (starting at `x0`). -/
def imap {α β : Type} (g : ℕ → α → β) : ℕ → List α → List β
  | _, [] => []
  | x0, a :: l => g x0 a :: imap g (x0 + 1) l

theorem imap_append {α β : Type} (g : ℕ → α → β) :
    ∀ (x0 : ℕ) (l1 l2 : List α), imap g x0 (l1 ++ l2) = imap g x0 l1 ++ imap g (x0 + l1.length) l2
  | _, [], _ => by simp [imap]
  | x0, a :: l1, l2 => by
    simp only [List.cons_append, imap, List.length_cons]
    rw [imap_append g (x0 + 1) l1 l2, show x0 + 1 + l1.length = x0 + (l1.length + 1) by ring]

theorem imap_range_map {α β : Type} (g : ℕ → α → β) (F : ℕ → α) :
    ∀ n : ℕ, imap g 0 ((List.range n).map F) = (List.range n).map fun i => g i (F i)
  | 0 => by simp [imap]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, imap_append, imap_range_map g F n]
    simp [imap]

/-- The engine's input records of an array: each coefficient as its two fields. -/
def recsOf (W : ℕ) (v : List (List CInt)) : List (List (List Bool × List Bool)) :=
  v.map fun cs => cs.map fun c => (twosBits W c.1, twosBits W c.2)

theorem carrSyms_recsOf (W : ℕ) (v : List (List CInt)) :
    carrSyms W v = arrSyms ((recsOf W v).map fun cs => cs.flatMap fun c => c.1 ++ c.2) := by
  simp only [carrSyms, recsOf, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  simp only [Function.comp_apply, crecBits, List.flatMap_map]
  rfl

theorem arrSyms_outRecs (mu : Bool) (kfun : ℕ → Fin 4) (W e : ℕ) :
    ∀ (x0 : ℕ) (v : List (List CInt)),
      arrSyms (outRecs mu kfun (W - min e W) (min e W) x0 (recsOf W v)) =
        carrSyms W (imap (fun i cs => cs.map (cmulC (cZ e mu (kfun i)))) x0 v)
  | _, [] => rfl
  | x0, cs :: v => by
    have ih := arrSyms_outRecs mu kfun W e (x0 + 1) v
    simp only [recsOf, List.map_cons, outRecs, imap, carrSyms] at ih ⊢
    rw [WalshLift.arrSyms_cons, WalshLift.arrSyms_cons, ih]
    congr 2
    simp only [crecBits, List.flatMap_map]
    apply List.flatMap_congr
    intro c _
    exact outCoefBits_twosBits mu (kfun x0) W e c.1 c.2

/-- **A recordwise Gaussian-integer diagonal on the stored array.** -/
theorem encCube_scale {m r : ℕ} (F : ℕ) (f : Cube m → ℂ) (y : RArr (Cube m) r)
    (hy : ArrOnGrid F y) (cf : ℕ → CInt) (hf : ∀ i, f (cubeOfNat m i) = toC (cf i)) :
    encCube F (diagArr f y) = imap (fun i cs => cs.map (cmulC (cf i))) 0 (encCube F y) := by
  simp only [encCube, encArr, cubeAddrs, List.map_map]
  rw [imap_range_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, diagArr, hf i]
  exact gridInt_mul_toC (hy _ k) (cf i)

end SubNLogN.Machine.WalshScanAux
