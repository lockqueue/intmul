/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarRowDefs
import SubNLogN.Machine.CCore.LeafPhaseCost

/-!
# Scalar row leaf: the cost bound (`CCore/LeafScalarRowCost.lean`)

**Scope (honest summary).** Pure arithmetic, all proved (no `sorry`):
* `termCost_le`: `termCost t.wg V Cacc ≤ (42 + 6·Cacc)·volG` when `V ≤ 2·volG`;
* `tgtCost_le`: `tgtCost t.wg V Cacc k ≤ 40·volG + k·((42 + 6·Cacc)·volG)`;
* `sum_le_of_le`: summing such per-role bounds over a list of roles;
* `rowCost_le`: the scalar-row program costs at most
  `(950 + 19·Cd p + 40·W + Nmax·(42 + 6·Cacc))·volG`, for `L.length ≤ W` target roles with at
  most `Nmax` terms in total. It uses the header bound `≤ 600·volG + 19·Cd p·volG`, the width
  counter `≤ 300·volG`, the counter drop `≤ 40·volG` (`LeafPhaseCost.lean`) and the floors
  `10 ≤ 10·volG`. `W` is a generic number (not the closed `Wn`).
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowCost

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.CCore.LeafScalarAux
  SubNLogN.Machine.CCore.LeafScalarRowAux

/-- One term costs `O(volG)`. -/
theorem termCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (Cacc V : ℕ)
    (hV : V ≤ 2 * t.volG) : termCost t.wg V Cacc ≤ (42 + 6 * Cacc) * t.volG := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hw, -⟩ := fields_le hb
  have h1 : Cacc * (V + V + t.wg + 1) ≤ Cacc * (6 * t.volG) := Nat.mul_le_mul_left _ (by omega)
  have e : (42 + 6 * Cacc) * t.volG = 42 * t.volG + Cacc * (6 * t.volG) := by ring
  unfold termCost
  rw [e]
  omega

/-- One target role with `k` terms costs `40·volG` plus `k` terms. -/
theorem tgtCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (Cacc V k : ℕ)
    (hV : V ≤ 2 * t.volG) :
    tgtCost t.wg V Cacc k ≤ 40 * t.volG + k * ((42 + 6 * Cacc) * t.volG) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := fields_le hb
  have h1 : k * termCost t.wg V Cacc ≤ k * ((42 + 6 * Cacc) * t.volG) :=
    Nat.mul_le_mul_left _ (termCost_le hb Cacc V hV)
  unfold tgtCost
  omega

/-- Summing per-role bounds `f k ≤ a + k·K` over a list of roles with term counts `n`. -/
theorem sum_le_of_le {W : ℕ} (f : ℕ → ℕ) (a K : ℕ) (hf : ∀ k, f k ≤ a + k * K)
    (n : Fin W → ℕ) : ∀ L : List (Fin W),
      (L.map fun u => f (n u)).sum ≤ L.length * a + (L.map n).sum * K
  | [] => by simp
  | u :: L => by
    have ih := sum_le_of_le f a K hf n L
    have h := hf (n u)
    have e1 : (L.length + 1) * a = L.length * a + a := by ring
    have e2 : (n u + (L.map n).sum) * K = n u * K + (L.map n).sum * K := by ring
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [e1, e2]
    omega

/-- **The cost bound of the scalar-row program.** -/
theorem rowCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) {W : ℕ}
    (L : List (Fin W)) (n : Fin W → ℕ) (Nmax Cacc V : ℕ) (hL : L.length ≤ W)
    (hN : (L.map n).sum ≤ Nmax) (hV : V ≤ 2 * t.volG) :
    hdrCost t + wgCost t + (psS.length + 1) + ((L.map fun u => tgtCost t.wg V Cacc (n u)).sum +
      (psS.length + 1 + dropCost t)) ≤
      (950 + 19 * Cd p + 40 * W + Nmax * (42 + 6 * Cacc)) * t.volG := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := fields_le hb
  have hh := hdrCost_le hb
  have hw := wgCost_le hb
  have hd := dropCost_le hb
  have hs := sum_le_of_le (tgtCost t.wg V Cacc) (40 * t.volG) ((42 + 6 * Cacc) * t.volG)
    (fun k => tgtCost_le hb Cacc V k hV) n L
  have h1 : L.length * (40 * t.volG) ≤ W * (40 * t.volG) := Nat.mul_le_mul_right _ hL
  have h2 : (L.map n).sum * ((42 + 6 * Cacc) * t.volG) ≤ Nmax * ((42 + 6 * Cacc) * t.volG) :=
    Nat.mul_le_mul_right _ hN
  have hps : psS.length = 4 := rfl
  have e : (950 + 19 * Cd p + 40 * W + Nmax * (42 + 6 * Cacc)) * t.volG =
      950 * t.volG + 19 * (Cd p * t.volG) + W * (40 * t.volG) +
        Nmax * ((42 + 6 * Cacc) * t.volG) := by ring
  rw [e]
  omega

end SubNLogN.Machine.CCore.LeafScalarRowCost
