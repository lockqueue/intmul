/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanLoop

/-!
# Layer driver phase scan, proved (`Machine/Layer/DrvPhaseScan.lean`)

**Result.** `SubNLogN.Machine.Layer.drvPhaseScan_holds : DrvPhaseScanStmt`
(`Machine/Layer/DrvPhaseDefs.lean:63`; Lemma A.5 (`lem:transfer-long-record`),
Section A.6 (`sec:transfer-layer`)), with exponent `J = 2` and constant
`C = 400`. Nothing is assumed beyond the statement's own guards; no `sorry`.

## The kernel (`phaseProg`, files `DrvPhaseScan{Math,Step,Coef,Addr,Rec,Setup,Main,Loop}.lean`)
* Set-up: the header fields go to eight private counters (header restored); `y := 0`,
  `r := S - 1` (`y = x / S`, `r = S - 1 - x mod S` for the current record `x`).
* Per record: the exponent `e = (c + selCount S K ρ D x) mod 4` by a counter scan of the bits of
  `y` (no division); per coefficient a bit-serial signed adder of `w2` steps computes
  `i^e·z` (times `1 - i` if `o = 1`) from the two `w1`-bit fields (sign extension / truncation);
  outputs are staged, reversed, on a private stack; the counters are updated.
* End: the staged outputs are moved back onto the array; the counters are dropped.

## Cost
Per coefficient `O(w1 + w2)` (paid by `V_in + V_out`), per record `O((bitLen N + |hdr|)^2)`
(the exponent scan), set-up and clean-up `O(|hdr| + V_out + bitLen N)`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

theorem length_hdrSyms (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have e : (natSyms f).length = bitLen f := by simp [natSyms]; rfl
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.length_singleton] at ih ⊢
    rw [ih, e]
    simp only [List.map_cons, List.sum_cons]

theorem bitLen_add_le' (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  rw [TMFw.W3s.bitLen_le_iff]
  have ha := TMFw.W3s.lt_two_pow_bitLen a
  have hb := TMFw.W3s.lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem map_length_mapIdx : ∀ (v : List (List CInt)) (g : ℕ → List CInt → List CInt),
    (∀ i a, (g i a).length = a.length) → (v.mapIdx g).map List.length = v.map List.length
  | [], _, _ => rfl
  | a :: v, g, hg => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons, hg,
      map_length_mapIdx v (fun i => g (i + 1)) (fun i b => hg (i + 1) b)]

theorem cvol_phase (S K ρ D c o w : ℕ) (v : List (List CInt)) :
    (carrSyms w (v.mapIdx (phaseRec S K ρ D c o))).length = cvol w v := by
  have h1 : (carrSyms w (v.mapIdx (phaseRec S K ρ D c o))).length =
      cvol w (v.mapIdx (phaseRec S K ρ D c o)) := rfl
  rw [h1, SubNLogN.Machine.cvol_eq, SubNLogN.Machine.cvol_eq, List.length_mapIdx]
  congr 2
  unfold ncoef
  rw [map_length_mapIdx v _ (fun i a => by simp [phaseRec])]

/-- Record costs are bounded uniformly (records `x < N`). -/
theorem loopB_le (S K ρ D w1 w2 N Rb : ℕ)
    (hRb : ∀ x a, x < N → recCost S K ρ D w1 w2 x a ≤ Rb + a.length * (coefCost w1 w2 + 2)) :
    ∀ (vs : List (List CInt)) (x : ℕ), x + vs.length ≤ N →
      K1.loopB (recCost S K ρ D w1 w2) x vs ≤
        vs.length * (Rb + 1) + ncoef vs * (coefCost w1 w2 + 2) + 1
  | [], _, _ => by simp [K1.loopB]
  | a :: vs, x, h => by
    have h1 := hRb x a (by simp at h; omega)
    have h2 := loopB_le S K ρ D w1 w2 N Rb hRb vs (x + 1) (by simp at h; omega)
    simp only [K1.loopB, List.length_cons, ncoef, List.map_cons, List.sum_cons] at h2 ⊢
    nlinarith [h1, h2]

/-- The final cost arithmetic (all quantities as plain variables). -/
theorem cost_arith (hdrC bS LB R1 Q b1 b2 dropC A B N X H L : ℕ)
    (h1 : hdrC ≤ 20 * H + 1) (h2 : bS ≤ H) (h3 : LB ≤ R1 + Q + 1) (h4 : R1 ≤ 80 * (N * X))
    (h5 : Q ≤ 122 * A + 28 * B) (h6 : b1 ≤ L) (h7 : b2 ≤ H) (h8 : dropC ≤ 2 * H + 1)
    (h9 : L + H + 1 ≤ X) :
    hdrC + 13 * bS + 20 + (1 + (LB + (3 * B + 2 * b1 + 2 * b2 + dropC + 6))) ≤
      400 * (A + B + (N + 1) * X) := by
  rw [Nat.add_mul, Nat.one_mul]
  generalize N * X = P at h4 ⊢
  omega

/-- **The cost bound** of the whole run. -/
theorem phaseCost_le (S K ρ D c o w1 w2 : ℕ) (v : List (List CInt)) (hS1 : 1 ≤ S)
    (hw1 : 1 ≤ w1) :
    phaseCost S K ρ D c o w1 w2 v ≤ 400 * (cvol w1 v + cvol w2 v + (v.length + 1) *
      (bitLen v.length + (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length + 1) ^ 2) := by
  have hH : (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length = bitLen S + bitLen K + bitLen ρ +
      bitLen D + bitLen c + bitLen o + bitLen w1 + bitLen w2 + 8 := by
    rw [length_hdrSyms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hhdr : hdrCost [S, K, ρ, D, c, o, w1, w2] ≤
      20 * (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length + 1 := by
    rw [hH]
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hdrop : dropCost [S, K, ρ, D, c, o, w1, w2] ≤
      2 * (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length + 1 := by
    rw [hH]
    simp only [dropCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hS : bitLen S ≤ (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length := by rw [hH]; omega
  have hM : bitLen (ρ + K + D) ≤ (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length := by
    have h1 := bitLen_add_le' (ρ + K) D
    have h2 := bitLen_add_le' ρ K
    rw [hH]
    omega
  have hcoef : ncoef v * (coefCost w1 w2 + 2) ≤ 122 * cvol w1 v + 28 * cvol w2 v := by
    rw [SubNLogN.Machine.cvol_eq w1 v, SubNLogN.Machine.cvol_eq w2 v]
    unfold coefCost
    have e : ncoef v * (80 * w1 + 50 * w2 + 80 + 2) =
        80 * (w1 * ncoef v) + 50 * (w2 * ncoef v) + 82 * ncoef v := by ring
    have e1 : 2 * w1 * ncoef v = 2 * (w1 * ncoef v) := by ring
    have e2 : 2 * w2 * ncoef v = 2 * (w2 * ncoef v) := by ring
    have hn : ncoef v ≤ w1 * ncoef v := Nat.le_mul_of_pos_left _ hw1
    rw [e, e1, e2]
    generalize w1 * ncoef v = P1 at hn ⊢
    generalize w2 * ncoef v = P2
    omega
  have hb2 : bitLen (S - 1 - v.length % S) ≤ (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length :=
    (TMFw.W3s.bitLen_mono (show S - 1 - v.length % S ≤ S by omega)).trans hS
  have hb1 : bitLen (v.length / S) ≤ bitLen v.length := TMFw.W3s.bitLen_mono (Nat.div_le_self _ _)
  unfold phaseCost
  rw [cvol_phase]
  generalize hHd : (hdrSyms [S, K, ρ, D, c, o, w1, w2]).length = H at hhdr hdrop hS hM hb2 ⊢
  generalize hLd : bitLen v.length = L at hb1 ⊢
  have hRb : ∀ x a, x < v.length → recCost S K ρ D w1 w2 x a ≤
      ((L + 1) * (19 * H + 40) + 6 * L + 13 * H + 33) + a.length * (coefCost w1 w2 + 2) := by
    intro x a hx
    have e1 : bitLen (x / S) ≤ L := by
      rw [← hLd]; exact TMFw.W3s.bitLen_mono (by have := Nat.div_le_self x S; omega)
    have e2 : bitLen x ≤ L := by rw [← hLd]; exact TMFw.W3s.bitLen_mono (by omega)
    have e3 : addrCost (bitLen (x / S)) (bitLen (ρ + K + D)) ≤ (L + 1) * (19 * H + 40) := by
      unfold addrCost
      exact Nat.mul_le_mul (by omega) (by omega)
    unfold recCost
    generalize addrCost (bitLen (x / S)) (bitLen (ρ + K + D)) = T0 at e3 ⊢
    generalize (L + 1) * (19 * H + 40) = T1 at e3 ⊢
    generalize a.length * (coefCost w1 w2 + 2) = Q
    omega
  have hloop := loopB_le S K ρ D w1 w2 v.length _ hRb v 0 (by simp)
  have hX1 : L + H + 1 ≤ (L + H + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hR : (L + 1) * (19 * H + 40) + 6 * L + 13 * H + 33 + 1 ≤ 80 * (L + H + 1) ^ 2 := by
    have hR1 : (L + 1) * (19 * H + 40) ≤ (L + H + 1) * (40 * (L + H + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hR2 : (L + H + 1) * (40 * (L + H + 1)) = 40 * (L + H + 1) ^ 2 := by ring
    rw [hR2] at hR1
    generalize (L + 1) * (19 * H + 40) = T1 at hR1 ⊢
    generalize (L + H + 1) ^ 2 = X at hR1 hX1 ⊢
    omega
  have hNR : v.length * ((L + 1) * (19 * H + 40) + 6 * L + 13 * H + 33 + 1) ≤
      80 * (v.length * (L + H + 1) ^ 2) := by
    calc v.length * ((L + 1) * (19 * H + 40) + 6 * L + 13 * H + 33 + 1)
        ≤ v.length * (80 * (L + H + 1) ^ 2) := Nat.mul_le_mul_left _ hR
      _ = 80 * (v.length * (L + H + 1) ^ 2) := by ring
  exact cost_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhdr hS hloop hNR hcoef hb1 hb2 hdrop hX1

end SubNLogN.Machine.Layer.DrvPhaseScanAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Layer.DrvPhaseScanAux

/-- **Driver phase scan, proved** (`DrvPhaseScanStmt`, `Machine/Layer/DrvPhaseDefs.lean:63`;
Lemma A.5 (`lem:transfer-long-record`), Section A.6 (`sec:transfer-layer`)). The kernel
`phaseProg` replaces record `x` of the array by `phaseRec S K ρ D c o x` of itself at width
`w2` (in place, header restored, all private stacks restored), within
`400·(V_in + V_out + (N + 1)·(bitLen N + |hdr| + 1)^2)` steps (exponent `J = 2`), under exactly
the statement's guards (`1 ≤ S`, `ρ < K`, `o ≤ 1`, `1 ≤ w1`, inputs fit `w1`, `BlkTerm rest`; the
guards `1 ≤ w2`, "outputs fit `w2`" and `TermOK rp` are not needed). -/
theorem drvPhaseScan_holds : DrvPhaseScanStmt := by
  refine ⟨2, 400, fun _ => ⟨Scr, inferInstance, inferInstance, PReg, phaseProg, inferInstance,
    ⟨(none, none, none, none)⟩, closed_phaseProg, ?_⟩⟩
  intro S K ρ D c o w1 w2 v rest rp St hS1 hρK ho hw1 _hw2 hfit1 _hfit2 hrest _hrp hA hH
  exact WP.W9comp.runs_mono (runs_phaseProg St S K ρ D c o w1 w2 hS1 hρK ho hw1 v rest rp hfit1
    hrest hA hH) (fun _ h => h) (phaseCost_le S K ρ D c o w1 w2 v hS1 hw1)

end SubNLogN.Machine.Layer
