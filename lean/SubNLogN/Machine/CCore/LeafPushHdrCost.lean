/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPushHdrDefs
import SubNLogN.Machine.CCore.LeafHdrVol

/-!
# C-core leaf (2): cost bound of the push-child-header kernel (`CCore/LeafPushHdrCost.lean`)

**Scope (honest summary).** `PushHdrAux.pushCost_le p`: assume the bands with cutoff `1`, a node
(`1 ≤ k`) and a slot `a < m`. Then the exact step count `costL t a` of the push program
(`CCore/LeafPushHdrDefs.lean`) is at most `C · V_g`, with
`C = 5000·(dConst p + 1)·(bitLen W + 1)·(bitLen m + 3)²`, a constant of `p` only.

Proof:
* Every bit length of a header field, parent or child, is at most `V_g`. For `d` the bound is
  `dConst p · V_g`, from `hdrFields_le_volG`. The slot offset satisfies `a·m^(k-1) ≤ m^k = e`.
* The division products `bitLen v · bitLen W` are at most `V_g · bitLen W`.
* `powCost m a (k - 1) ≤ 200·(bitLen m + 3)²·(k + 1)³ ≤ 200·(bitLen m + 3)²·V_g`.

`bitLen W` and `bitLen m` stay symbolic throughout.
-/

namespace SubNLogN.Machine.CCore.PushHdrAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability

namespace CostAux

/-! ## The field lists, explicitly -/

theorem fsP_eq (t : CCoreRT) :
    fsP t = [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ] := rfl

theorem fs4_eq (t : CCoreRT) (a : ℕ) :
    fs4 t a = [t.P, t.d, t.r, t.Δ, t.A / Wn, t.R / Wn, t.K, t.D, t.S,
      t.j0 + a * mn ^ (t.k - 1), t.k - 1, t.ρ] := rfl

/-! ## The power step -/

/-- `powCost m a (k - 1) ≤ 200 (bitLen m + 3)² (k + 1)³` for a slot `a < m`. -/
theorem powCost_mn_le {a k : ℕ} (ha : a < mn) (hk : 1 ≤ k) :
    NatArith.powCost mn a (k - 1) ≤ 200 * ((bitLen mn + 3) ^ 2 * (k + 1) ^ 3) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  unfold NatArith.powCost
  have h1 := NatArith.bitLen_mul_le' a (mn ^ k')
  have h2 := LeafHdrAux.bitLen_pow_le mn k'
  have h3 : bitLen a ≤ bitLen mn := NatArith.bitLen_mono'' ha.le
  have h4 : bitLen (a * mn ^ k') + bitLen mn + 2 ≤ (k' + 1 + 1) * (bitLen mn + 3) := by
    have e : (k' + 1 + 1) * (bitLen mn + 3) = k' * bitLen mn + 2 * bitLen mn + 3 * k' + 6 := by
      ring
    rw [e]
    omega
  calc (k' + 1) * (200 * (bitLen (a * mn ^ k') + bitLen mn + 2) ^ 2)
      ≤ (k' + 1 + 1) * (200 * ((k' + 1 + 1) * (bitLen mn + 3)) ^ 2) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 2))
    _ = 200 * ((bitLen mn + 3) ^ 2 * (k' + 1 + 1) ^ 3) := by ring

/-- The slot offset is at most the group size: `a·m^(k-1) ≤ m^k = e`. -/
theorem slot_le_e {t : CCoreRT} {a : ℕ} (ha : a < mn) (hk : 1 ≤ t.k) :
    a * mn ^ (t.k - 1) ≤ t.e := by
  have he : t.e = mn ^ t.k := rfl
  obtain ⟨k', hk'⟩ : ∃ k', t.k = k' + 1 := ⟨t.k - 1, by omega⟩
  rw [he, hk', Nat.add_sub_cancel, pow_succ]
  calc a * mn ^ k' ≤ mn * mn ^ k' := Nat.mul_le_mul_right _ ha.le
    _ = mn ^ k' * mn := Nat.mul_comm _ _

/-! ## Sums over the field lists -/

theorem set9_eq (t : CCoreRT) (x : ℕ) :
    (fsP t).set 9 x = [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, x, t.k, t.ρ] := rfl

theorem fs2_eq (t : CCoreRT) (w : ℕ) :
    fs2 t w = [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0 + w, t.k - 1, t.ρ] := rfl

theorem fs2set_eq (t : CCoreRT) (w x : ℕ) :
    (fs2 t w).set 4 x = [t.P, t.d, t.r, t.Δ, x, t.R, t.K, t.D, t.S, t.j0 + w, t.k - 1, t.ρ] :=
  rfl

/-- A sum `Σ (c·bitLen f + d)` over a list whose bit lengths are at most `U`. -/
theorem sum_map_le (c d U : ℕ) : ∀ (l : List ℕ), (∀ f ∈ l, bitLen f ≤ U) →
    (l.map fun f => c * bitLen f + d).sum ≤ l.length * (c * U + d)
  | [], _ => by simp
  | f :: l, h => by
    have h1 := h f (List.mem_cons.mpr (Or.inl rfl))
    have h2 := sum_map_le c d U l (fun g hg => h g (List.mem_cons.mpr (Or.inr hg)))
    have h3 : c * bitLen f ≤ c * U := Nat.mul_le_mul_left _ h1
    simp only [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]
    omega

/-- Every element of an explicit twelve-element list has bit length at most `U`. -/
theorem list12_le {U a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ℕ} (h0 : bitLen a0 ≤ U)
    (h1 : bitLen a1 ≤ U) (h2 : bitLen a2 ≤ U) (h3 : bitLen a3 ≤ U) (h4 : bitLen a4 ≤ U)
    (h5 : bitLen a5 ≤ U) (h6 : bitLen a6 ≤ U) (h7 : bitLen a7 ≤ U) (h8 : bitLen a8 ≤ U)
    (h9 : bitLen a9 ≤ U) (h10 : bitLen a10 ≤ U) (h11 : bitLen a11 ≤ U) :
    ∀ f ∈ [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], bitLen f ≤ U := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-! ### The ten phases of `costL`, over plain variables -/

theorem piece1 {S1 S2 bk U V : ℕ} (s1 : S1 ≤ 12 * (13 * U + 20)) (s2 : S2 ≤ 10 * (3 * U + 6))
    (hk : bk ≤ V) : (S1 + 2) + 1 + (2 * S2 + 7 * bk + 9) ≤ 216 * U + 7 * V + 372 := by
  omega

theorem piece2 {b1 bk ba PC V PM : ℕ} (h1 : b1 ≤ 1) (hk : bk ≤ V) (ha : ba ≤ PM)
    (hpow : PC ≤ 200 * PM) :
    1 + (b1 + 1) + 1 + 20 * (bk + b1 + 1) + 1 + (ba + 1) + PC ≤ 20 * V + 201 * PM + 46 := by
  omega

theorem piece3 {S3 bj U V : ℕ} (s3 : S3 ≤ 9 * (3 * U + 6)) (hj : bj ≤ V) :
    1 + (2 * S3 + 7 * bj + 9) ≤ 54 * U + 7 * V + 118 := by
  omega

theorem piece4 {bj bw V : ℕ} (hj : bj ≤ V) (hw : bw ≤ V) : 1 + 20 * (bj + bw + 1) ≤ 40 * V + 21 := by
  omega

theorem piece5 {S3 S4 bj bjw bk bk1 U V : ℕ} (s3 : S3 ≤ 9 * (3 * U + 6))
    (s4 : S4 ≤ 10 * (3 * U + 6)) (hj : bj ≤ V) (hjw : bjw ≤ V) (hk : bk ≤ V) (hk1 : bk1 ≤ V) :
    (2 * S3 + (2 * bj + 7 * bjw + 11) + 2) + (2 * S4 + (2 * bk + 7 * bk1 + 11) + 2) ≤
      114 * U + 18 * V + 254 := by
  omega

theorem piece6 {bW WV : ℕ} (hWn : bW ≤ WV) : 1 + (bW + 1) ≤ WV + 2 := by
  omega

theorem piece7 {S5 bA AW bW bAd bAm U V WV : ℕ} (s5 : S5 ≤ 4 * (3 * U + 6)) (hA : bA ≤ V)
    (hAW : AW ≤ WV) (hWn : bW ≤ WV) (hAd : bAd ≤ V) (hAm : bAm ≤ V) :
    (1 + (2 * S5 + 7 * bA + 9) + 1 + 1) + ((2 * 20 + 70) * (AW + bA + bW + 1)) +
      (2 * S5 + (2 * bA + 7 * bAd + 11) + 2) + ((2 * bAd + 2) + (2 * bAm + 2) + (2 * bA + 2)) ≤
      48 * U + 132 * V + 220 * WV + 237 := by
  omega

theorem piece8 {S6 bR RW bW bRd bRm U V WV : ℕ} (s6 : S6 ≤ 5 * (3 * U + 6)) (hR : bR ≤ V)
    (hRW : RW ≤ WV) (hWn : bW ≤ WV) (hRd : bRd ≤ V) (hRm : bRm ≤ V) :
    (1 + (2 * S6 + 7 * bR + 9) + 1 + 1) + ((2 * 20 + 70) * (RW + bR + bW + 1)) +
      (2 * S6 + (2 * bR + 7 * bRd + 11) + 2) + ((2 * bRd + 2) + (2 * bRm + 2) + (2 * bR + 2)) ≤
      60 * U + 132 * V + 220 * WV + 261 := by
  omega

theorem piece9 {S7 S8 U : ℕ} (s7 : S7 ≤ 12 * (13 * U + 20)) (s8 : S8 ≤ 12 * (2 * U + 5)) :
    (S7 + 2) + (S8 + 1) ≤ 180 * U + 303 := by
  omega

theorem piece10 {bW bjw bj bw bk1 b1 bk V WV : ℕ} (hWn : bW ≤ WV) (hjw : bjw ≤ V) (hj : bj ≤ V)
    (hw : bw ≤ V) (hk1 : bk1 ≤ V) (h1 : b1 ≤ 1) (hk : bk ≤ V) :
    (2 * bW + 2) + ((2 * bjw + 2) + ((2 * bj + 2) + ((2 * bw + 2) + ((2 * bk1 + 2) +
      ((2 * b1 + 2) + (2 * bk + 2)))))) ≤ 2 * WV + 10 * V + 16 := by
  omega

theorem piece_combo {U V WV PM : ℕ} (hV1 : 1 ≤ V) :
    (216 * U + 7 * V + 372) + ((20 * V + 201 * PM + 46) + ((54 * U + 7 * V + 118) +
      ((40 * V + 21) + ((114 * U + 18 * V + 254) + ((WV + 2) +
      ((48 * U + 132 * V + 220 * WV + 237) +
      ((60 * U + 132 * V + 220 * WV + 261) + (180 * U + 303) + (2 * WV + 10 * V + 16)))))))) ≤
    700 * U + 3000 * V + 500 * WV + 300 * PM := by
  omega

/-- **The step count over plain variables**: the shape of `costL t a` after unfolding `costL` and
`dvCost`, with every atom (list sums, bit lengths, products, the power step) a variable. -/
theorem costL_arith {S1 S2 S3 S4 S5 S6 S7 S8 bk b1 ba PC bj bw bjw bk1 bW bA AW bAd bAm bR RW bRd
    bRm U V WV PM : ℕ}
    (s1 : S1 ≤ 12 * (13 * U + 20)) (s2 : S2 ≤ 10 * (3 * U + 6)) (s3 : S3 ≤ 9 * (3 * U + 6))
    (s4 : S4 ≤ 10 * (3 * U + 6)) (s5 : S5 ≤ 4 * (3 * U + 6)) (s6 : S6 ≤ 5 * (3 * U + 6))
    (s7 : S7 ≤ 12 * (13 * U + 20)) (s8 : S8 ≤ 12 * (2 * U + 5))
    (hV1 : 1 ≤ V) (hk : bk ≤ V) (h1 : b1 ≤ 1) (ha : ba ≤ PM) (hpow : PC ≤ 200 * PM)
    (hj : bj ≤ V) (hw : bw ≤ V) (hjw : bjw ≤ V) (hk1 : bk1 ≤ V) (hWn : bW ≤ WV) (hA : bA ≤ V)
    (hAW : AW ≤ WV) (hAd : bAd ≤ V) (hAm : bAm ≤ V) (hR : bR ≤ V) (hRW : RW ≤ WV)
    (hRd : bRd ≤ V) (hRm : bRm ≤ V) :
    ((S1 + 2) + 1 +
        (2 * S2 + 7 * bk + 9)) +
    ((1 + (b1 + 1) + 1 + 20 * (bk + b1 + 1) + 1 + (ba + 1) +
        PC) +
    ((1 + (2 * S3 + 7 * bj + 9)) +
    ((1 + 20 * (bj + bw + 1)) +
    (((2 * S3 +
            (2 * bj + 7 * bjw + 11) + 2) +
          (2 * S4 + (2 * bk + 7 * bk1 + 11) + 2)) +
    ((1 + (bW + 1)) +
    ((  (1 + (2 * S5 + 7 * bA + 9) + 1 + 1) +
    ((2 * 20 + 70) * (AW + bA + bW + 1)) +
    (2 * S5 + (2 * bA + 7 * bAd + 11) + 2) +
    ((2 * bAd + 2) + (2 * bAm + 2) + (2 * bA + 2))) +
    ((  (1 + (2 * S6 + 7 * bR + 9) + 1 + 1) +
    ((2 * 20 + 70) * (RW + bR + bW + 1)) +
    (2 * S6 + (2 * bR + 7 * bRd + 11) + 2) +
    ((2 * bRd + 2) + (2 * bRm + 2) + (2 * bR + 2))) +
    ((S7 + 2) +
        (S8 + 1)) +
    ((2 * bW + 2) + ((2 * bjw + 2) + ((2 * bj + 2) +
      ((2 * bw + 2) + ((2 * bk1 + 2) + ((2 * b1 + 2) +
        (2 * bk + 2)))))))))))))) ≤
      700 * U + 3000 * V + 500 * WV + 300 * PM :=
  le_trans (Nat.add_le_add (piece1 s1 s2 hk) (Nat.add_le_add (piece2 h1 hk ha hpow)
    (Nat.add_le_add (piece3 s3 hj) (Nat.add_le_add (piece4 hj hw)
    (Nat.add_le_add (piece5 s3 s4 hj hjw hk hk1) (Nat.add_le_add (piece6 hWn)
    (Nat.add_le_add (piece7 s5 hA hAW hWn hAd hAm)
    (Nat.add_le_add (Nat.add_le_add (piece8 s6 hR hRW hWn hRd hRm) (piece9 s7 s8))
      (piece10 hWn hjw hj hw hk1 h1 hk))))))))) (piece_combo hV1)

/-- **The step count, linearised**: `costL t a` from bounds on its atoms (the header fields by `U`,
the scalar bit lengths by `V`, the division products and `bitLen W` by `WV`, the power step and
`bitLen a` by `PM`). -/
theorem costL_le_of {t : CCoreRT} {a U V WV PM : ℕ}
    (hfsP : ∀ f ∈ fsP t, bitLen f ≤ U)
    (hset9 : ∀ f ∈ (fsP t).set 9 (t.j0 + a * mn ^ (t.k - 1)), bitLen f ≤ U)
    (hfs2 : ∀ f ∈ fs2 t (a * mn ^ (t.k - 1)), bitLen f ≤ U)
    (hfs2s : ∀ f ∈ (fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn), bitLen f ≤ U)
    (hfs4 : ∀ f ∈ fs4 t a, bitLen f ≤ U)
    (hV1 : 1 ≤ V) (hk : bitLen t.k ≤ V) (h1 : bitLen 1 ≤ 1) (ha : bitLen a ≤ PM)
    (hpow : NatArith.powCost mn a (t.k - 1) ≤ 200 * PM) (hj : bitLen t.j0 ≤ V)
    (hw : bitLen (a * mn ^ (t.k - 1)) ≤ V) (hjw : bitLen (t.j0 + a * mn ^ (t.k - 1)) ≤ V)
    (hk1 : bitLen (t.k - 1) ≤ V) (hWn : bitLen Wn ≤ WV) (hA : bitLen t.A ≤ V)
    (hAW : bitLen t.A * bitLen Wn ≤ WV) (hAd : bitLen (t.A / Wn) ≤ V)
    (hAm : bitLen (t.A % Wn) ≤ V) (hR : bitLen t.R ≤ V) (hRW : bitLen t.R * bitLen Wn ≤ WV)
    (hRd : bitLen (t.R / Wn) ≤ V) (hRm : bitLen (t.R % Wn) ≤ V) :
    costL t a ≤ 700 * U + 3000 * V + 500 * WV + 300 * PM := by
  have s1 := sum_map_le 13 20 U (fsP t) hfsP
  have s2 := sum_map_le 3 6 U ((fsP t).take 10) (fun f hf => hfsP f (List.mem_of_mem_take hf))
  have s3 := sum_map_le 3 6 U ((fsP t).take 9) (fun f hf => hfsP f (List.mem_of_mem_take hf))
  have s4 := sum_map_le 3 6 U (((fsP t).set 9 (t.j0 + a * mn ^ (t.k - 1))).take 10)
    (fun f hf => hset9 f (List.mem_of_mem_take hf))
  have s5 := sum_map_le 3 6 U ((fs2 t (a * mn ^ (t.k - 1))).take 4)
    (fun f hf => hfs2 f (List.mem_of_mem_take hf))
  have s6 := sum_map_le 3 6 U (((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn)).take 5)
    (fun f hf => hfs2s f (List.mem_of_mem_take hf))
  have s7 := sum_map_le 13 20 U (fs4 t a) hfs4
  have s8 := sum_map_le 2 5 U (fs4 t a) hfs4
  have l1 : (fsP t).length = 12 := rfl
  have l2 : ((fsP t).take 10).length = 10 := rfl
  have l3 : ((fsP t).take 9).length = 9 := rfl
  have l4 : (((fsP t).set 9 (t.j0 + a * mn ^ (t.k - 1))).take 10).length = 10 := rfl
  have l5 : ((fs2 t (a * mn ^ (t.k - 1))).take 4).length = 4 := rfl
  have l6 : (((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn)).take 5).length = 5 := rfl
  have l7 : (fs4 t a).length = 12 := rfl
  rw [l1] at s1
  rw [l2] at s2
  rw [l3] at s3
  rw [l4] at s4
  rw [l5] at s5
  rw [l6] at s6
  rw [l7] at s7 s8
  unfold costL dvCost
  exact costL_arith s1 s2 s3 s4 s5 s6 s7 s8 hV1 hk h1 ha hpow hj hw hjw hk1 hWn hA hAW hAd hAm hR
    hRW hRd hRm

/-- The final combination, as a pure inequality. -/
theorem final_arith {cL DV V WV PM Q : ℕ}
    (key : cL ≤ 700 * (V + DV) + 3000 * V + 500 * WV + 300 * PM) (q1 : DV * 9 ≤ Q)
    (q2 : WV * 9 ≤ Q) (q3 : PM ≤ Q) (q4 : V * 9 ≤ Q) : cL ≤ 5000 * Q := by
  omega

end CostAux

open CostAux in
/-- **Cost of the push-child-header kernel.** Assume the bands with cutoff `1`, a node (`1 ≤ k`)
and a slot `a < m`. Then `costL t a ≤ C · V_g`, with
`C = 5000·(dConst p + 1)·(bitLen W + 1)·(bitLen m + 3)²`. -/
theorem pushCost_le (p : LayerParams) : ∃ C : ℕ, ∀ (t : CCoreRT) (a : ℕ), CCoreBands p 1 t →
    1 ≤ t.k → a < mn → costL t a ≤ C * t.volG := by
  refine ⟨5000 * (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2,
    fun t a hb hk ha => ?_⟩
  obtain ⟨hPV, hrV, hΔV, hAV, hRV, hKV, hDV, hSV, hjeV, hk3V, hρV, h1V, hdV⟩ :=
    LeafHdrAux.hdrFields_le_volG hb (le_refl 1)
  have bP := (WP.W0m.bitLen_le_self t.P).trans hPV
  have br := (WP.W0m.bitLen_le_self t.r).trans hrV
  have bΔ := (WP.W0m.bitLen_le_self t.Δ).trans hΔV
  have bA := (WP.W0m.bitLen_le_self t.A).trans hAV
  have bR := (WP.W0m.bitLen_le_self t.R).trans hRV
  have bK := (WP.W0m.bitLen_le_self t.K).trans hKV
  have bD := (WP.W0m.bitLen_le_self t.D).trans hDV
  have bS := (WP.W0m.bitLen_le_self t.S).trans hSV
  have bρ := (WP.W0m.bitLen_le_self t.ρ).trans hρV.le
  have hk3 : t.k + 1 ≤ (t.k + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have bk : bitLen t.k ≤ t.volG := (WP.W0m.bitLen_le_self _).trans (by omega)
  have bk1 : bitLen (t.k - 1) ≤ t.volG := (WP.W0m.bitLen_le_self _).trans (by omega)
  have hw := slot_le_e (t := t) ha hk
  have bw : bitLen (a * mn ^ (t.k - 1)) ≤ t.volG := (WP.W0m.bitLen_le_self _).trans (by omega)
  have bj : bitLen t.j0 ≤ t.volG := (WP.W0m.bitLen_le_self _).trans (by omega)
  have bjw : bitLen (t.j0 + a * mn ^ (t.k - 1)) ≤ t.volG :=
    (WP.W0m.bitLen_le_self _).trans (by omega)
  have bAd : bitLen (t.A / Wn) ≤ t.volG :=
    (NatArith.bitLen_mono'' (Nat.div_le_self _ _)).trans bA
  have bRd : bitLen (t.R / Wn) ≤ t.volG :=
    (NatArith.bitLen_mono'' (Nat.div_le_self _ _)).trans bR
  have bAm : bitLen (t.A % Wn) ≤ t.volG :=
    (WP.W0m.bitLen_le_self _).trans ((Nat.mod_le _ _).trans hAV)
  have bRm : bitLen (t.R % Wn) ≤ t.volG :=
    (WP.W0m.bitLen_le_self _).trans ((Nat.mod_le _ _).trans hRV)
  have bd : bitLen t.d ≤ LeafHdrAux.dConst p * t.volG := by
    have h := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (bitLen t.d + 1)
    omega
  have b1 : bitLen 1 ≤ 1 := WP.W0m.bitLen_le_self 1
  have ba : bitLen a ≤ bitLen mn := NatArith.bitLen_mono'' ha.le
  have hAW : bitLen t.A * bitLen Wn ≤ t.volG * bitLen Wn := Nat.mul_le_mul_right _ bA
  have hRW : bitLen t.R * bitLen Wn ≤ t.volG * bitLen Wn := Nat.mul_le_mul_right _ bR
  have hpow : NatArith.powCost mn a (t.k - 1) ≤ 200 * ((bitLen mn + 3) ^ 2 * t.volG) :=
    (powCost_mn_le ha hk).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk3V))
  have hmnPM : bitLen a ≤ (bitLen mn + 3) ^ 2 * t.volG := by
    have h1 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (bitLen mn + 3)
    have h2 : (bitLen mn + 3) ^ 2 ≤ (bitLen mn + 3) ^ 2 * t.volG :=
      Nat.le_mul_of_pos_right _ h1V
    omega
  have hWnWV : bitLen Wn ≤ t.volG * bitLen Wn := Nat.le_mul_of_pos_left _ h1V
  -- the uniform field bound `U = V_g + dConst p · V_g`
  have uV : t.volG ≤ t.volG + LeafHdrAux.dConst p * t.volG := Nat.le_add_right _ _
  have uD : LeafHdrAux.dConst p * t.volG ≤ t.volG + LeafHdrAux.dConst p * t.volG :=
    Nat.le_add_left _ _
  have m1 : ∀ f ∈ fsP t, bitLen f ≤ t.volG + LeafHdrAux.dConst p * t.volG := by
    rw [fsP_eq]
    exact list12_le (bP.trans uV) (bd.trans uD) (br.trans uV) (bΔ.trans uV) (bA.trans uV)
      (bR.trans uV) (bK.trans uV) (bD.trans uV) (bS.trans uV) (bj.trans uV) (bk.trans uV)
      (bρ.trans uV)
  have m2 : ∀ f ∈ (fsP t).set 9 (t.j0 + a * mn ^ (t.k - 1)),
      bitLen f ≤ t.volG + LeafHdrAux.dConst p * t.volG := by
    rw [set9_eq]
    exact list12_le (bP.trans uV) (bd.trans uD) (br.trans uV) (bΔ.trans uV) (bA.trans uV)
      (bR.trans uV) (bK.trans uV) (bD.trans uV) (bS.trans uV) (bjw.trans uV) (bk.trans uV)
      (bρ.trans uV)
  have m3 : ∀ f ∈ fs2 t (a * mn ^ (t.k - 1)),
      bitLen f ≤ t.volG + LeafHdrAux.dConst p * t.volG := by
    rw [fs2_eq]
    exact list12_le (bP.trans uV) (bd.trans uD) (br.trans uV) (bΔ.trans uV) (bA.trans uV)
      (bR.trans uV) (bK.trans uV) (bD.trans uV) (bS.trans uV) (bjw.trans uV) (bk1.trans uV)
      (bρ.trans uV)
  have m4 : ∀ f ∈ (fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn),
      bitLen f ≤ t.volG + LeafHdrAux.dConst p * t.volG := by
    rw [fs2set_eq]
    exact list12_le (bP.trans uV) (bd.trans uD) (br.trans uV) (bΔ.trans uV) (bAd.trans uV)
      (bR.trans uV) (bK.trans uV) (bD.trans uV) (bS.trans uV) (bjw.trans uV) (bk1.trans uV)
      (bρ.trans uV)
  have m5 : ∀ f ∈ fs4 t a, bitLen f ≤ t.volG + LeafHdrAux.dConst p * t.volG := by
    rw [fs4_eq]
    exact list12_le (bP.trans uV) (bd.trans uD) (br.trans uV) (bΔ.trans uV) (bAd.trans uV)
      (bRd.trans uV) (bK.trans uV) (bD.trans uV) (bS.trans uV) (bjw.trans uV) (bk1.trans uV)
      (bρ.trans uV)
  have key := costL_le_of (t := t) (a := a) (U := t.volG + LeafHdrAux.dConst p * t.volG)
    (V := t.volG) (WV := t.volG * bitLen Wn) (PM := (bitLen mn + 3) ^ 2 * t.volG)
    m1 m2 m3 m4 m5 h1V bk b1 hmnPM hpow bj bw bjw bk1 hWnWV bA hAW bAd bAm bR hRW bRd bRm
  have hm9 : 9 ≤ (bitLen mn + 3) ^ 2 := by
    have h3 : 3 ≤ bitLen mn + 3 := by omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (bitLen mn + 3) ^ 2 := Nat.pow_le_pow_left h3 2
  have q1 : LeafHdrAux.dConst p * t.volG * 9 ≤
      (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG := by
    calc LeafHdrAux.dConst p * t.volG * 9 = LeafHdrAux.dConst p * 1 * 9 * t.volG := by ring
      _ ≤ (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hm9)
  have q2 : t.volG * bitLen Wn * 9 ≤
      (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG := by
    calc t.volG * bitLen Wn * 9 = 1 * bitLen Wn * 9 * t.volG := by ring
      _ ≤ (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hm9)
  have q3 : (bitLen mn + 3) ^ 2 * t.volG ≤
      (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG := by
    calc (bitLen mn + 3) ^ 2 * t.volG = 1 * 1 * (bitLen mn + 3) ^ 2 * t.volG := by ring
      _ ≤ (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl)
  have q4 : t.volG * 9 ≤
      (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG := by
    calc t.volG * 9 = 1 * 1 * 9 * t.volG := by ring
      _ ≤ (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hm9)
  have hC : 5000 * (LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG =
      5000 * ((LeafHdrAux.dConst p + 1) * (bitLen Wn + 1) * (bitLen mn + 3) ^ 2 * t.volG) := by
    ring
  rw [hC]
  exact final_arith key q1 q2 q3 q4

end SubNLogN.Machine.CCore.PushHdrAux
