/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.AppC
import SubNLogN.Math.Networks.AppCShear
import SubNLogN.Math.Networks.AppCModel

/-!
# Correspondence of Appendix A machine targets with pure-network semantics (`Machine/AppC/Corr.lean`)

(`Machine/AppC` and `C5`/`C6`/`C7` retain earlier draft numbering for identifier stability;
they correspond to Appendix A (`app:parameter-transfer`), Proposition A.7, Lemma A.8, and Lemma A.9.)
* Proved: the coordinate form of the two index maps of `Contracts/AppC.lean`.
  * `swapFieldsInv_coord`: on coordinates, `swapFieldsInv Hh G Hd B` is the inverse map of
    `(a, h, g, d, z) ↦ (a, d, g, h, z)` (Proposition A.7 (`prop:transfer11`), Lemma A.8 (`lem:transfer12`)).
  * `c7Slot_rank`, `packedXorAddr_rank`, `packedXorAddr_corr`: on the Lemma A.9 (`lem:transfer13`)
    rectangle, `packedXorAddr` updates only the `y` slot to `packedT0 K ρ (f + 1)` (all `f` selected
    bits, `Math/Networks/AppCShear.lean`), leaving spectator coordinates unchanged.
* Interface proposition (`def SwapBlocksCorrStmt : Prop`, stated without proof in this file):
  `permByInv (swapFieldsInv …)` on the lexicographic record list equals `Model.Step.swapBlocks`
  (`Math/Networks/AppCModel.lean`) on an arbitrary `Layout` (for `nodeLayout`, see `C5NetSimSteps.lean`).
-/

namespace SubNLogN.Machine.AppC.Corr

open SubNLogN.Machine SubNLogN.Math.Networks

/-! ## Arithmetic helper -/

/-- Quotient and remainder of `q·B + r` by `B` when `r < B`. -/
theorem divmod_aux {q r B : ℕ} (hr : r < B) : (q * B + r) / B = q ∧ (q * B + r) % B = r := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-! ## Proposition A.7 and Lemma A.8: the field interchange on coordinates -/

/-- **`swapFieldsInv` on coordinates.** The output record at `(a, d, g, h, z)` of shape
`[A] × [Hd] × [G] × [Hh] × [B]` is the input record at `(a, h, g, d, z)` of shape
`[A] × [Hh] × [G] × [Hd] × [B]`. -/
theorem swapFieldsInv_coord {Hh G Hd B a d g h z : ℕ} (hd : d < Hd) (hg : g < G) (hh : h < Hh)
    (hz : z < B) :
    swapFieldsInv Hh G Hd B ((((a * Hd + d) * G + g) * Hh + h) * B + z) =
      (((a * Hh + h) * G + g) * Hd + d) * B + z := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := ((a * Hd + d) * G + g) * Hh + h) hz
  obtain ⟨e3, e4⟩ := divmod_aux (q := (a * Hd + d) * G + g) hh
  obtain ⟨e5, e6⟩ := divmod_aux (q := a * Hd + d) hg
  obtain ⟨e7, e8⟩ := divmod_aux (q := a) hd
  simp only [swapFieldsInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6, e7, e8]

/-! ## Lemma A.9: the packed selected-bit map on coordinates -/

/-- Mixed-radix rank on the Lemma A.9 rectangle `[N0] × [2^L] × [N1] × [2^L] × [N2] × [2^L] × [N3]`, with
spectators `a0, …, a3` and chunk slots `c 0, c 1, c 2`. -/
def c7Rank (L N1 N2 N3 a0 a1 a2 a3 : ℕ) (c : Fin 3 → ℕ) : ℕ :=
  (((((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2) * 2 ^ L + c 2) * N3 + a3

/-- The slots of a rank are its chunk coordinates. -/
theorem c7Slot_rank {L N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ} (hc : ∀ i, c i < 2 ^ L)
    (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) (j : Fin 3) :
    c7Slot L N1 N2 N3 j (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) = c j := by
  obtain ⟨e1, -⟩ := divmod_aux
    (q := ((((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2) * 2 ^ L + c 2) h3
  obtain ⟨e2, e2'⟩ := divmod_aux
    (q := (((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) * N2 + a2) (hc 2)
  obtain ⟨e3, -⟩ := divmod_aux (q := ((a0 * 2 ^ L + c 0) * N1 + a1) * 2 ^ L + c 1) h2
  obtain ⟨e4, e4'⟩ := divmod_aux (q := (a0 * 2 ^ L + c 0) * N1 + a1) (hc 1)
  obtain ⟨e5, -⟩ := divmod_aux (q := a0 * 2 ^ L + c 0) h1
  obtain ⟨-, e6'⟩ := divmod_aux (q := a0) (hc 0)
  obtain ⟨jv, hjv⟩ := j
  interval_cases jv
  · show (c7Rank L N1 N2 N3 a0 a1 a2 a3 c / (N3 * 2 ^ L * N2 * 2 ^ L * N1)) % 2 ^ L = c 0
    simp only [c7Rank, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6']
  · show (c7Rank L N1 N2 N3 a0 a1 a2 a3 c / (N3 * 2 ^ L * N2)) % 2 ^ L = c 1
    simp only [c7Rank, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4']
  · show (c7Rank L N1 N2 N3 a0 a1 a2 a3 c / N3) % 2 ^ L = c 2
    simp only [c7Rank, e1, e2']

/-- Replacing one chunk coordinate of a rank, written with the slot stride. -/
theorem c7Rank_update (L N1 N2 N3 a0 a1 a2 a3 : ℕ) (c : Fin 3 → ℕ) (j : Fin 3) (v : ℕ) :
    c7Rank L N1 N2 N3 a0 a1 a2 a3 c - c j * c7Stride L N1 N2 N3 j + v * c7Stride L N1 N2 N3 j =
      c7Rank L N1 N2 N3 a0 a1 a2 a3 (Function.update c j v) := by
  have key : ∀ w : ℕ, c7Rank L N1 N2 N3 a0 a1 a2 a3 (Function.update c j w) =
      w * c7Stride L N1 N2 N3 j + c7Rank L N1 N2 N3 a0 a1 a2 a3 (Function.update c j 0) := by
    intro w
    rcases j with ⟨_ | _ | _ | n, hj⟩
    · simp only [c7Rank, c7Stride, Function.update_apply]; simp; ring
    · simp only [c7Rank, c7Stride, Function.update_apply]; simp; ring
    · simp only [c7Rank, c7Stride, Function.update_apply]; simp; ring
    · omega
  have hc : c7Rank L N1 N2 N3 a0 a1 a2 a3 c =
      c7Rank L N1 N2 N3 a0 a1 a2 a3 (Function.update c j (c j)) := by
    rw [Function.update_eq_self]
  rw [hc, key (c j), key v]
  rw [Nat.add_sub_cancel_left]
  ring

/-- **`packedXorAddr` on coordinates**: it replaces the `y` slot by `y ⊕ mask(x)` and fixes the
spectators and the other slots. -/
theorem packedXorAddr_rank {L K ρ f N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ}
    (σ : Equiv.Perm (Fin 3)) (hc : ∀ i, c i < 2 ^ L) (h1 : a1 < N1) (h2 : a2 < N2)
    (h3 : a3 < N3) :
    packedXorAddr L K ρ f N1 N2 N3 σ (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
      c7Rank L N1 N2 N3 a0 a1 a2 a3
        (Function.update c (σ.symm 1) (Nat.xor (c (σ.symm 1)) (selMask K ρ f (c (σ.symm 0))))) := by
  unfold packedXorAddr
  rw [c7Slot_rank hc h1 h2 h3, c7Slot_rank hc h1 h2 h3, c7Rank_update]

/-- The selected-bit mask is below `2^{fK}` when `ρ < K`. -/
theorem selMask_lt {K ρ : ℕ} (hρ : ρ < K) (xv : ℕ) : ∀ f, selMask K ρ f xv < 2 ^ (f * K)
  | 0 => by simp [selMask]
  | f + 1 => by
    have ih := selMask_lt hρ xv f
    have hb : xv / 2 ^ (ρ + f * K) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have h1 : 2 ^ (f * K) ≤ 2 ^ (ρ + f * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (ρ + f * K) * 2 ≤ 2 ^ ((f + 1) * K) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.succ_mul]; omega)
    have h4 : 2 ^ (ρ + f * K) * (xv / 2 ^ (ρ + f * K) % 2) ≤ 2 ^ (ρ + f * K) := by
      calc 2 ^ (ρ + f * K) * (xv / 2 ^ (ρ + f * K) % 2) ≤ 2 ^ (ρ + f * K) * 1 :=
            Nat.mul_le_mul_left _ hb
        _ = 2 ^ (ρ + f * K) := Nat.mul_one _
    have hs : selMask K ρ (f + 1) xv =
        selMask K ρ f xv + 2 ^ (ρ + f * K) * (xv / 2 ^ (ρ + f * K) % 2) := by
      simp only [selMask, Finset.sum_range_succ]
    rw [hs]
    omega

/-- **Lemma A.9 (`lem:transfer13`) correspondence with `packedT0`.** On a record index of the
Lemma A.9 rectangle, with `L = fK` and `ρ < K`, the image under `packedXorAddr` is the rank of a
chunk triple `c'` with the same spectators. In the chunk names `(x, y, z)` (slot `σ⁻¹ i` holds `i`),
`c'` is `packedT0 K ρ (f + 1)` of `c`, i.e. `y_{ρ+iK} ← y_{ρ+iK} ⊕ x_{ρ+iK}` for all `i < f`. -/
theorem packedXorAddr_corr {L K ρ f N1 N2 N3 a0 a1 a2 a3 : ℕ} {c : Fin 3 → ℕ}
    (σ : Equiv.Perm (Fin 3)) (hL : L = f * K) (hρ : ρ < K) (hc : ∀ i, c i < 2 ^ L)
    (h1 : a1 < N1) (h2 : a2 < N2) (h3 : a3 < N3) :
    ∃ c' : Fin 3 → ℕ,
      packedXorAddr L K ρ f N1 N2 N3 σ (c7Rank L N1 N2 N3 a0 a1 a2 a3 c) =
        c7Rank L N1 N2 N3 a0 a1 a2 a3 c' ∧ (∀ i, c' i < 2 ^ L) ∧
      (c' (σ.symm 0), c' (σ.symm 1), c' (σ.symm 2)) =
        packedT0 K ρ (f + 1) (c (σ.symm 0), c (σ.symm 1), c (σ.symm 2)) := by
  have hv : Nat.xor (c (σ.symm 1)) (selMask K ρ f (c (σ.symm 0))) < 2 ^ L := by
    have hm := selMask_lt hρ (c (σ.symm 0)) f
    rw [← hL] at hm
    exact Nat.xor_lt_two_pow (hc _) hm
  refine ⟨Function.update c (σ.symm 1) (Nat.xor (c (σ.symm 1)) (selMask K ρ f (c (σ.symm 0)))),
    packedXorAddr_rank σ hc h1 h2 h3, ?_, ?_⟩
  · intro i
    by_cases hi : i = σ.symm 1
    · subst hi; simpa using hv
    · rw [Function.update_of_ne hi]; exact hc i
  · have h01 : σ.symm 0 ≠ σ.symm 1 := fun h => by simpa using σ.symm.injective h
    have h21 : σ.symm 2 ≠ σ.symm 1 := fun h => by simpa using σ.symm.injective h
    simp only [Function.update_of_ne h01, Function.update_of_ne h21, Function.update_self,
      packedT0, Nat.add_sub_cancel, selMask, bitAt]

/-! ## Proposition A.7 and Lemma A.8: correspondence with `Model.Step.swapBlocks` -/

/-- The record list of a model array in lexicographic order (field `0` most significant): entry
`v < card` is the record at the address of mixed-radix rank `v`. `x₀` only witnesses that the
field ranges are nonzero (it is overwritten). -/
def lexRecords (L : Model.Layout) (x₀ : L.Addr) {β : Type} (A : L.Addr → β) : List β :=
  (List.range L.card).map fun v => A (L.blockSet 0 L.n x₀ v)

/-- **Interface proposition: correspondence with `Model.Step.swapBlocks`.** For a layout whose
fields split into the blocks `[0, t₀)`, `[t₀, t₀+len)`, `[t₀+len, s₀)`, `[s₀, s₀+len)` and
`[s₀+len, n)`, with equal ranges of the two swapped blocks, the lexicographic record list of
`(Step.swapBlocks t₀ s₀ len).run A` is `permByInv (swapFieldsInv Hh G Hd B)` of the record list of
`A`, where `Hh, G, Hd, B` are the block ranges. On coordinates this is `swapFieldsInv_coord` above;
for `nodeLayout` it is proved directly in `C5NetSimSteps.lean`. -/
def SwapBlocksCorrStmt : Prop :=
  ∀ (L : Model.Layout) (x₀ : L.Addr) (β : Type) [Inhabited β] (A : L.Addr → β) (t₀ s₀ len : ℕ),
    t₀ + len ≤ s₀ → s₀ + len ≤ L.n →
    L.blockRange t₀ (t₀ + len) = L.blockRange s₀ (s₀ + len) →
    lexRecords L x₀ ((Model.Step.swapBlocks t₀ s₀ len : Model.Step L β).run A) =
      permByInv (swapFieldsInv (L.blockRange t₀ (t₀ + len)) (L.blockRange (t₀ + len) s₀)
        (L.blockRange s₀ (s₀ + len)) (L.blockRange (s₀ + len) L.n)) (lexRecords L x₀ A)

end SubNLogN.Machine.AppC.Corr
