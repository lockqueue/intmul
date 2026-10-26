import SubNLogN.Math.Walsh.LayerSpec

/-!
# Walsh: record-order convention lemmas for layer addresses

Paper: Proposition A.11 (`prop:prop14-param`): "The input is a disk-grid array in lexicographic order
on `[A] × [2^K]^D × [S]`". `lexIndex` (in `LayerSpec.lean`) fixes this order; the lemmas below say
that it is a bijection onto `[M]`, `M = A · 2^{KD} · S`. They are needed only to connect tape
positions with `LayerAddr` (machine level); `LayerSpec` itself does not depend on the order.

Proof method: a chunk value is the base-`2` number of its digit vector and the chunk part of
`lexIndex` is the base-`2^K` number of the chunk values (most significant chunk first); both are
identified with Mathlib's `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` (the chunk part
after reversing the chunk order with `Fin.rev`), which gives the bounds and injectivity. The
prefix/suffix layers are separated by uniqueness of division with remainder.
-/

namespace SubNLogN.Math.Walsh

/-! ## Helpers: digit vectors as `finFunctionFinEquiv` numbers (namespace `LayerOrderAux`) -/

namespace LayerOrderAux

/-- The digits of a chunk digit vector as elements of `Fin 2`. -/
def chunkDigits {K : ℕ} (c : Fin K → Bool) : Fin K → Fin 2 := fun i => if c i then 1 else 0

/-- `chunkVal c` is the base-`2` number with digits `chunkDigits c` (digit `i` of weight `2^i`). -/
theorem chunkVal_eq_finFunctionFinEquiv {K : ℕ} (c : Fin K → Bool) :
    chunkVal c = (finFunctionFinEquiv (chunkDigits c) : ℕ) := by
  rw [finFunctionFinEquiv_apply, chunkVal]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : c i <;> simp [chunkDigits, h]

end LayerOrderAux

/-- A chunk digit vector has value below `2^K`. CONTRACT (convention lemma). -/
theorem chunkVal_lt {K : ℕ} (c : Fin K → Bool) : chunkVal c < 2 ^ K := by
  rw [LayerOrderAux.chunkVal_eq_finFunctionFinEquiv]
  exact (finFunctionFinEquiv (LayerOrderAux.chunkDigits c)).isLt

namespace LayerOrderAux

/-- Distinct chunk digit vectors have distinct values. -/
theorem chunkVal_injective {K : ℕ} : Function.Injective (chunkVal : (Fin K → Bool) → ℕ) := by
  intro c c' h
  rw [chunkVal_eq_finFunctionFinEquiv, chunkVal_eq_finFunctionFinEquiv] at h
  have h2 := finFunctionFinEquiv.injective (Fin.ext h)
  funext i
  have hi := congrFun h2 i
  simp only [chunkDigits] at hi
  cases hc : c i <;> cases hc' : c' i <;> simp_all

/-- The chunk part of `lexIndex`: the chunk values read as a base-`2^K` number, chunk `0` most
significant. -/
def chunksVal {K D : ℕ} (c : Fin D → Fin K → Bool) : ℕ :=
  ∑ j : Fin D, chunkVal (c j) * 2 ^ (K * (D - 1 - (j : ℕ)))

/-- The chunk values as base-`2^K` digits, least significant (i.e. chunk `D-1`) first. -/
def chunkDigitsRev {K D : ℕ} (c : Fin D → Fin K → Bool) : Fin D → Fin (2 ^ K) :=
  fun j => ⟨chunkVal (c (Fin.rev j)), chunkVal_lt _⟩

theorem chunksVal_eq_finFunctionFinEquiv {K D : ℕ} (c : Fin D → Fin K → Bool) :
    chunksVal c = (finFunctionFinEquiv (chunkDigitsRev c) : ℕ) := by
  rw [finFunctionFinEquiv_apply, chunksVal,
    ← Equiv.sum_comp Fin.revPerm (fun j : Fin D => chunkVal (c j) * 2 ^ (K * (D - 1 - (j : ℕ))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, chunkDigitsRev, Fin.val_rev]
  have hj : D - 1 - (D - ((j : ℕ) + 1)) = j := by have := j.isLt; omega
  rw [hj, ← pow_mul]

theorem chunksVal_lt {K D : ℕ} (c : Fin D → Fin K → Bool) : chunksVal c < 2 ^ (K * D) := by
  rw [chunksVal_eq_finFunctionFinEquiv, pow_mul]
  exact (finFunctionFinEquiv (chunkDigitsRev c)).isLt

theorem chunksVal_injective {K D : ℕ} :
    Function.Injective (chunksVal : (Fin D → Fin K → Bool) → ℕ) := by
  intro c c' h
  rw [chunksVal_eq_finFunctionFinEquiv, chunksVal_eq_finFunctionFinEquiv] at h
  have h2 := finFunctionFinEquiv.injective (Fin.ext h)
  funext j
  have hj := congrFun h2 (Fin.rev j)
  simp only [chunkDigitsRev, Fin.rev_rev, Fin.mk.injEq] at hj
  exact chunkVal_injective hj

theorem lexIndex_eq_chunksVal {A K D S : ℕ} (x : LayerAddr A K D S) :
    lexIndex x = ((x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1) * S + (x.2.2 : ℕ) := rfl

/-- Uniqueness of division with remainder, in the form used for `lexIndex`. -/
theorem mul_add_eq_mul_add_of_lt {S a a' b b' : ℕ} (hb : b < S) (hb' : b' < S)
    (h : a * S + b = a' * S + b') : a = a' ∧ b = b' := by
  have hS : 0 < S := by omega
  have e1 := (Nat.div_mod_unique hS).2 ⟨(by ring : b + S * a = a * S + b), hb⟩
  have e2 := (Nat.div_mod_unique hS).2 ⟨(by ring : b' + S * a' = a' * S + b'), hb'⟩
  rw [h] at e1
  exact ⟨e1.1.symm.trans e2.1, e1.2.symm.trans e2.2⟩

end LayerOrderAux

open LayerOrderAux

/-! ## The convention lemmas -/

/-- The lexicographic index of a layer address is below `M = A · 2^{KD} · S`
(record-order convention of Proposition A.11, `prop:prop14-param`). CONTRACT (convention lemma). -/
theorem lexIndex_lt {A K D S : ℕ} (x : LayerAddr A K D S) :
    lexIndex x < A * 2 ^ (K * D) * S := by
  rw [lexIndex_eq_chunksVal]
  have h1 := chunksVal_lt x.2.1
  have h2 := x.1.isLt
  have h3 := x.2.2.isLt
  have hQ : (x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1 < A * 2 ^ (K * D) := by
    calc (x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1
        < (x.1 : ℕ) * 2 ^ (K * D) + 2 ^ (K * D) := by omega
      _ = ((x.1 : ℕ) + 1) * 2 ^ (K * D) := by ring
      _ ≤ A * 2 ^ (K * D) := Nat.mul_le_mul_right _ (by omega)
  calc ((x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1) * S + (x.2.2 : ℕ)
      < ((x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1) * S + S := by omega
    _ = ((x.1 : ℕ) * 2 ^ (K * D) + chunksVal x.2.1 + 1) * S := by ring
    _ ≤ A * 2 ^ (K * D) * S := Nat.mul_le_mul_right _ (by omega)

/-- The lexicographic index is injective on layer addresses; with `lexIndex_lt` and
`Fintype.card (LayerAddr A K D S) = A · 2^{KD} · S` it is a bijection onto `[M]`
(record-order convention of Proposition A.11, `prop:prop14-param`). CONTRACT (convention lemma). -/
theorem lexIndex_injective {A K D S : ℕ} :
    Function.Injective (lexIndex : LayerAddr A K D S → ℕ) := by
  intro x y h
  rw [lexIndex_eq_chunksVal, lexIndex_eq_chunksVal] at h
  obtain ⟨hQ, hs⟩ := mul_add_eq_mul_add_of_lt x.2.2.isLt y.2.2.isLt h
  rw [add_comm ((x.1 : ℕ) * _), add_comm ((y.1 : ℕ) * _)] at hQ
  obtain ⟨hc, h1⟩ := mul_add_eq_mul_add_of_lt (chunksVal_lt x.2.1) (chunksVal_lt y.2.1)
    (by rw [add_comm, hQ, add_comm])
  exact Prod.ext (Fin.ext hc) (Prod.ext (chunksVal_injective h1) (Fin.ext hs))

end SubNLogN.Math.Walsh
