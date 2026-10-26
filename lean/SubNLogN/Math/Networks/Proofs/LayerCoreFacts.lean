import SubNLogN.Math.Networks.LayerCore

/-!
# Networks: the `layerLayout` address round trip (`DecodeEncodeAddrStmt`)

`decodeAddr ∘ encodeAddr = id` on `LayerAddr A K D S`. The prefix (field `0`) and the suffix
(field `DK + 1`) are copied. Bit `t` of chunk `j` sits at field `i = 1 + jK + (K−1−t)`, and
`encodeAddr` reads chunk `(i−1)/K = j`, bit `K−1−((i−1) mod K) = t` there
(`LayerCoreAux.div_mod_aux`). Helpers live in `SubNLogN.Math.Networks.LayerCoreAux`.
-/

namespace SubNLogN.Math.Networks

namespace LayerCoreAux

/-- For `t < K`: `(1 + jK + (K−1−t) − 1)/K = j` and `K − 1 − ((1 + jK + (K−1−t) − 1) mod K) = t`. -/
theorem div_mod_aux {K j t : ℕ} (ht : t < K) :
    (1 + j * K + (K - 1 - t) - 1) / K = j ∧ K - 1 - (1 + j * K + (K - 1 - t) - 1) % K = t := by
  have h1 : 1 + j * K + (K - 1 - t) - 1 = (K - 1 - t) + j * K := by omega
  have hK : 0 < K := by omega
  rw [h1, Nat.add_mul_div_right _ _ hK, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

end LayerCoreAux

/-- **Layout round trip**: `decodeAddr (encodeAddr x) = x` for every layer address `x`. -/
theorem decodeEncodeAddr_holds : DecodeEncodeAddrStmt := by
  intro A K D S x
  obtain ⟨x1, x2, x3⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    simp [decodeAddr, encodeAddr]
  · funext j t
    have hK : 0 < K := by have := t.isLt; omega
    obtain ⟨e1, e2⟩ := LayerCoreAux.div_mod_aux (j := j.val) t.isLt
    have h1 : 1 + j.val * K + (K - 1 - t.val) ≤ D * K := by
      have := j.isLt
      have : j.val * K + K ≤ D * K := by nlinarith
      omega
    simp [decodeAddr, encodeAddr, h1, hK, e1, e2]
  · apply Fin.ext
    have h1 : ¬ (D * K + 1 ≤ D * K) := by omega
    simp [decodeAddr, encodeAddr, h1]

end SubNLogN.Math.Networks
