import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 2: the packed row addition on encoded layer addresses

Proof of `CCoreEdgeAux.AddrXorAllEncodeStmt` (statement and the block/bit lemmas in
`Proofs/CCoreEdgeBits.lean`): for the slots of a Lemma A.10 (`lem:transfer-phase`) node (`slotPos t = 1 + (j0 + t f) K`,
`L = fK`), the Lemma A.9 (`lem:transfer13`) address map `addrXorAll` adding slot `j` into slot `i` acts on encoded layer
addresses as `encodeAddr ∘ rowAddL ρ f j0 i j`: bit `ρ` of chunk `j0 + i f + q` is XORed with bit
`ρ` of chunk `j0 + j f + q` (`q < f`), nothing else changes. No hypotheses beyond those of the
statement (`1 ≤ f`, `i, j < m`, `j0 + m f ≤ D`; `i = j` is allowed).

Proof. Compare field by field. A field `m` of the `y` block `[py, py + fK)` is
`m = py + qK + r` (`q < f`, `r < K`): bit `t = K−1−r` of chunk `ch = j0 + if + q`, at binary
position `b = (f−1−q)K + t` of the slot value. By `addrXorAll_val` the new field is
`testBit y b XOR testBit ctrl b`; `testBit y b` is the old bit (`testBit_blockVal_bin`), and
`testBit ctrl b` holds iff `ρ + i'K = b` for some `i' < f` with source bit `1`
(`testBit_ctrl`), i.e. iff `t = ρ` (then `i' = f−1−q`, residues mod `K`) and bit `ρ` of chunk
`j0 + jf + q` is set. Fields outside the `y` block are unchanged on both sides (a bit changed by
`rowAddL` lives in the `y` block).
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeBits2Aux

open Model CCoreEdgeAux SubNLogN.Math.Walsh

variable {A K D S : ℕ}

/-- The value of a binary field of an encoded address is the bit it encodes. -/
theorem encode_val_bit (y : LayerAddr A K D S) (m : Fin (layerLayout A K D S).n) (ch t : ℕ)
    (hch : ch < D) (ht : t < K) (hm : m.val = 1 + ch * K + (K - 1 - t)) :
    (encodeAddr y m).val = if y.2.1 ⟨ch, hch⟩ ⟨t, ht⟩ then 1 else 0 := by
  obtain ⟨mv, hmv⟩ := m
  simp only at hm
  subst hm
  exact encode_bit y ⟨ch, hch⟩ ⟨t, ht⟩

/-- Every middle field `1 ≤ m ≤ DK` encodes some bit `t` of some chunk `ch`. -/
theorem mid_decomp {m : ℕ} (h0 : m ≠ 0) (h1 : m ≤ D * K) :
    ∃ ch t, ∃ (_ : ch < D) (_ : t < K), m = 1 + ch * K + (K - 1 - t) := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · rw [hK, Nat.mul_zero] at h1
      omega
    · exact hK
  have hdm := Nat.div_add_mod' (m - 1) K
  have hr := Nat.mod_lt (m - 1) hK
  refine ⟨(m - 1) / K, K - 1 - (m - 1) % K, ?_, by omega, by omega⟩
  apply Nat.div_lt_of_lt_mul
  rw [Nat.mul_comm K D]
  omega

end CCoreEdgeBits2Aux

open Model CCoreEdgeAux CCoreEdgeBits2Aux SubNLogN.Math.Walsh in
/-- **Packed row addition on encoded layer addresses** (`AddrXorAllEncodeStmt`): adding slot `j`
into slot `i` of a Lemma A.10 (`lem:transfer-phase`) node by the Lemma A.9 (`lem:transfer13`) map `addrXorAll` is `encodeAddr ∘ rowAddL ρ f j0 i j`. -/
theorem addrXorAll_encode_holds : AddrXorAllEncodeStmt := by
  intro A K D S ρ f j0 i j t3 hf hi hj hD x
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) ρ.isLt
  have hρ : ρ.val < K := ρ.isLt
  have hiF : i * f + f ≤ mH * f := by
    have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt hi)
    rwa [Nat.succ_mul] at this
  have hjF : j * f + f ≤ mH * f := by
    have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt hj)
    rwa [Nat.succ_mul] at this
  have hyD : j0 + i * f + f ≤ D := by omega
  have hxD : j0 + j * f + f ≤ D := by omega
  have hyK : (j0 + i * f + f) * K ≤ D * K := Nat.mul_le_mul_right K hyD
  have hxK : (j0 + j * f + f) * K ≤ D * K := Nat.mul_le_mul_right K hxD
  have eyK : (j0 + i * f + f) * K = (j0 + i * f) * K + f * K := Nat.add_mul _ _ _
  have exK : (j0 + j * f + f) * K = (j0 + j * f) * K + f * K := Nat.add_mul _ _ _
  have hn : (layerLayout A K D S).n = D * K + 2 := rfl
  have hyn : 1 + (j0 + i * f) * K + f * K ≤ (layerLayout A K D S).n := by omega
  have hxn : 1 + (j0 + j * f) * K + f * K ≤ (layerLayout A K D S).n := by omega
  have hybin : ∀ m' : Fin (layerLayout A K D S).n, 1 + (j0 + i * f) * K ≤ m'.val →
      m'.val < 1 + (j0 + i * f) * K + f * K → (layerLayout A K D S).r m' = 2 :=
    fun m' h1 h2 => layer_r_mid m' (by omega) (by omega)
  have hxbin : ∀ m' : Fin (layerLayout A K D S).n, 1 + (j0 + j * f) * K ≤ m'.val →
      m'.val < 1 + (j0 + j * f) * K + f * K → (layerLayout A K D S).r m' = 2 :=
    fun m' h1 h2 => layer_r_mid m' (by omega) (by omega)
  funext m
  apply Fin.ext
  by_cases hm : 1 + (j0 + i * f) * K ≤ m.val ∧ m.val < 1 + (j0 + i * f) * K + f * K
  · -- a field of the target block
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨q, r, hqf, hrK, hmqr⟩ : ∃ q r, q < f ∧ r < K ∧
        m.val = 1 + (j0 + i * f) * K + q * K + r := by
      have hdm := Nat.div_add_mod' (m.val - (1 + (j0 + i * f) * K)) K
      have hr := Nat.mod_lt (m.val - (1 + (j0 + i * f) * K)) hK
      refine ⟨(m.val - (1 + (j0 + i * f) * K)) / K, (m.val - (1 + (j0 + i * f) * K)) % K, ?_,
        hr, by omega⟩
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm K f]
      omega
    have hch : j0 + i * f + q < D := by omega
    have hch' : j0 + j * f + q < D := by omega
    have ht : K - 1 - r < K := by omega
    have eqK : (j0 + i * f + q) * K = (j0 + i * f) * K + q * K := Nat.add_mul _ _ _
    have eqK' : (j0 + j * f + q) * K = (j0 + j * f) * K + q * K := Nat.add_mul _ _ _
    have hmc : m.val = 1 + (j0 + i * f + q) * K + (K - 1 - (K - 1 - r)) := by omega
    have e1 : (f - 1 - q) * K + (q + 1) * K = f * K := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have e2 : (q + 1) * K = q * K + K := Nat.succ_mul q K
    have hb : 1 + (j0 + i * f) * K + f * K - 1 - m.val = (f - 1 - q) * K + (K - 1 - r) := by
      omega
    -- the old bit of the target chunk
    have T1 : (chunkVal (f * K) (1 + (j0 + i * f) * K) (encodeAddr x)).testBit
        ((f - 1 - q) * K + (K - 1 - r)) = x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩ := by
      apply Bool.eq_iff_iff.2
      unfold chunkVal
      rw [testBit_blockVal_bin hyn hybin]
      have hidx : 1 + (j0 + i * f) * K + f * K - 1 - ((f - 1 - q) * K + (K - 1 - r)) = m.val := by
        omega
      rw [hidx, fv_of_lt (encodeAddr x) m.isLt, Fin.eta, encode_val_bit x m _ _ hch ht hmc]
      constructor
      · rintro ⟨_, h⟩
        by_contra hx
        rw [if_neg hx] at h
        exact absurd h (by norm_num)
      · intro h
        exact ⟨by omega, by rw [if_pos h]⟩
    -- the control bit
    have T2 : (∑ i' ∈ Finset.range f, 2 ^ (ρ.val + i' * K) *
        chunkBit (f * K) (1 + (j0 + j * f) * K) (ρ.val + i' * K) (encodeAddr x)).testBit
          ((f - 1 - q) * K + (K - 1 - r)) =
        (decide ((⟨K - 1 - r, ht⟩ : Fin K) = ρ) && x.2.1 ⟨j0 + j * f + q, hch'⟩ ρ) := by
      apply Bool.eq_iff_iff.2
      rw [testBit_ctrl hρ hxn hxbin, Bool.and_eq_true, decide_eq_true_eq]
      have hidx : ∀ i' : ℕ, i' = f - 1 - q →
          1 + (j0 + j * f) * K + f * K - 1 - (ρ.val + i' * K) =
            1 + (j0 + j * f + q) * K + (K - 1 - ρ.val) := by
        rintro i' rfl
        omega
      constructor
      · rintro ⟨i', hi', hib, hfv⟩
        have hmod : (ρ.val + i' * K) % K = ((f - 1 - q) * K + (K - 1 - r)) % K := by rw [hib]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ,
          Nat.add_comm ((f - 1 - q) * K) (K - 1 - r), Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt ht] at hmod
        have hi'q : i' * K = (f - 1 - q) * K := by omega
        have hi'eq : i' = f - 1 - q := Nat.eq_of_mul_eq_mul_right hK hi'q
        refine ⟨Fin.ext hmod.symm, ?_⟩
        rw [hidx i' hi'eq, fv_encode_bit x _ _ hch' hρ, Fin.eta] at hfv
        by_contra hx
        rw [if_neg hx] at hfv
        exact absurd hfv (by norm_num)
      · rintro ⟨htρ, hx⟩
        have hρv : ρ.val = K - 1 - r := (congrArg Fin.val htρ).symm
        refine ⟨f - 1 - q, by omega, by omega, ?_⟩
        rw [hidx (f - 1 - q) rfl, fv_encode_bit x _ _ hch' hρ, Fin.eta, if_pos hx]
    -- the new bit
    have R : (encodeAddr (rowAddL ρ f j0 i j x) m).val =
        if (if (⟨K - 1 - r, ht⟩ : Fin K) = ρ then
            xor (x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩) (x.2.1 ⟨j0 + j * f + q, hch'⟩ ρ)
          else x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩) = true then 1 else 0 := by
      rw [encode_val_bit _ m _ _ hch ht hmc]
      have hrange : j0 + i * f ≤ j0 + i * f + q ∧ j0 + i * f + q < j0 + i * f + f :=
        ⟨by omega, by omega⟩
      have hxb : xbit x (j0 + i * f + q - i * f + j * f) ρ.val =
          x.2.1 ⟨j0 + j * f + q, hch'⟩ ρ := by
        have e3 : j0 + i * f + q - i * f + j * f = j0 + j * f + q := by omega
        unfold xbit
        rw [dif_pos ⟨by omega, hρ⟩]
        simp only [e3, Fin.eta]
      have hbit : (rowAddL ρ f j0 i j x).2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩ =
          if (⟨K - 1 - r, ht⟩ : Fin K) = ρ then
            xor (x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩) (x.2.1 ⟨j0 + j * f + q, hch'⟩ ρ)
          else x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩ := by
        show (if (⟨K - 1 - r, ht⟩ : Fin K) = ρ ∧ j0 + i * f ≤ j0 + i * f + q ∧
            j0 + i * f + q < j0 + i * f + f then
            xor (x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩)
              (xbit x (j0 + i * f + q - i * f + j * f) ρ.val)
          else x.2.1 ⟨j0 + i * f + q, hch⟩ ⟨K - 1 - r, ht⟩) = _
        by_cases htρ : (⟨K - 1 - r, ht⟩ : Fin K) = ρ
        · rw [if_pos ⟨htρ, hrange⟩, if_pos htρ, hxb]
        · rw [if_neg (fun h => htρ h.1), if_neg htρ]
      rw [hbit]
    rw [addrXorAll_val (Ly := layerLayout A K D S) (f * K) K ρ.val f
      ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ hyn hybin
      (encodeAddr x) m hm1 hm2]
    dsimp only
    rw [hb, T1, T2, R]
    by_cases htρ : (⟨K - 1 - r, ht⟩ : Fin K) = ρ
    · simp [htρ]
    · simp [htρ]
  · -- a field outside the target block: unchanged on both sides
    have hL : addrXorAll (Ly := layerLayout A K D S) (f * K) K ρ.val f
        ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ (encodeAddr x) m =
          encodeAddr x m := by
      unfold addrXorAll
      exact blockSet_apply_of_not _ _ m hm
    rw [hL]
    by_cases h0 : m.val = 0
    · rw [encode_zero x m h0, encode_zero _ m h0]
      rfl
    · by_cases h1 : m.val ≤ D * K
      · obtain ⟨ch, t, hch, ht, hmc⟩ := mid_decomp h0 h1
        rw [encode_val_bit x m ch t hch ht hmc, encode_val_bit _ m ch t hch ht hmc]
        have hnot : ¬ ((⟨t, ht⟩ : Fin K) = ρ ∧ j0 + i * f ≤ ch ∧ ch < j0 + i * f + f) := by
          rintro ⟨htρ, h2, h3⟩
          have htv : t = ρ.val := congrArg Fin.val htρ
          have e1 : (j0 + i * f) * K ≤ ch * K := Nat.mul_le_mul_right K h2
          have e2 : (ch + 1) * K ≤ (j0 + i * f + f) * K := Nat.mul_le_mul_right K h3
          rw [Nat.succ_mul] at e2
          exact hm ⟨by omega, by omega⟩
        have hbit : (rowAddL ρ f j0 i j x).2.1 ⟨ch, hch⟩ ⟨t, ht⟩ = x.2.1 ⟨ch, hch⟩ ⟨t, ht⟩ :=
          if_neg hnot
        rw [hbit]
      · rw [encode_top x m h0 h1, encode_top _ m h0 h1]
        rfl

end SubNLogN.Math.Networks
