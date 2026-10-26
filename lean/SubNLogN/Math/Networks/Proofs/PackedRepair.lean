import SubNLogN.Math.Networks.AppCFun
import SubNLogN.Math.Networks.Proofs.PackedAgree

/-!
# Proofs of `PackedRepairStmt` and `PackedFullStmt` (Lemma A.9 (`lem:transfer13`) repair and composition)

We prove `packedRepair_holds : PackedRepairStmt` and `packedFull_holds : PackedFullStmt`
(statements in `AppCFun.lean`; Lemma A.9 (`lem:transfer13`), [OAI26, §5.2, Lemma 13]).
No hypotheses beyond those of the statements are used; `PackedAgreeStmt` enters through its proof
`packedAgree_holds` (`Proofs/PackedAgree.lean`).

## Plan
* **One line is a bijection of `[2^L]³`.** A packed line changes only its target chunk, by an offset
  that depends only on `x` and the other chunk (`offS`); so the line with the opposite sign undoes it
  on the rectangle (`packedLine_cancel`, using `((t + a) mod 2^L + b) mod 2^L = t` for `a + b = 0`,
  `0 ≤ t < 2^L`). Hence every line, and every fold of lines, in particular `S₀ = packedS0`, is a
  bijection of the rectangle (`Set.InvOn.bijOn`, `Set.BijOn.comp`).
* **`T₀` is an involution of `[2^L]³`.** It XORs `y` with a mask depending only on `x`, and the mask is
  below `2^{ρ+(f-1)K} ≤ 2^L` (`mask_lt`, from `mask_parts`).
* **Good part.** On `rect ∩ good`, `S₀ = T₀` and `T₀` keeps goodness (`packedAgree_holds`); `T₀` is an
  involution, so `S₀` maps `rect ∩ good` onto itself (preimage of `q` is `T₀ q`), and injectivity is
  inherited from the rectangle. **Bad part.** `S₀` is a bijection of the rectangle mapping the good part
  onto itself, hence it maps the bad part onto itself.
* **Top bit.** With `f = n + 1`, the lower mask `M₀ = Σ_{i<n} 2^{ρ+iK} x_{ρ+iK}` is below `2^J`,
  `J = ρ + nK`, so `M₀ ⊕ 2^J b = M₀ + 2^J b` (compare the parts below and from `2^J`); then
  `(y ⊕ M₀) ⊕ 2^J b = y ⊕ (M₀ + 2^J b)` is the full mask by `Finset.sum_range_succ`.
-/

namespace SubNLogN.Math.Networks

namespace PackedRepairAux

open PackedAgreeAux

/-! ### Packed lines are bijections of the rectangle -/

/-- The unsigned offset of a packed line with controls from `x`, testing parity `q` of chunk `o`. -/
def offS (K ρ f x o q : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (f - 1), (2 : ℤ) ^ (ρ + i * K) *
    (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = q then 1 else 0)

lemma packedLine_true (L K ρ f : ℕ) (e : ℤ) (q x y z : ℕ) :
    packedLine L K ρ f (true, e, q) (x, y, z) =
      (x, (((y : ℤ) + e * offS K ρ f x z q) % (2 : ℤ) ^ L).toNat, z) := rfl

lemma packedLine_false (L K ρ f : ℕ) (e : ℤ) (q x y z : ℕ) :
    packedLine L K ρ f (false, e, q) (x, y, z) =
      (x, y, (((z : ℤ) + e * offS K ρ f x y q) % (2 : ℤ) ^ L).toNat) := rfl

lemma toNat_emod_lt (L : ℕ) (a : ℤ) : (a % (2 : ℤ) ^ L).toNat < 2 ^ L := by
  have h0 : 0 ≤ a % (2 : ℤ) ^ L := Int.emod_nonneg _ (by positivity)
  have h1 : a % (2 : ℤ) ^ L < (2 : ℤ) ^ L := Int.emod_lt_of_pos _ (by positivity)
  have h2 : (((a % (2 : ℤ) ^ L).toNat : ℕ) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]; push_cast; exact h1
  exact_mod_cast h2

/-- Adding `a` and then `b = -a` modulo `2^L` returns `t ∈ [0, 2^L)`. -/
lemma emod_cancel {L t : ℕ} (ht : t < 2 ^ L) (a b : ℤ) (hab : a + b = 0) :
    (((((((t : ℤ) + a) % (2 : ℤ) ^ L).toNat : ℕ) : ℤ) + b) % (2 : ℤ) ^ L).toNat = t := by
  have h0 : 0 ≤ ((t : ℤ) + a) % (2 : ℤ) ^ L := Int.emod_nonneg _ (by positivity)
  rw [Int.toNat_of_nonneg h0, Int.emod_add_emod, add_assoc, hab, add_zero,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ht), Int.toNat_natCast]

lemma packedLine_mem {L K ρ f : ℕ} (op : Bool × ℤ × ℕ) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ packedRect L) : packedLine L K ρ f op p ∈ packedRect L := by
  obtain ⟨t, e, q⟩ := op
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hx, hy, hz⟩ := hp
  cases t
  · rw [packedLine_false]; exact ⟨hx, hy, toNat_emod_lt L _⟩
  · rw [packedLine_true]; exact ⟨hx, toNat_emod_lt L _, hz⟩

/-- The line with the opposite sign undoes a packed line on the rectangle (its offset depends only
on the unchanged chunks). -/
lemma packedLine_cancel {L K ρ f : ℕ} (t : Bool) (e : ℤ) (q : ℕ) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ packedRect L) :
    packedLine L K ρ f (t, -e, q) (packedLine L K ρ f (t, e, q) p) = p := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hx, hy, hz⟩ := hp
  have hy' : y < 2 ^ L := hy
  have hz' : z < 2 ^ L := hz
  cases t
  · rw [packedLine_false, packedLine_false,
      emod_cancel hz' (e * offS K ρ f x y q) (-e * offS K ρ f x y q) (by ring)]
  · rw [packedLine_true, packedLine_true,
      emod_cancel hy' (e * offS K ρ f x z q) (-e * offS K ρ f x z q) (by ring)]

lemma packedLine_bijOn (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) :
    Set.BijOn (packedLine L K ρ f op) (packedRect L) (packedRect L) := by
  obtain ⟨t, e, q⟩ := op
  have hinv : Set.InvOn (packedLine L K ρ f (t, -e, q)) (packedLine L K ρ f (t, e, q))
      (packedRect L) (packedRect L) := by
    refine ⟨fun p hp => packedLine_cancel t e q hp, fun p hp => ?_⟩
    have h := packedLine_cancel (L := L) (K := K) (ρ := ρ) (f := f) t (-e) q hp
    rwa [neg_neg] at h
  exact hinv.bijOn (fun p hp => packedLine_mem _ hp) (fun p hp => packedLine_mem _ hp)

/-- Every fold of packed lines is a bijection of the rectangle. -/
lemma foldl_bijOn (L K ρ f : ℕ) : ∀ ops : List (Bool × ℤ × ℕ),
    Set.BijOn (fun p => ops.foldl (fun p op => packedLine L K ρ f op p) p)
      (packedRect L) (packedRect L)
  | [] => Set.bijOn_id _
  | op :: rest => (foldl_bijOn L K ρ f rest).comp (packedLine_bijOn L K ρ f op)

/-! ### The ideal map `T₀` -/

lemma mask_lt {L K ρ f : ℕ} (hK : 1 ≤ K) (hL : L = f * K) (hρ : ρ < K) (x : ℕ) :
    maskOf K ρ (f - 1) x < 2 ^ L := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp only [maskOf, Nat.zero_sub, Finset.range_zero, Finset.sum_empty]
    positivity
  · have hJ : ρ + (f - 1) * K ≤ L := by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      rw [hL, Nat.add_sub_cancel, add_mul, one_mul]
      omega
    have h0 := (mask_parts hK ρ (f - 1) x).2.1
    have h := Nat.div_add_mod (maskOf K ρ (f - 1) x) (2 ^ (ρ + (f - 1) * K))
    rw [h0, mul_zero, zero_add] at h
    calc maskOf K ρ (f - 1) x = maskOf K ρ (f - 1) x % 2 ^ (ρ + (f - 1) * K) := h.symm
      _ < 2 ^ (ρ + (f - 1) * K) := Nat.mod_lt _ (by positivity)
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hJ

lemma packedT0_mem {L K ρ f : ℕ} (hK : 1 ≤ K) (hL : L = f * K) (hρ : ρ < K) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ packedRect L) : packedT0 K ρ f p ∈ packedRect L := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hx, hy, hz⟩ := hp
  have hy' : y < 2 ^ L := hy
  show x < 2 ^ L ∧ y ^^^ maskOf K ρ (f - 1) x < 2 ^ L ∧ z < 2 ^ L
  exact ⟨hx, Nat.xor_lt_two_pow hy' (mask_lt hK hL hρ x), hz⟩

lemma packedT0_invol (K ρ f : ℕ) (p : ℕ × ℕ × ℕ) : packedT0 K ρ f (packedT0 K ρ f p) = p := by
  obtain ⟨x, y, z⟩ := p
  show (x, (y ^^^ maskOf K ρ (f - 1) x) ^^^ maskOf K ρ (f - 1) x, z) = (x, y, z)
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ### The top selected bit -/

/-- If `M < 2^J` (stated as `M / 2^J = 0`), XOR with `2^J b` is addition. -/
lemma xor_eq_add_of_div_eq_zero {M J b : ℕ} (hM : M / 2 ^ J = 0) :
    M ^^^ 2 ^ J * b = M + 2 ^ J * b := by
  have hMlt : M < 2 ^ J := by
    have h := Nat.div_add_mod M (2 ^ J)
    rw [hM, mul_zero, zero_add] at h
    rw [← h]; exact Nat.mod_lt _ (by positivity)
  have h1 : (M ^^^ 2 ^ J * b) % 2 ^ J = M := by
    rw [Nat.xor_mod_two_pow, Nat.mul_mod_right, Nat.xor_zero, Nat.mod_eq_of_lt hMlt]
  have h2 : (M ^^^ 2 ^ J * b) / 2 ^ J = b := by
    rw [Nat.xor_div_two_pow, hM, Nat.mul_div_cancel_left _ (by positivity), Nat.zero_xor]
  have h3 : (M + 2 ^ J * b) % 2 ^ J = M := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hMlt]
  have h4 : (M + 2 ^ J * b) / 2 ^ J = b := by
    rw [Nat.add_mul_div_left _ _ (by positivity), hM, zero_add]
  calc M ^^^ 2 ^ J * b
      = 2 ^ J * ((M ^^^ 2 ^ J * b) / 2 ^ J) + (M ^^^ 2 ^ J * b) % 2 ^ J :=
        (Nat.div_add_mod _ _).symm
    _ = 2 ^ J * ((M + 2 ^ J * b) / 2 ^ J) + (M + 2 ^ J * b) % 2 ^ J := by rw [h1, h2, h3, h4]
    _ = M + 2 ^ J * b := Nat.div_add_mod _ _

end PackedRepairAux

open PackedAgreeAux PackedRepairAux in
/-- **Lemma A.9 (`lem:transfer13`) repair** ([OAI26, §5.2, Lemma 13]). For `K ≥ 6`,
`L = fK`, `ρ < K`: `S₀` and `T₀` are bijections of `[2^L]³`, and `S₀` maps the good part and the bad
part of the rectangle onto themselves. -/
theorem packedRepair_holds : PackedRepairStmt := by
  intro L K ρ f hK hL hρ
  have hK1 : 1 ≤ K := by omega
  have hS : Set.BijOn (packedS0 L K ρ f) (packedRect L) (packedRect L) :=
    foldl_bijOn L K ρ f eightOps
  have hTmaps : Set.MapsTo (packedT0 K ρ f) (packedRect L) (packedRect L) :=
    fun p hp => packedT0_mem hK1 hL hρ hp
  have hTinv : Set.InvOn (packedT0 K ρ f) (packedT0 K ρ f) (packedRect L) (packedRect L) :=
    ⟨fun p _ => packedT0_invol K ρ f p, fun p _ => packedT0_invol K ρ f p⟩
  have hT : Set.BijOn (packedT0 K ρ f) (packedRect L) (packedRect L) :=
    hTinv.bijOn hTmaps hTmaps
  have hagree : ∀ p ∈ packedRect L ∩ packedGoodSet K ρ f,
      packedS0 L K ρ f p = packedT0 K ρ f p ∧ packedT0 K ρ f p ∈ packedGoodSet K ρ f := by
    rintro ⟨x, y, z⟩ ⟨⟨hx, hy, hz⟩, hg⟩
    exact packedAgree_holds L K ρ f hK hL hρ (x, y, z) hx hy hz hg
  have hG : Set.BijOn (packedS0 L K ρ f) (packedRect L ∩ packedGoodSet K ρ f)
      (packedRect L ∩ packedGoodSet K ρ f) := by
    refine ⟨fun p hp => ?_, hS.injOn.mono Set.inter_subset_left, fun q hq => ?_⟩
    · obtain ⟨h1, h2⟩ := hagree p hp
      rw [h1]
      exact ⟨hTmaps hp.1, h2⟩
    · obtain ⟨_, h2⟩ := hagree q hq
      refine ⟨packedT0 K ρ f q, ⟨hTmaps hq.1, h2⟩, ?_⟩
      rw [(hagree (packedT0 K ρ f q) ⟨hTmaps hq.1, h2⟩).1, packedT0_invol]
  have hB : Set.BijOn (packedS0 L K ρ f) (packedRect L \ packedGoodSet K ρ f)
      (packedRect L \ packedGoodSet K ρ f) := by
    refine ⟨fun p hp => ⟨hS.mapsTo hp.1, fun hgood => ?_⟩, hS.injOn.mono Set.sdiff_subset,
      fun q hq => ?_⟩
    · obtain ⟨p', hp', hpp'⟩ := hG.surjOn ⟨hS.mapsTo hp.1, hgood⟩
      have he : p' = p := hS.injOn hp'.1 hp.1 hpp'
      exact hp.2 (he ▸ hp'.2)
    · obtain ⟨p, hp, hpq⟩ := hS.surjOn hq.1
      refine ⟨p, ⟨hp, fun hgood => hq.2 ?_⟩, hpq⟩
      rw [← hpq]
      exact (hG.mapsTo ⟨hp, hgood⟩).2
  exact ⟨hS, hT, hG, hB⟩

open PackedAgreeAux PackedRepairAux in
/-- **Lemma A.9 (`lem:transfer13`) composition.** For `f ≥ 1` and `ρ < K`, flipping the top selected bit after `T₀` gives the
full selected-bit XOR `packedFull` (for every triple; `x` and `z` unchanged). -/
theorem packedFull_holds : PackedFullStmt := by
  intro K ρ f hf hρ xyz
  obtain ⟨x, y, z⟩ := xyz
  have hK1 : 1 ≤ K := by omega
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  have key : maskOf K ρ n x ^^^ 2 ^ (ρ + n * K) * bitAt x (ρ + n * K) =
      maskOf K ρ n x + 2 ^ (ρ + n * K) * bitAt x (ρ + n * K) :=
    xor_eq_add_of_div_eq_zero (mask_parts hK1 ρ n x).2.1
  show (x, (y ^^^ maskOf K ρ (n + 1 - 1) x) ^^^
      2 ^ (ρ + (n + 1 - 1) * K) * bitAt x (ρ + (n + 1 - 1) * K), z) =
    (x, y ^^^ ∑ i ∈ Finset.range (n + 1), 2 ^ (ρ + i * K) * bitAt x (ρ + i * K), z)
  rw [Nat.add_sub_cancel, Finset.sum_range_succ, Nat.xor_assoc, key]
  rfl

end SubNLogN.Math.Networks
