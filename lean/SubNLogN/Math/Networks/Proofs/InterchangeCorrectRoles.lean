import SubNLogN.Math.Networks.Proofs.InterchangeCorrectCoords

/-!
# Proposition A.7 (`prop:transfer11`) correctness: the role classes of a bit-network node

At a node in class `c` with `W_b` roles (`RowClass.sub`, `roleIdx`, `rolePos`, `aligned` of
`AppCModel.lean`), role `w` of the bit network is the role class `c.sub W_b (roleIdxB w)`. The point
`(H, D, y)` of role `k` is the address `roleAddr c Q h₀ d₀ b k H D y`: `y` moved to role `k` at the
same position (`aligned`), then its `H` and `D` chunks overwritten. `roleState` reads a physical array
as one array on `ChunkAddr 100 Q L.Addr` per role (`H`, `D` indexed by the cube via `cubeEquiv`).
Needs `c.μ · W_b ∣ r_row` (the aligned row values exist) and the row field before both chunks.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-- Hypotheses on one node of the recursion (block width `b`). -/
structure NodeHyp (L : Layout) (q h₀ d₀ b : ℕ) (c : RowClass L) : Prop where
  two : TwoChunks L q h₀ d₀ b
  row : c.row.val < h₀
  div : c.μ * Wb ∣ L.r c.row

/-- The address of the point `(H, D, y)` of role `k`: `y` moved to role `k` (same position), then
its two chunks overwritten by `H` and `D`. -/
noncomputable def roleAddr (c : RowClass L) (Q h₀ d₀ b : ℕ) (k : ℕ) (H D : Fin mH → ZMod Q)
    (y : L.Addr) : L.Addr :=
  setCoords L Q d₀ b (setCoords L Q h₀ b (aligned c Wb y k) H) D

/-- The role state of a physical array at a bit-network node in class `c`. -/
noncomputable def roleState {β : Type} (c : RowClass L) (Q h₀ d₀ b : ℕ) (A : L.Addr → β) :
    Role .bit 100 → (ChunkAddr 100 Q L.Addr → β) :=
  fun w z => A (roleAddr c Q h₀ d₀ b (roleIdxB w) (fun i => z.1 (cubeEquiv.symm i))
    (fun i => z.2.1 (cubeEquiv.symm i)) z.2.2)

namespace RolesProof

/-! ### Helpers: mixed-radix arithmetic of row classes, `withRow`, `setCoords` vs the row field -/

theorem mod_mul_iff (μ W res k v : ℕ) (hμ : 0 < μ) (hres : res < μ) :
    v % (μ * W) = res + μ * k ↔ v % μ = res ∧ (v / μ) % W = k := by
  rw [Nat.mod_mul]
  constructor
  · intro h
    have ha : v % μ < μ := Nat.mod_lt _ hμ
    have h1 : (v % μ + μ * (v / μ % W)) % μ = (res + μ * k) % μ := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hres] at h1
    refine ⟨h1, ?_⟩
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left hμ (by omega)
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem withRow_ne (row : Fin L.n) (x : L.Addr) (v : ℕ) {j : Fin L.n} (hj : j ≠ row) :
    withRow row x v j = x j := by
  unfold withRow
  split_ifs
  · exact Function.update_of_ne hj _ _
  · rfl

theorem withRow_withRow (row : Fin L.n) (x : L.Addr) {v₁ v₂ : ℕ} (h₁ : v₁ < L.r row)
    (h₂ : v₂ < L.r row) : withRow row (withRow row x v₁) v₂ = withRow row x v₂ := by
  unfold withRow
  rw [dif_pos h₁, dif_pos h₂, dif_pos h₂]
  exact Function.update_idem _ _ _

/-- The aligned row value stays in range (complete role streams, `c.μ · W_b ∣ r_row`). -/
theorem aligned_val_lt (c : RowClass L) {W : ℕ} (hW : 0 < W) (hdiv : c.μ * W ∣ L.r c.row)
    (x : L.Addr) (k' : ℕ) (hk' : k' < W) : c.res + c.μ * (k' + W * rolePos c W x) < L.r c.row := by
  obtain ⟨N, hN⟩ := hdiv
  have hx : (x c.row).val < c.μ * W * N := lt_of_lt_of_eq (x c.row).isLt hN
  have hp : rolePos c W x < N := by
    unfold rolePos
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos c.hμ hW)]
    linarith [mul_comm (c.μ * W) N]
  have hres := c.hres
  have h3 : W * (rolePos c W x + 1) ≤ W * N := Nat.mul_le_mul_left _ hp
  have h4 : W * (rolePos c W x + 1) = W * rolePos c W x + W := by ring
  calc c.res + c.μ * (k' + W * rolePos c W x) < c.μ + c.μ * (k' + W * rolePos c W x) := by
        omega
    _ = c.μ * (k' + 1 + W * rolePos c W x) := by ring
    _ ≤ c.μ * (W * N) := Nat.mul_le_mul_left _ (by omega)
    _ = L.r c.row := by rw [hN]; ring

theorem aligned_row (c : RowClass L) {W : ℕ} (hW : 0 < W) (hdiv : c.μ * W ∣ L.r c.row)
    (x : L.Addr) (k' : ℕ) (hk' : k' < W) :
    (aligned c W x k' c.row).val = c.res + c.μ * (k' + W * rolePos c W x) := by
  unfold aligned withRow
  rw [dif_pos (aligned_val_lt c hW hdiv x k' hk'), Function.update_self]

theorem rolePos_aligned (c : RowClass L) {W : ℕ} (hW : 0 < W) (hdiv : c.μ * W ∣ L.r c.row)
    (x : L.Addr) (k' : ℕ) (hk' : k' < W) : rolePos c W (aligned c W x k') = rolePos c W x := by
  show ((aligned c W x k' c.row).val / c.μ) / W = rolePos c W x
  rw [aligned_row c hW hdiv x k' hk', Nat.add_mul_div_left _ _ c.hμ, Nat.div_eq_of_lt c.hres,
    zero_add, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hk', zero_add]

theorem withRow_aligned (c : RowClass L) {W : ℕ} (hW : 0 < W) (hdiv : c.μ * W ∣ L.r c.row)
    (y : L.Addr) (k k' : ℕ) (hk : k < W) (hk' : k' < W) :
    withRow c.row (aligned c W y k) (c.res + c.μ * (k' + W * rolePos c W y)) =
      aligned c W y k' := by
  unfold aligned
  exact withRow_withRow c.row y (aligned_val_lt c hW hdiv y k hk)
    (aligned_val_lt c hW hdiv y k' hk')

theorem setCoords_apply_congr {Q t₀ b : ℕ} {y z : L.Addr} (X : Fin mH → ZMod Q) (j : Fin L.n)
    (h : y j = z j) : setCoords L Q t₀ b y X j = setCoords L Q t₀ b z X j := by
  unfold setCoords
  split_ifs with hj
  · unfold Layout.blockSet
    split_ifs
    · rfl
    · exact h
  · exact h

theorem setCoords_withRow {Q t₀ b : ℕ} (row : Fin L.n) (hrow : row.val < t₀) (x : L.Addr)
    (v : ℕ) (X : Fin mH → ZMod Q) :
    setCoords L Q t₀ b (withRow row x v) X = withRow row (setCoords L Q t₀ b x X) v := by
  funext j
  by_cases hj : j = row
  · subst hj
    rw [setCoords_of_not _ _ _ (by omega)]
    unfold withRow
    split_ifs with hv
    · simp only [Function.update_self]
    · rw [setCoords_of_not _ _ _ (by omega)]
  · rw [withRow_ne _ _ _ hj]
    exact setCoords_apply_congr X j (withRow_ne row x v hj)

theorem row_lt_d₀ {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) :
    c.row.val < d₀ := by
  have := hN.two.HD
  have := hN.row
  omega

/-- The row field of `roleAddr` is that of `aligned`. -/
theorem roleAddr_row {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) {Q : ℕ}
    (k : ℕ) (H D : Fin mH → ZMod Q) (y : L.Addr) :
    roleAddr c Q h₀ d₀ b k H D y c.row = aligned c Wb y k c.row := by
  have h1 := row_lt_d₀ hN
  have h2 := hN.row
  unfold roleAddr
  rw [setCoords_of_not _ _ _ (by omega), setCoords_of_not _ _ _ (by omega)]

/-- `mem_sub_iff` for an arbitrary number of roles (`W` kept abstract: never evaluate `W_b`). -/
theorem mem_sub_iff_gen (c : RowClass L) {W : ℕ} (hW : 0 < W) (k : Fin W) (x : L.Addr) :
    (c.sub W hW k).mem x ↔ c.mem x ∧ roleIdx c W hW x = k := by
  show (x c.row).val % (c.μ * W) = c.res + c.μ * k.val ↔
    (x c.row).val % c.μ = c.res ∧ roleIdx c W hW x = k
  rw [Fin.ext_iff]
  exact mod_mul_iff c.μ W c.res k.val (x c.row).val c.hμ c.hres

end RolesProof

open RolesProof

theorem mem_sub_iff (c : RowClass L) (k : Fin Wb) (x : L.Addr) :
    (c.sub Wb Wb_pos k).mem x ↔ c.mem x ∧ roleIdx c Wb Wb_pos x = k := by
  exact mem_sub_iff_gen c Wb_pos k x

theorem roleAddr_mem_class {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (k : Fin Wb) (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    c.mem (roleAddr c (q ^ b) h₀ d₀ b k H D y) := by
  show (roleAddr c (q ^ b) h₀ d₀ b k H D y c.row).val % c.μ = c.res
  rw [roleAddr_row hN, aligned_row c Wb_pos hN.div y k k.isLt, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt c.hres]

theorem roleIdx_roleAddr {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (k : Fin Wb) (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    roleIdx c Wb Wb_pos (roleAddr c (q ^ b) h₀ d₀ b k H D y) = k := by
  apply Fin.ext
  show (roleAddr c (q ^ b) h₀ d₀ b k H D y c.row).val / c.μ % Wb = k.val
  rw [roleAddr_row hN, aligned_row c Wb_pos hN.div y k k.isLt, Nat.add_mul_div_left _ _ c.hμ,
    Nat.div_eq_of_lt c.hres, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]

theorem roleAddr_mem {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) (k : Fin Wb)
    (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    (c.sub Wb Wb_pos k).mem (roleAddr c (q ^ b) h₀ d₀ b k H D y) :=
  (mem_sub_iff c k _).2 ⟨roleAddr_mem_class hN k H D y, roleIdx_roleAddr hN k H D y⟩

theorem aligned_roleAddr {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (k k' : Fin Wb) (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    aligned c Wb (roleAddr c (q ^ b) h₀ d₀ b k H D y) k' = roleAddr c (q ^ b) h₀ d₀ b k' H D y := by
  have hrd := row_lt_d₀ hN
  have hp : rolePos c Wb (roleAddr c (q ^ b) h₀ d₀ b k H D y) = rolePos c Wb y := by
    show (roleAddr c (q ^ b) h₀ d₀ b k H D y c.row).val / c.μ / Wb = rolePos c Wb y
    rw [roleAddr_row hN]
    exact rolePos_aligned c Wb_pos hN.div y k k.isLt
  show withRow c.row (roleAddr c (q ^ b) h₀ d₀ b k H D y)
    (c.res + c.μ * (k'.val + Wb * rolePos c Wb (roleAddr c (q ^ b) h₀ d₀ b k H D y))) = _
  rw [hp]
  unfold roleAddr
  rw [← setCoords_withRow c.row hrd, ← setCoords_withRow c.row hN.row,
    withRow_aligned c Wb_pos hN.div y k k' k.isLt k'.isLt]

theorem coords_roleAddr {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) (k : ℕ)
    (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    coords L (q ^ b) h₀ b (roleAddr c (q ^ b) h₀ d₀ b k H D y) = H ∧
      coords L (q ^ b) d₀ b (roleAddr c (q ^ b) h₀ d₀ b k H D y) = D := by
  unfold roleAddr
  exact ⟨by rw [coords_setCoords_D hN.two, coords_setCoords hN.two.H],
    coords_setCoords hN.two.D _ _⟩

theorem setCoords_H_roleAddr {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) (k : ℕ)
    (H D H' : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    setCoords L (q ^ b) h₀ b (roleAddr c (q ^ b) h₀ d₀ b k H D y) H' =
      roleAddr c (q ^ b) h₀ d₀ b k H' D y := by
  unfold roleAddr
  rw [← setCoords_comm hN.two, setCoords_setCoords]

theorem setCoords_D_roleAddr {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) (k : ℕ)
    (H D D' : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    setCoords L (q ^ b) d₀ b (roleAddr c (q ^ b) h₀ d₀ b k H D y) D' =
      roleAddr c (q ^ b) h₀ d₀ b k H D' y := by
  unfold roleAddr
  rw [setCoords_setCoords]

/-- Every address of `c` is the point `(H(x), D(x), x)` of its own role. -/
theorem roleAddr_self {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) (x : L.Addr)
    (hx : c.mem x) :
    roleAddr c (q ^ b) h₀ d₀ b (roleIdx c Wb Wb_pos x) (coords L (q ^ b) h₀ b x)
      (coords L (q ^ b) d₀ b x) x = x := by
  have hv : c.res + c.μ * ((roleIdx c Wb Wb_pos x).val + Wb * rolePos c Wb x) = (x c.row).val := by
    have h1 := Nat.div_add_mod (x c.row).val c.μ
    have h2 := Nat.div_add_mod ((x c.row).val / c.μ) Wb
    have hm : (x c.row).val % c.μ = c.res := hx
    show c.res + c.μ * (((x c.row).val / c.μ) % Wb + Wb * (((x c.row).val / c.μ) / Wb)) =
      (x c.row).val
    rw [← hm, (Nat.add_comm _ _).trans h2]
    exact (Nat.add_comm _ _).trans h1
  have hal : aligned c Wb x (roleIdx c Wb Wb_pos x) = x := by
    unfold aligned withRow
    rw [dif_pos (by rw [hv]; exact (x c.row).isLt)]
    funext j
    rcases eq_or_ne j c.row with rfl | hj
    · rw [Function.update_self]
      exact Fin.ext hv
    · exact Function.update_of_ne hj _ _
  unfold roleAddr
  rw [hal, setCoords_coords hN.two.H, setCoords_coords hN.two.D]

/-- Arrays agreeing off `c` and with the same role state are equal. -/
theorem eq_of_roleState {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c) {β : Type}
    {A A' : L.Addr → β} (hout : ∀ x, ¬ c.mem x → A x = A' x)
    (hrs : roleState c (q ^ b) h₀ d₀ b A = roleState c (q ^ b) h₀ d₀ b A') : A = A' := by
  funext x
  by_cases hx : c.mem x
  · have key := congrFun (congrFun hrs (roleIdxB.symm (roleIdx c Wb Wb_pos x)))
      (fun p => coords L (q ^ b) h₀ b x (cubeEquiv p),
        fun p => coords L (q ^ b) d₀ b x (cubeEquiv p), x)
    simp only [roleState, Equiv.apply_symm_apply] at key
    rw [roleAddr_self hN x hx] at key
    exact key
  · exact hout x hx

end InterchangeCorrect

end SubNLogN.Math.Networks
