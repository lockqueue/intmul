import SubNLogN.Math.Networks.LayoutEncoding2

/-!
# Layout encoding, part 3: node operations of a class, transported to its role array

For a row class `c` with `c.μ ∣ r row`, the list of `c` is the list of the role array `A ∘ e_c` on
`L_c = roleLayout c.row c.μ`, where `e_c = roleEmbed c.row c.μ ⟨c.res, _⟩` (`roleBlocks_enc`). If
moreover `c.μ · W ∣ r row`, a node with `W` roles in class `c` acts on that role array exactly as a
node split on the whole role array:
* `gateRun_comp_roleEmbed : gateRun c W G A ∘ e_c = gateRun (top) W G (A ∘ e_c)`;
* `relabelRun_comp_roleEmbed`: the same for `relabelRun`;
* outside `c` nothing changes (`gateRun_of_not_mem`, `relabelRun_of_not_mem`), so the lists of the
  other classes `(c.row, c.μ, k)` are unchanged (`roleBlocks_enc_gateRun_ne`, …).
With `dvd_roleLayout_r` (`W ∣ r_c row`) the top-level list lemmas of `LayoutEncoding2.lean`
(`roleBlocks_enc`, `enc_gateRun`, `enc_relabelRun`, `enc_reassemble`) apply on `L_c`, which gives the
list form of nested node operations.
-/

namespace SubNLogN.Math.Networks.Model

open LayoutEncodingAux

namespace Layout

variable (L : Layout)

theorem dvd_roleLayout_r (c : RowClass L) {W : ℕ} (hμW : c.μ * W ∣ L.r c.row) :
    W ∣ (L.roleLayout c.row c.μ).r c.row := by
  rw [L.roleLayout_r_self]
  obtain ⟨m, hm⟩ := hμW
  rw [hm, Nat.mul_assoc, Nat.mul_div_cancel_left _ c.hμ]
  exact Dvd.intro m rfl

theorem dvd_of_mul_dvd (c : RowClass L) {W : ℕ} (hμW : c.μ * W ∣ L.r c.row) : c.μ ∣ L.r c.row :=
  Dvd.dvd.trans (Dvd.intro W rfl) hμW

theorem gateRun_of_not_mem {β : Type} (A : L.Addr → β) (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (G : (Fin W → β) → (Fin W → β)) {x : L.Addr} (hx : ¬ c.mem x) :
    gateRun c W hW G A x = A x := by
  show (if c.mem x then _ else _) = _
  exact if_neg hx

theorem relabelRun_of_not_mem {β : Type} (A : L.Addr → β) (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (π : Equiv.Perm (Fin W)) {x : L.Addr} (hx : ¬ c.mem x) :
    relabelRun c W hW π A x = A x := by
  show (if c.mem x then _ else _) = _
  exact if_neg hx

theorem roleEmbed_res_apply_self (c : RowClass L) (hμr : c.μ ∣ L.r c.row)
    (x' : (L.roleLayout c.row c.μ).Addr) :
    (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x' c.row).val = (x' c.row).val * c.μ + c.res :=
  L.roleEmbed_apply_self hμr _ x'

theorem roleIdx_roleEmbed (c : RowClass L) (hμr : c.μ ∣ L.r c.row) {W : ℕ} (hW : 0 < W)
    (x' : (L.roleLayout c.row c.μ).Addr) :
    roleIdx c W hW (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') =
      roleIdx (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW x' := by
  apply Fin.ext
  show (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x' c.row).val / c.μ % W =
    (x' c.row).val / 1 % W
  rw [L.roleEmbed_res_apply_self c hμr x', Nat.div_one, Nat.add_comm,
    Nat.add_mul_div_right _ _ c.hμ, Nat.div_eq_of_lt c.hres, zero_add]

theorem aligned_roleEmbed (c : RowClass L) (hμr : c.μ ∣ L.r c.row) {W : ℕ} (hW : 0 < W)
    (hμW : c.μ * W ∣ L.r c.row) (k' : Fin W) (x' : (L.roleLayout c.row c.μ).Addr) :
    aligned c W (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') k'.val =
      L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ (aligned (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W x' k'.val) := by
  have hx'lt : (x' c.row).val < L.r c.row / c.μ :=
    lt_of_lt_of_eq (x' c.row).isLt (L.roleLayout_r_self c.row c.μ)
  obtain ⟨m, hm⟩ := hμW
  have hrμ : L.r c.row / c.μ = W * m := by
    rw [hm, Nat.mul_assoc, Nat.mul_div_cancel_left _ c.hμ]
  rw [hrμ] at hx'lt
  have hq : (x' c.row).val / W < m := by
    rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]
    exact hx'lt
  have hv' : k'.val + W * ((x' c.row).val / W) < W * m := by
    have h2 : W * ((x' c.row).val / W) + W ≤ W * m := by
      calc W * ((x' c.row).val / W) + W = W * ((x' c.row).val / W + 1) := by ring
        _ ≤ W * m := Nat.mul_le_mul_left _ hq
    have := k'.isLt
    omega
  have hv'L : k'.val + W * ((x' c.row).val / W) < (L.roleLayout c.row c.μ).r c.row :=
    lt_of_lt_of_eq hv' (by rw [L.roleLayout_r_self, hrμ])
  have hv : c.res + c.μ * (k'.val + W * ((x' c.row).val / W)) < L.r c.row := by
    have h1 : ∀ v : ℕ, c.res + c.μ * v < c.μ * (v + 1) := by
      intro v
      rw [Nat.mul_succ]
      have := c.hres
      omega
    calc c.res + c.μ * (k'.val + W * ((x' c.row).val / W))
        < c.μ * (k'.val + W * ((x' c.row).val / W) + 1) := h1 _
      _ ≤ c.μ * (W * m) := Nat.mul_le_mul_left _ hv'
      _ = L.r c.row := by rw [hm]; ring
  have hposc : rolePos c W (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') =
      (x' c.row).val / W := by
    show (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x' c.row).val / c.μ / W = _
    rw [L.roleEmbed_res_apply_self c hμr x', Nat.add_comm, Nat.add_mul_div_right _ _ c.hμ,
      Nat.div_eq_of_lt c.hres, zero_add]
  have hpost : rolePos (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W x' = (x' c.row).val / W := by
    show (x' c.row).val / 1 / W = _
    rw [Nat.div_one]
  unfold aligned
  rw [hposc, hpost]
  show withRow c.row (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x')
      (c.res + c.μ * (k'.val + W * ((x' c.row).val / W))) =
    L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩
      (withRow c.row x' (0 + 1 * (k'.val + W * ((x' c.row).val / W))))
  rw [zero_add, one_mul]
  unfold withRow
  rw [dif_pos hv, dif_pos hv'L]
  funext i
  by_cases hi : i = c.row
  · rw [hi, Function.update_self]
    apply Fin.ext
    rw [L.roleEmbed_apply_self, Function.update_self]
    show c.res + c.μ * (k'.val + W * ((x' c.row).val / W)) =
      (k'.val + W * ((x' c.row).val / W)) * c.μ + c.res
    ring
  · rw [Function.update_of_ne hi]
    apply Fin.ext
    rw [L.roleEmbed_apply_of_ne hμr _ _ hi, L.roleEmbed_apply_of_ne hμr _ _ hi,
      Function.update_of_ne hi]

/-- **Gate transport**: a gate on the `W` roles of class `c` acts on `c`'s role array as a gate on a
split of the whole role array. -/
theorem gateRun_comp_roleEmbed {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ} (hW : 0 < W)
    (hμr : c.μ ∣ L.r c.row) (hμW : c.μ * W ∣ L.r c.row) (G : (Fin W → β) → (Fin W → β)) :
    gateRun c W hW G A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ =
      gateRun (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW G (A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩) := by
  funext x'
  show (if c.mem (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') then _ else _) =
    (if (RowClass.top (L := L.roleLayout c.row c.μ) c.row).mem x' then _ else _)
  rw [if_pos ((L.mem_roleEmbed c hμr ⟨c.res, c.hres⟩ x').2 rfl),
    if_pos ((L.roleLayout c.row c.μ).top_mem c.row x'), L.roleIdx_roleEmbed c hμr hW x']
  congr 1
  funext k'
  rw [L.aligned_roleEmbed c hμr hW hμW k' x']
  rfl

/-- **Relabel transport**: a relabelling of the `W` roles of class `c` acts on `c`'s role array as a
relabelling of a split of the whole role array. -/
theorem relabelRun_comp_roleEmbed {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ}
    (hW : 0 < W) (hμr : c.μ ∣ L.r c.row) (hμW : c.μ * W ∣ L.r c.row) (π : Equiv.Perm (Fin W)) :
    relabelRun c W hW π A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ =
      relabelRun (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW π (A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩) := by
  funext x'
  show (if c.mem (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') then _ else _) =
    (if (RowClass.top (L := L.roleLayout c.row c.μ) c.row).mem x' then _ else _)
  rw [if_pos ((L.mem_roleEmbed c hμr ⟨c.res, c.hres⟩ x').2 rfl),
    if_pos ((L.roleLayout c.row c.μ).top_mem c.row x'), L.roleIdx_roleEmbed c hμr hW x',
    L.aligned_roleEmbed c hμr hW hμW (π.symm (roleIdx (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW x')) x']
  rfl

/-! ### List forms -/

theorem roleBlocks_enc_gateRun_self {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ}
    (hW : 0 < W) (hμr : c.μ ∣ L.r c.row) (hμW : c.μ * W ∣ L.r c.row)
    (G : (Fin W → β) → (Fin W → β)) :
    roleBlocks c.μ c.res (L.place L.n c.row) (L.enc (gateRun c W hW G A)) =
      (L.roleLayout c.row c.μ).enc
        (gateRun (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW G (A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩)) := by
  refine (L.roleBlocks_enc (gateRun c W hW G A) c.row c.hμ hμr ⟨c.res, c.hres⟩).trans ?_
  rw [L.gateRun_comp_roleEmbed A c hW hμr hμW G]

theorem roleBlocks_enc_gateRun_ne {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ}
    (hW : 0 < W) (hμr : c.μ ∣ L.r c.row) (G : (Fin W → β) → (Fin W → β)) (k : Fin c.μ)
    (hk : k.val ≠ c.res) :
    roleBlocks c.μ k.val (L.place L.n c.row) (L.enc (gateRun c W hW G A)) =
      roleBlocks c.μ k.val (L.place L.n c.row) (L.enc A) := by
  rw [L.roleBlocks_enc _ c.row c.hμ hμr k, L.roleBlocks_enc _ c.row c.hμ hμr k]
  congr 1
  funext x'
  exact L.gateRun_of_not_mem A c W hW G (fun h => hk ((L.mem_roleEmbed c hμr k x').1 h))

theorem roleBlocks_enc_relabelRun_self {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ}
    (hW : 0 < W) (hμr : c.μ ∣ L.r c.row) (hμW : c.μ * W ∣ L.r c.row) (π : Equiv.Perm (Fin W)) :
    roleBlocks c.μ c.res (L.place L.n c.row) (L.enc (relabelRun c W hW π A)) =
      (L.roleLayout c.row c.μ).enc
        (relabelRun (RowClass.top (L := L.roleLayout c.row c.μ) c.row) W hW π (A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩)) := by
  refine (L.roleBlocks_enc (relabelRun c W hW π A) c.row c.hμ hμr ⟨c.res, c.hres⟩).trans ?_
  rw [L.relabelRun_comp_roleEmbed A c hW hμr hμW π]

theorem roleBlocks_enc_relabelRun_ne {β : Type} (A : L.Addr → β) (c : RowClass L) {W : ℕ}
    (hW : 0 < W) (hμr : c.μ ∣ L.r c.row) (π : Equiv.Perm (Fin W)) (k : Fin c.μ)
    (hk : k.val ≠ c.res) :
    roleBlocks c.μ k.val (L.place L.n c.row) (L.enc (relabelRun c W hW π A)) =
      roleBlocks c.μ k.val (L.place L.n c.row) (L.enc A) := by
  rw [L.roleBlocks_enc _ c.row c.hμ hμr k, L.roleBlocks_enc _ c.row c.hμ hμr k]
  congr 1
  funext x'
  exact L.relabelRun_of_not_mem A c W hW π (fun h => hk ((L.mem_roleEmbed c hμr k x').1 h))

end Layout

end SubNLogN.Math.Networks.Model
