import SubNLogN.Math.Networks.LayoutEncoding

/-!
# Layout encoding (Step half): elementary steps on lexicographic indices

Companion of `LayoutEncoding.lean` (base half: `Layout.lexEquiv`, `idxBlock`, `idxSetBlock`, `enc`,
machine-layer list functions). Conventions shared with `Machine/Contracts/`: arrays are lists in lexicographic
address order (field `0` most significant), and address maps are given in the INVERSE convention
(the record at output index `y` is the input record at index `g y`, as in `permByInv`).

For every `Step` constructor (`AppCModel.lean`):
* `elem e` (`pair`, `shift`, `unit`): explicit index map `Elem.idx` built from `idxSetBlock` /
  `idxBlock` (`Elem.lexEquiv_pull`), `Step.run (.elem e) A = A ∘ (lexEquiv.symm ∘ e.idxFin h ∘
  lexEquiv)` (`Step.run_elem_lex`); well-formed steps are bijections (`Elem.pull_bijective`,
  `Elem.idxFin_bijective`);
* `swapBlocks`: explicit `swapIdx` (`Step.run_swapBlocks_lex`), equal to `swapFieldsInv` for
  disjoint blocks of equal range (`swapIdx_eq_swapFieldsInv`);
* `digitGate`: aligned streams at `idxSetBlock k (k+1) i v` (`Step.run_digitGate_lex`);
* `recMap`, `addrMap`, `sparsePerm`: the trivial forms; the index map of a well-formed sparse
  permutation is a bijection fixing every index outside the support (`sparsePerm_idx`);
* `Step.runIn`: the class test is the residue test on the row digit (`Step.runIn_lex`);
* list bridges `enc (s.run A) = permByInv g (enc A)` and the class-restricted version;
* the prefix form of `idxSetBlock` (for collapsed mixed shapes).
Helpers are in `SubNLogN.Math.Networks.Model.LayoutEncodingStepAux`.
-/

/-! ## Step half: elementary steps on lexicographic indices -/

namespace SubNLogN.Math.Networks.Model

variable {L : Layout}

/-! ### Elementary steps: explicit index maps (inverse convention) -/

/-- Explicit index map of an elementary step, in the inverse convention: after the step, the
record at index `i` is the record that was at index `e.idx i` (`Step.run (.elem e) A = A ∘ e.pull`).
For a shift the offset is read at the address of `i` (by `Elem.WF` it depends only on the fields
before the target block). -/
def Elem.idx : Elem L → Fin L.card → ℕ
  | .pair a b g, i =>
      L.idxSetBlock b.val (b.val + 1)
        (L.idxSetBlock a.val (a.val + 1) i.val
          (g.symm (L.lexEquiv.symm i a, L.lexEquiv.symm i b)).1.val)
        (g.symm (L.lexEquiv.symm i a, L.lexEquiv.symm i b)).2.val
  | .shift t₀ t₁ off, i =>
      L.idxSetBlock t₀ t₁ i.val
        ((L.idxBlock t₀ t₁ i.val + L.blockRange t₀ t₁ - off (L.lexEquiv.symm i) % L.blockRange t₀ t₁) %
          L.blockRange t₀ t₁)
  | .unit t₀ t₁ _ u', i =>
      L.idxSetBlock t₀ t₁ i.val (u' * L.idxBlock t₀ t₁ i.val % L.blockRange t₀ t₁)

/-- The explicit index map is the pull map read on lexicographic indices. -/
theorem Elem.lexEquiv_pull {B : ℕ} (e : Elem L) (h : e.WF B) (i : Fin L.card) :
    (L.lexEquiv (e.pull (L.lexEquiv.symm i))).val = e.idx i := by
  cases e with
  | pair a b g =>
    simp only [Elem.pull, Elem.idx]
    rw [L.lexEquiv_update, L.lexEquiv_update, Equiv.apply_symm_apply]
  | shift t₀ t₁ off =>
    obtain ⟨h₁, h₂, _⟩ : t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧ _ := h
    simp only [Elem.pull, Elem.idx]
    rw [L.lexEquiv_blockSet h₁ h₂, Equiv.apply_symm_apply, L.blockVal_lexEquiv_symm h₁ h₂]
  | unit t₀ t₁ u u' =>
    obtain ⟨h₁, h₂, _⟩ : t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧ _ := h
    simp only [Elem.pull, Elem.idx]
    rw [L.lexEquiv_blockSet h₁ h₂, Equiv.apply_symm_apply, L.blockVal_lexEquiv_symm h₁ h₂]

/-- The index map of a well-formed elementary step, as a map of `Fin L.card`. -/
def Elem.idxFin {B : ℕ} (e : Elem L) (h : e.WF B) (i : Fin L.card) : Fin L.card :=
  ⟨e.idx i, by rw [← e.lexEquiv_pull h i]; exact (L.lexEquiv _).isLt⟩

theorem Elem.idxFin_val {B : ℕ} (e : Elem L) (h : e.WF B) (i : Fin L.card) :
    (e.idxFin h i).val = e.idx i := rfl

theorem Elem.idxFin_eq {B : ℕ} (e : Elem L) (h : e.WF B) (i : Fin L.card) :
    e.idxFin h i = L.lexEquiv (e.pull (L.lexEquiv.symm i)) :=
  Fin.ext (e.lexEquiv_pull h i).symm

/-- **Elementary steps on indices**: `Step.run (.elem e) A = A ∘ (lexEquiv.symm ∘ f ∘ lexEquiv)` with
the explicit `f = e.idxFin h`. -/
theorem Step.run_elem_lex {β : Type} {B : ℕ} (e : Elem L) (h : e.WF B) (A : L.Addr → β) :
    (Step.elem e : Step L β).run A = A ∘ (L.lexEquiv.symm ∘ e.idxFin h ∘ L.lexEquiv) := by
  funext x
  simp only [Step.run, Function.comp, Elem.idxFin_eq, Equiv.symm_apply_apply]

/-! ### Block interchange -/

/-- Explicit index map of `swapBlocks t₀ s₀ len` (inverse convention). -/
def swapIdx (L : Layout) (t₀ s₀ len y : ℕ) : ℕ :=
  L.idxSetBlock s₀ (s₀ + len) (L.idxSetBlock t₀ (t₀ + len) y (L.idxBlock s₀ (s₀ + len) y))
    (L.idxBlock t₀ (t₀ + len) y)

theorem lexEquiv_swapBlocks {t₀ s₀ len : ℕ} (ht : t₀ + len ≤ L.n) (hs : s₀ + len ≤ L.n)
    (i : Fin L.card) :
    (L.lexEquiv (L.blockSet s₀ (s₀ + len)
      (L.blockSet t₀ (t₀ + len) (L.lexEquiv.symm i) (L.blockVal s₀ (s₀ + len) (L.lexEquiv.symm i)))
      (L.blockVal t₀ (t₀ + len) (L.lexEquiv.symm i)))).val = swapIdx L t₀ s₀ len i.val := by
  rw [L.lexEquiv_blockSet (Nat.le_add_right _ _) hs, L.lexEquiv_blockSet (Nat.le_add_right _ _) ht,
    Equiv.apply_symm_apply, L.blockVal_lexEquiv_symm (Nat.le_add_right _ _) hs,
    L.blockVal_lexEquiv_symm (Nat.le_add_right _ _) ht]
  rfl

/-- The index map of `swapBlocks` as a map of `Fin L.card`. -/
def swapFin {t₀ s₀ len : ℕ} (ht : t₀ + len ≤ L.n) (hs : s₀ + len ≤ L.n) (i : Fin L.card) :
    Fin L.card :=
  ⟨swapIdx L t₀ s₀ len i.val, by rw [← lexEquiv_swapBlocks ht hs i]; exact (L.lexEquiv _).isLt⟩

/-- **Block interchange on indices.** -/
theorem Step.run_swapBlocks_lex {β : Type} {t₀ s₀ len : ℕ} (ht : t₀ + len ≤ L.n)
    (hs : s₀ + len ≤ L.n) (A : L.Addr → β) :
    (Step.swapBlocks t₀ s₀ len : Step L β).run A = A ∘ (L.lexEquiv.symm ∘ swapFin ht hs ∘ L.lexEquiv) := by
  funext x
  have h := lexEquiv_swapBlocks ht hs (L.lexEquiv x)
  rw [Equiv.symm_apply_apply] at h
  simp only [Step.run, Function.comp]
  refine congrArg A ?_
  rw [Equiv.eq_symm_apply]
  exact Fin.ext h

/-! ### Digit gates, record maps, sparse permutations -/

/-- The index of the address of `i` with field `k` set to `v` (aligned stream `v` of the split at
field `k`). -/
def Layout.digitUpd (L : Layout) (i : Fin L.card) (k : Fin L.n) (v : Fin (L.r k)) :
    Fin L.card :=
  L.lexEquiv (Function.update (L.lexEquiv.symm i) k v)

theorem Layout.digitUpd_val (L : Layout) (i : Fin L.card) (k : Fin L.n) (v : Fin (L.r k)) :
    (L.digitUpd i k v).val = L.idxSetBlock k.val (k.val + 1) i.val v.val := by
  rw [Layout.digitUpd, L.lexEquiv_update, Equiv.apply_symm_apply]

/-- **Digit gate on indices**: the aligned stream `v` of index `i` is at index
`idxSetBlock k (k+1) i v`, and the gate output is selected by the digit `idxBlock k (k+1) i`. -/
theorem Step.run_digitGate_lex {β : Type} (k : Fin L.n)
    (G : (Fin (L.r k) → β) → (Fin (L.r k) → β)) (A : L.Addr → β) (i : Fin L.card) :
    (Step.digitGate k G : Step L β).run A (L.lexEquiv.symm i) =
      G (fun v => A (L.lexEquiv.symm (L.digitUpd i k v))) (L.lexEquiv.symm i k) := by
  simp only [Step.run, Layout.digitUpd, Equiv.symm_apply_apply]

theorem Layout.digit_lexEquiv_symm (L : Layout) (i : Fin L.card) (k : Fin L.n) :
    (L.lexEquiv.symm i k).val = L.idxBlock k.val (k.val + 1) i.val := by
  rw [L.lexEquiv_symm_val, L.idxBlock_single]

theorem Step.run_recMap_lex {β : Type} (f : β → β) (A : L.Addr → β) :
    (Step.recMap f : Step L β).run A ∘ L.lexEquiv.symm = f ∘ (A ∘ L.lexEquiv.symm) := rfl

theorem Step.run_addrMap_lex {β : Type} (f : L.Addr → β → β) (A : L.Addr → β) :
    (Step.addrMap f : Step L β).run A ∘ L.lexEquiv.symm =
      fun i => f (L.lexEquiv.symm i) (A (L.lexEquiv.symm i)) := rfl

theorem Step.run_sparsePerm_lex {β : Type} (pull : L.Addr → L.Addr) (supp : Finset L.Addr)
    (A : L.Addr → β) :
    (Step.sparsePerm pull supp : Step L β).run A =
      A ∘ (L.lexEquiv.symm ∘ (L.lexEquiv ∘ pull ∘ L.lexEquiv.symm) ∘ L.lexEquiv) := by
  funext x
  simp only [Step.run, Function.comp, Equiv.symm_apply_apply]

/-- Under `Step.WF`, the index map of a sparse permutation is a bijection of `Fin L.card` that fixes
every index outside `lexEquiv '' supp`. -/
theorem sparsePerm_idx {β : Type} {B : ℕ} (pull : L.Addr → L.Addr) (supp : Finset L.Addr)
    (h : (Step.sparsePerm pull supp : Step L β).WF B) :
    Function.Bijective (L.lexEquiv ∘ pull ∘ L.lexEquiv.symm) ∧
      ∀ i : Fin L.card, L.lexEquiv.symm i ∉ supp → (L.lexEquiv ∘ pull ∘ L.lexEquiv.symm) i = i := by
  obtain ⟨hb, hs⟩ : Function.Bijective pull ∧ ∀ x, x ∉ supp → pull x = x := h
  refine ⟨L.lexEquiv.bijective.comp (hb.comp L.lexEquiv.symm.bijective), fun i hi => ?_⟩
  simp only [Function.comp, hs _ hi, Equiv.apply_symm_apply]

/-! ### Steps restricted to a row class -/

/-- **Class-restricted steps on indices**: the class test is a residue test on the row digit of the
index. -/
theorem Step.runIn_lex {β : Type} (c : RowClass L) (s : Step L β) (A : L.Addr → β)
    (i : Fin L.card) :
    s.runIn c A (L.lexEquiv.symm i) =
      if L.idxBlock c.row.val (c.row.val + 1) i.val % c.μ = c.res then s.run A (L.lexEquiv.symm i)
      else A (L.lexEquiv.symm i) := by
  simp only [Step.runIn]
  by_cases hm : c.mem (L.lexEquiv.symm i)
  · rw [if_pos hm, if_pos ((RowClass.mem_lexEquiv_symm c i).1 hm)]
  · rw [if_neg hm, if_neg (fun h' => hm ((RowClass.mem_lexEquiv_symm c i).2 h'))]

/-! ### List bridges (list conventions: `enc` and `permByInv`) -/

/-- The class-restricted index map of an elementary step (identity off the class). -/
def Elem.idxIn (c : RowClass L) (e : Elem L) (y : ℕ) : ℕ :=
  if hy : y < L.card then
    (if L.idxBlock c.row.val (c.row.val + 1) y % c.μ = c.res then e.idx ⟨y, hy⟩ else y)
  else y

theorem enc_run_elem {β : Type} [Inhabited β] {B : ℕ} (e : Elem L) (h : e.WF B)
    (A : L.Addr → β) :
    L.enc ((Step.elem e : Step L β).run A) =
      permByInv (fun y => if hy : y < L.card then e.idx ⟨y, hy⟩ else y) (L.enc A) := by
  show L.enc (A ∘ e.pull) = _
  exact L.enc_comp A e.pull _ (fun y hy => by rw [dif_pos hy, e.lexEquiv_pull h])

theorem enc_runIn_elem {β : Type} [Inhabited β] {B : ℕ} (c : RowClass L) (e : Elem L)
    (h : e.WF B) (A : L.Addr → β) :
    L.enc ((Step.elem e : Step L β).runIn c A) = permByInv (Elem.idxIn c e) (L.enc A) := by
  have hrun : (Step.elem e : Step L β).runIn c A =
      A ∘ (fun x => if c.mem x then e.pull x else x) := by
    funext x
    simp only [Step.runIn, Step.run, Function.comp]
    split_ifs <;> rfl
  rw [hrun]
  refine L.enc_comp A _ _ (fun y hy => ?_)
  simp only [Elem.idxIn, dif_pos hy]
  by_cases hm : L.idxBlock c.row.val (c.row.val + 1) y % c.μ = c.res
  · rw [if_pos hm, if_pos ((RowClass.mem_lexEquiv_symm c ⟨y, hy⟩).2 hm), e.lexEquiv_pull h]
  · rw [if_neg hm, if_neg (fun h' => hm ((RowClass.mem_lexEquiv_symm c ⟨y, hy⟩).1 h')),
      Equiv.apply_symm_apply]

theorem enc_run_swapBlocks {β : Type} [Inhabited β] {t₀ s₀ len : ℕ} (ht : t₀ + len ≤ L.n)
    (hs : s₀ + len ≤ L.n) (A : L.Addr → β) :
    L.enc ((Step.swapBlocks t₀ s₀ len : Step L β).run A) =
      permByInv (swapIdx L t₀ s₀ len) (L.enc A) := by
  rw [Step.run_swapBlocks_lex ht hs]
  refine L.enc_comp A _ _ (fun y hy => ?_)
  simp only [Function.comp, Equiv.apply_symm_apply]
  rfl

/-! ### Prefix form of a block overwrite (collapsed shapes `[np] × [R] × [T]`) -/

theorem Layout.idxSetBlock_eq (L : Layout) (t₀ t₁ y v : ℕ) :
    L.idxSetBlock t₀ t₁ y v =
      y / (L.blockRange t₁ L.n * L.blockRange t₀ t₁) * (L.blockRange t₁ L.n * L.blockRange t₀ t₁) +
        v % L.blockRange t₀ t₁ * L.blockRange t₁ L.n + y % L.blockRange t₁ L.n := by
  unfold Layout.idxSetBlock Layout.idxBlock
  generalize L.blockRange t₁ L.n = T
  generalize L.blockRange t₀ t₁ = R
  have h1 := Nat.div_add_mod y T
  have h2 := Nat.div_add_mod (y / T) R
  rw [Nat.div_div_eq_div_mul] at h2
  have hy : y = y / (T * R) * (T * R) + y / T % R * T + y % T :=
    calc y = T * (y / T) + y % T := h1.symm
      _ = T * (R * (y / (T * R)) + y / T % R) + y % T := by rw [h2]
      _ = y / (T * R) * (T * R) + y / T % R * T + y % T := by ring
  omega

end SubNLogN.Math.Networks.Model

/-! ## Bijectivity of well-formed elementary steps -/

namespace SubNLogN.Math.Networks.Model

variable {L : Layout}

namespace LayoutEncodingStepAux

open LayoutEncodingAux

theorem blockSet_blockSet' (t₀ t₁ : ℕ) (x : L.Addr) (v v' : ℕ) :
    L.blockSet t₀ t₁ (L.blockSet t₀ t₁ x v) v' = L.blockSet t₀ t₁ x v' := by
  funext j
  by_cases hj : inBlock t₀ t₁ j
  · simp only [Layout.blockSet, if_pos hj]
  · simp only [Layout.blockSet, if_neg hj]

theorem blockSet_apply_of_not' {t₀ t₁ : ℕ} (x : L.Addr) (v : ℕ) (j : Fin L.n)
    (hj : ¬ inBlock t₀ t₁ j) : L.blockSet t₀ t₁ x v j = x j := by
  simp only [Layout.blockSet, if_neg hj]

theorem update_update_pair {a b : Fin L.n} (hab : a ≠ b) (x : L.Addr) (u u' : Fin (L.r a))
    (w w' : Fin (L.r b)) :
    Function.update (Function.update (Function.update (Function.update x a u) b w) a u') b w' =
      Function.update (Function.update x a u') b w' := by
  funext j
  by_cases hjb : j = b
  · subst hjb
    simp only [Function.update_self]
  · by_cases hja : j = a
    · subst hja
      simp only [Function.update_of_ne hjb, Function.update_self]
    · simp only [Function.update_of_ne hjb, Function.update_of_ne hja]

/-- `((v + R − o) mod R + o) mod R = v` for `v < R`, `o < R`. -/
theorem mod_sub_add {v R o : ℕ} (hv : v < R) (ho : o < R) : ((v + R - o) % R % R + o) % R = v := by
  rw [Nat.mod_mod, Nat.mod_add_mod, show v + R - o + o = v + R by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hv]

/-- `((v + o) mod R + R − o) mod R = v` for `v < R`, `o < R`. -/
theorem mod_add_sub {v R o : ℕ} (hv : v < R) (ho : o < R) : ((v + o) % R % R + R - o) % R = v := by
  rw [Nat.mod_mod, Nat.add_sub_assoc (le_of_lt ho), Nat.mod_add_mod,
    show v + o + (R - o) = v + R by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hv]

/-- `(a · ((b · v) mod R)) mod R = v` if `a b ≡ 1 (mod R)` and `v < R`. -/
theorem mul_mod_inv {a b v R : ℕ} (hab : a * b % R = 1 % R) (hv : v < R) :
    a * (b * v % R) % R = v := by
  rw [Nat.mul_mod_mod, ← mul_assoc, Nat.mul_mod, hab, ← Nat.mul_mod, one_mul, Nat.mod_eq_of_lt hv]

end LayoutEncodingStepAux

open LayoutEncodingAux LayoutEncodingStepAux

/-- A well-formed elementary step is a bijection of addresses. -/
theorem Elem.pull_bijective {B : ℕ} (e : Elem L) (h : e.WF B) : Function.Bijective e.pull := by
  cases e with
  | pair a b g =>
    obtain ⟨hab, _, _⟩ : a ≠ b ∧ L.r a ≤ B ∧ L.r b ≤ B := h
    have hpa : ∀ (x : L.Addr) (u : Fin (L.r a)) (w : Fin (L.r b)),
        Function.update (Function.update x a u) b w a = u := fun x u w => by
      rw [Function.update_of_ne hab, Function.update_self]
    have hpb : ∀ (x : L.Addr) (u : Fin (L.r a)) (w : Fin (L.r b)),
        Function.update (Function.update x a u) b w b = w := fun x u w => Function.update_self _ _ _
    refine Function.bijective_iff_has_inverse.2
      ⟨fun x => Function.update (Function.update x a (g (x a, x b)).1) b (g (x a, x b)).2,
        fun x => ?_, fun x => ?_⟩
    · simp only [Elem.pull, hpa, hpb, Prod.mk.eta, Equiv.apply_symm_apply, update_update_pair hab,
        Function.update_eq_self]
    · simp only [Elem.pull, hpa, hpb, Prod.mk.eta, Equiv.symm_apply_apply, update_update_pair hab,
        Function.update_eq_self]
  | shift t₀ t₁ off =>
    obtain ⟨_, _, hoff⟩ : t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧
        ∀ x y : L.Addr, (∀ i : Fin L.n, i.val < t₀ → x i = y i) → off x = off y := h
    have hoffset : ∀ (x : L.Addr) (v : ℕ), off (L.blockSet t₀ t₁ x v) = off x := fun x v =>
      hoff _ _ (fun i hi => blockSet_apply_of_not' x v i (fun hin => by
        have := hin.1
        omega))
    refine Function.bijective_iff_has_inverse.2
      ⟨fun x => L.blockSet t₀ t₁ x ((L.blockVal t₀ t₁ x + off x % L.blockRange t₀ t₁) %
          L.blockRange t₀ t₁), fun x => ?_, fun x => ?_⟩
    · have hR := blockRange_pos x t₀ t₁
      simp only [Elem.pull]
      rw [hoffset, blockVal_blockSet, blockSet_blockSet',
        mod_sub_add (blockVal_lt t₀ t₁ x) (Nat.mod_lt _ hR), blockSet_blockVal]
    · have hR := blockRange_pos x t₀ t₁
      simp only [Elem.pull]
      rw [hoffset, blockVal_blockSet, blockSet_blockSet',
        mod_add_sub (blockVal_lt t₀ t₁ x) (Nat.mod_lt _ hR), blockSet_blockVal]
  | unit t₀ t₁ u u' =>
    obtain ⟨_, _, huu⟩ : t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧
        (u * u') % L.blockRange t₀ t₁ = 1 % L.blockRange t₀ t₁ := h
    have hu'u : u' * u % L.blockRange t₀ t₁ = 1 % L.blockRange t₀ t₁ := by rw [mul_comm]; exact huu
    refine Function.bijective_iff_has_inverse.2
      ⟨fun x => L.blockSet t₀ t₁ x (u * L.blockVal t₀ t₁ x % L.blockRange t₀ t₁),
        fun x => ?_, fun x => ?_⟩
    · simp only [Elem.pull]
      rw [blockVal_blockSet, Nat.mod_mod, blockSet_blockSet',
        mul_mod_inv huu (blockVal_lt t₀ t₁ x), blockSet_blockVal]
    · simp only [Elem.pull]
      rw [blockVal_blockSet, Nat.mod_mod, blockSet_blockSet',
        mul_mod_inv hu'u (blockVal_lt t₀ t₁ x), blockSet_blockVal]

/-- The explicit index map of a well-formed elementary step is a permutation of `Fin L.card`. -/
theorem Elem.idxFin_bijective {B : ℕ} (e : Elem L) (h : e.WF B) :
    Function.Bijective (e.idxFin h) := by
  have : e.idxFin h = L.lexEquiv ∘ e.pull ∘ L.lexEquiv.symm := funext (e.idxFin_eq h)
  rw [this]
  exact L.lexEquiv.bijective.comp ((e.pull_bijective h).comp L.lexEquiv.symm.bijective)

end SubNLogN.Math.Networks.Model

/-! ## `swapBlocks` as `swapFieldsInv` (`Machine/Contracts/AppC.lean`) -/

namespace SubNLogN.Math.Networks.Model

variable {L : Layout}

namespace LayoutEncodingStepAux

/-- If `y = m * q + r` with `r < m`, then `y / m = q` and `y % m = r`. -/
theorem divmod_of {y m q r : ℕ} (hr : r < m) (hy : y = m * q + r) : y / m = q ∧ y % m = r :=
  (Nat.div_mod_unique (lt_of_le_of_lt (Nat.zero_le _) hr)).2 ⟨by rw [hy]; ring, hr⟩

theorem lt_mix {q Q r M : ℕ} (hq : q < Q) (hr : r < M) : M * q + r < M * Q :=
  calc M * q + r < M * q + M := by omega
    _ = M * (q + 1) := by ring
    _ ≤ M * Q := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)

/-- The arithmetic of the block interchange in the collapsed shape `[A] × [R] × [G] × [R] × [B]`. -/
theorem swap_arith (y R G B : ℕ) (hR : 0 < R) (hG : 0 < G) (hB : 0 < B) :
    (y / (G * (R * B) * R) * (G * (R * B) * R) + y / B % R % R * (G * (R * B)) +
          y % (G * (R * B))) / (B * R) * (B * R) +
        y / (G * (R * B)) % R % R * B +
        (y / (G * (R * B) * R) * (G * (R * B) * R) + y / B % R % R * (G * (R * B)) +
          y % (G * (R * B))) % B =
      (((y / (B * R * G * R) * R + y / B % R) * G + y / (B * R) % G) * R + y / (B * R * G) % R) * B +
        y % B := by
  have e1 : G * (R * B) * R = B * R * G * R := by ring
  have e2 : G * (R * B) = B * R * G := by ring
  rw [e1, e2]
  obtain ⟨a, t, g, h, z, hz, hh, hg, ht, hy⟩ : ∃ a t g h z : ℕ, z < B ∧ h < R ∧ g < G ∧ t < R ∧
      y = B * (R * (G * (R * a + t) + g) + h) + z := by
    refine ⟨y / (B * R * G * R), y / (B * R * G) % R, y / (B * R) % G, y / B % R, y % B,
      Nat.mod_lt _ hB, Nat.mod_lt _ hR, Nat.mod_lt _ hG, Nat.mod_lt _ hR, ?_⟩
    have r1 := (Nat.div_add_mod y B).symm
    have r2 := (Nat.div_add_mod (y / B) R).symm
    have r3 := (Nat.div_add_mod (y / B / R) G).symm
    have r4 := (Nat.div_add_mod (y / B / R / G) R).symm
    simp only [Nat.div_div_eq_div_mul] at r2 r3 r4
    rw [r4] at r3
    rw [r3] at r2
    rw [r2] at r1
    exact r1
  have b1 : B * h + z < B * R := lt_mix hh hz
  have b2 : B * R * g + (B * h + z) < B * R * G := lt_mix hg b1
  have b3 : B * R * G * t + (B * R * g + (B * h + z)) < B * R * G * R := lt_mix ht b2
  have q1 : y / (B * R * G * R) = a :=
    (divmod_of b3 (by rw [hy]; ring)).1
  have q2 : y / B % R = h := by
    rw [(divmod_of hz (q := R * (G * (R * a + t) + g) + h) hy).1]
    exact (divmod_of hh (q := G * (R * a + t) + g) rfl).2
  have q3 : y / (B * R) % G = g := by
    rw [(divmod_of b1 (q := G * (R * a + t) + g) (by rw [hy]; ring)).1]
    exact (divmod_of hg (q := R * a + t) rfl).2
  have q4 : y / (B * R * G) % R = t := by
    rw [(divmod_of b2 (q := R * a + t) (by rw [hy]; ring)).1]
    exact (divmod_of ht (q := a) rfl).2
  have q5 : y % (B * R * G) = B * R * g + (B * h + z) :=
    (divmod_of b2 (q := R * a + t) (by rw [hy]; ring)).2
  have q6 : y % B = z := (divmod_of hz (q := R * (G * (R * a + t) + g) + h) hy).2
  rw [q1, q2, q3, q4, q5, q6, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt ht]
  have q7 : (a * (B * R * G * R) + h * (B * R * G) + (B * R * g + (B * h + z))) / (B * R) =
      a * G * R + h * G + g := (divmod_of b1 (by ring)).1
  have q8 : (a * (B * R * G * R) + h * (B * R * G) + (B * R * g + (B * h + z))) % B = z :=
    (divmod_of hz (q := R * (a * G * R + h * G + g) + h) (by ring)).2
  rw [q7, q8]
  ring

end LayoutEncodingStepAux

open LayoutEncodingAux LayoutEncodingStepAux

/-- For two disjoint blocks of equal range `R` (`t₀ + len ≤ s₀`), the index map of `swapBlocks` is
`swapFieldsInv R G R B` (`G` the range between the blocks, `B` the range after `s₀ + len`). -/
theorem swapIdx_eq_swapFieldsInv {t₀ s₀ len : ℕ} (hts : t₀ + len ≤ s₀) (hs : s₀ + len ≤ L.n)
    (hR : L.blockRange t₀ (t₀ + len) = L.blockRange s₀ (s₀ + len))
    (hpos : 0 < L.blockRange t₀ (t₀ + len) ∧ 0 < L.blockRange (t₀ + len) s₀ ∧
      0 < L.blockRange (s₀ + len) L.n) (y : ℕ) :
    swapIdx L t₀ s₀ len y =
      swapFieldsInv (L.blockRange s₀ (s₀ + len)) (L.blockRange (t₀ + len) s₀)
        (L.blockRange s₀ (s₀ + len)) (L.blockRange (s₀ + len) L.n) y := by
  have hT : L.blockRange (t₀ + len) L.n =
      L.blockRange (t₀ + len) s₀ * (L.blockRange s₀ (s₀ + len) * L.blockRange (s₀ + len) L.n) := by
    rw [blockRange_split hts (le_trans (Nat.le_add_right _ _) hs),
      blockRange_split (Nat.le_add_right _ _) hs]
  obtain ⟨h1, h2, h3⟩ := hpos
  rw [hR] at h1
  unfold swapIdx swapFieldsInv
  rw [L.idxSetBlock_eq, L.idxSetBlock_eq]
  simp only [Layout.idxBlock]
  rw [hT, hR]
  exact swap_arith y _ _ _ h1 h2 h3

/-- The well-formed (blocks inside the layout, positive ranges) index map of `swapBlocks` on
`Fin L.card` agrees with `swapFieldsInv` below `L.card`. -/
theorem swapFin_eq_swapFieldsInv {t₀ s₀ len : ℕ} (ht : t₀ + len ≤ L.n) (hts : t₀ + len ≤ s₀)
    (hs : s₀ + len ≤ L.n) (hR : L.blockRange t₀ (t₀ + len) = L.blockRange s₀ (s₀ + len))
    (i : Fin L.card) :
    (swapFin ht hs i).val =
      swapFieldsInv (L.blockRange s₀ (s₀ + len)) (L.blockRange (t₀ + len) s₀)
        (L.blockRange s₀ (s₀ + len)) (L.blockRange (s₀ + len) L.n) i.val := by
  have hx : L.Addr := L.lexEquiv.symm i
  exact swapIdx_eq_swapFieldsInv hts hs hR
    ⟨blockRange_pos hx _ _, blockRange_pos hx _ _, blockRange_pos hx _ _⟩ i.val

end SubNLogN.Math.Networks.Model
