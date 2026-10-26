import SubNLogN.Math.Networks.AppCProc
import SubNLogN.Math.Networks.Proofs.FrameInvariant

/-!
# Networks: well-formedness of the explicit Proposition A.7 (`prop:transfer11`) procedure

`interchangeProcWF_holds : InterchangeProcWFStmt` (`AppCProc.lean`): under `InterchangeHyps`, every
primitive of `interchangeProc q fac k h₀ d₀` satisfies its side condition at the radix bound `q`
(`ProcK.WF`, `AppCModel.lean`). The row class plays no role. The proof is an induction on `k` with
the class-free hypotheses `InterchangeWFAux.WFHyps` (prime `q`, valid factorizations, radix-`q`
fields in both chunks, `h₀ + m^k ≤ d₀`, `d₀ + m^k ≤ L.n`), which the children of a node inherit:

* depth `0`: one `Elem.pair` of two distinct radix-`q` fields;
* shifts (`D ← D − H`, `D ← H − D`, the lower-triangular steps and the pivot shifts of Lemma A.6 (`lem:transfer-shear`)): the
  offset reads only `H`-blocks, which end before `d₀`, or earlier blocks of the same chunk
  (`blockVal` depends only on the fields of its block);
* units: a block of `b` radix-`q` fields has range `q^b`; `(R − 1)² ≡ 1 (mod R)`, and a diagonal
  entry `r` of a valid factorization has `ratMod R r · ratMod R r⁻¹ = 1` (`q ∤ den r`, `q ∤ num r`);
* gates: the row at `(j, ι, r)` changes only wires touched at `(j, ι, r)` (`FI.rowUpd_untouched`)
  and on such a wire reads only wires of the same gate (`FI.rowUpd_local`, `FI.gateAt_eq_some_iff`);
* child calls: by induction; relabellings are well formed by definition.

All helper lemmas live in the namespace `SubNLogN.Math.Networks.InterchangeWFAux`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeWFAux

/-! ### Blocks of fields -/

theorem mem_filter_inBlock {n t₀ t₁ : ℕ} {j : Fin n} :
    j ∈ Finset.univ.filter (inBlock t₀ t₁ (n := n)) ↔ t₀ ≤ j.val ∧ j.val < t₁ := by
  simp [inBlock]

/-- The block `[t₀, t₁)` has `t₁ - t₀` fields when `t₁ ≤ n`. -/
theorem card_filter_inBlock {n t₀ t₁ : ℕ} (h : t₁ ≤ n) :
    (Finset.univ.filter (inBlock t₀ t₁ (n := n))).card = t₁ - t₀ := by
  have hmap : (Finset.univ.filter (inBlock t₀ t₁ (n := n))).map Fin.valEmbedding =
      Finset.Ico t₀ t₁ := by
    ext x
    simp only [Finset.mem_map, mem_filter_inBlock, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]

/-- A block of radix-`q` fields `[t₀, t₁)` (with `t₁ ≤ n`) has range `q^(t₁ - t₀)`. -/
theorem blockRange_eq_pow {L : Layout} {q t₀ t₁ : ℕ} (h1n : t₁ ≤ L.n)
    (hr : ∀ l : Fin L.n, t₀ ≤ l.val → l.val < t₁ → L.r l = q) :
    L.blockRange t₀ t₁ = q ^ (t₁ - t₀) := by
  unfold Layout.blockRange
  rw [Finset.prod_congr rfl (fun l hl => hr l (mem_filter_inBlock.1 hl).1
    (mem_filter_inBlock.1 hl).2), Finset.prod_const, card_filter_inBlock h1n]

/-- The value of the block `[t₀, t₁)` depends only on the fields before `t₁`. -/
theorem blockVal_congr {L : Layout} {t₀ t₁ : ℕ} {x y : L.Addr}
    (hxy : ∀ i : Fin L.n, i.val < t₁ → x i = y i) :
    L.blockVal t₀ t₁ x = L.blockVal t₀ t₁ y := by
  unfold Layout.blockVal
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hxy j (mem_filter_inBlock.1 hj).2]

/-! ### The coordinate blocks `blk t₀ b i` of a chunk -/

theorem fin_mul_add_le (i : Fin mH) (b : ℕ) : i.val * b + b ≤ mH * b := by
  have h := Nat.mul_le_mul_right b (show i.val + 1 ≤ mH from i.isLt)
  rw [add_one_mul] at h
  exact h

theorem blk_fst_le_snd (t₀ b : ℕ) (i : Fin mH) : (blk t₀ b i).1 ≤ (blk t₀ b i).2 := by
  show t₀ + i.val * b ≤ t₀ + (i.val + 1) * b
  rw [add_one_mul]
  omega

theorem blk_snd_le (t₀ b : ℕ) (i : Fin mH) : (blk t₀ b i).2 ≤ t₀ + mH * b := by
  show t₀ + (i.val + 1) * b ≤ t₀ + mH * b
  have := fin_mul_add_le i b
  rw [add_one_mul]
  omega

theorem blk_fst_ge (t₀ b : ℕ) (i : Fin mH) : t₀ ≤ (blk t₀ b i).1 := by
  show t₀ ≤ t₀ + i.val * b
  omega

theorem blk_snd_le_fst_of_lt (t₀ b : ℕ) {i j : Fin mH} (hji : j < i) :
    (blk t₀ b j).2 ≤ (blk t₀ b i).1 := by
  show t₀ + (j.val + 1) * b ≤ t₀ + i.val * b
  have := Nat.mul_le_mul_right b (show j.val + 1 ≤ i.val from hji)
  omega

/-- A coordinate block of a radix-`q` chunk of `m` blocks of `b` fields has range `q^b`. -/
theorem blockRange_blk {L : Layout} {q t₀ b : ℕ} (i : Fin mH) (hn : t₀ + mH * b ≤ L.n)
    (hr : ∀ l : Fin L.n, t₀ ≤ l.val → l.val < t₀ + mH * b → L.r l = q) :
    L.blockRange (blk t₀ b i).1 (blk t₀ b i).2 = q ^ b := by
  have h1 := fin_mul_add_le i b
  have e : (i.val + 1) * b = i.val * b + b := add_one_mul _ _
  show L.blockRange (t₀ + i.val * b) (t₀ + (i.val + 1) * b) = q ^ b
  rw [blockRange_eq_pow (by omega) (fun l hl1 hl2 => hr l (by omega) (by omega))]
  congr 1
  omega

/-- A block value read before the target position `t` is unchanged by changes at or after `t`. -/
theorem blockVal_blk_congr {L : Layout} {s₀ b t : ℕ} (j : Fin mH) (hle : (blk s₀ b j).2 ≤ t)
    {x y : L.Addr} (hxy : ∀ i : Fin L.n, i.val < t → x i = y i) :
    L.blockVal (blk s₀ b j).1 (blk s₀ b j).2 x = L.blockVal (blk s₀ b j).1 (blk s₀ b j).2 y :=
  blockVal_congr (fun i hi => hxy i (lt_of_lt_of_le hi hle))

/-! ### Units modulo `R = q^b` -/

/-- `(R − 1)² ≡ 1 (mod R)` for `R > 0`. -/
theorem sub_one_mul_sub_one_mod {R : ℕ} (hR : 0 < R) : ((R - 1) * (R - 1)) % R = 1 % R := by
  obtain ⟨s, rfl⟩ : ∃ s, R = s + 1 := ⟨R - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← ZMod.natCast_eq_natCast_iff']
  have h : ((s : ℕ) : ZMod (s + 1)) = -1 := by
    have h1 : ((s + 1 : ℕ) : ZMod (s + 1)) = 0 := ZMod.natCast_self _
    push_cast at h1
    linear_combination h1
  push_cast
  rw [h]
  ring

/-- `ratMod n` is multiplicative on rationals with denominators prime to `n`. -/
theorem ratMod_mul_of_coprime (n : ℕ) {x y : ℚ} (hx : Nat.Coprime x.den n)
    (hy : Nat.Coprime y.den n) : ratMod n (x * y) = ratMod n x * ratMod n y := by
  have hxy : Nat.Coprime (x.den * y.den) n := Nat.Coprime.mul_left hx hy
  have hden : Nat.Coprime (x * y).den n :=
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd x y) hxy
  have hrep : (x * y) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) := by
    have h1 : x * x.den = x.num := Rat.mul_den_eq_num x
    have h2 : y * y.den = y.num := Rat.mul_den_eq_num y
    push_cast
    rw [← h1, ← h2]
    ring
  rw [FI.ratMod_eq_of_mul n (x * y) _ _ hxy hden hrep]
  have hu := ZMod.coe_mul_inv_eq_one x.den hx
  have hv := ZMod.coe_mul_inv_eq_one y.den hy
  have hw := ZMod.coe_mul_inv_eq_one (x.den * y.den) hxy
  set W := (((x.den * y.den : ℕ) : ZMod n))⁻¹ with hW
  rw [Nat.cast_mul] at hw
  unfold ratMod
  push_cast
  linear_combination
    (-(x.num : ZMod n) * (y.num : ZMod n) * W * (y.den : ZMod n) * ((y.den : ZMod n))⁻¹) * hu
    + (-(x.num : ZMod n) * (y.num : ZMod n) * W) * hv
    + ((x.num : ZMod n) * (y.num : ZMod n) * ((x.den : ZMod n))⁻¹ * ((y.den : ZMod n))⁻¹) * hw

/-- A rational `r` with `q ∤ den r` and `q ∤ num r` is a unit modulo `q^b`, with inverse
`ratMod (q^b) r⁻¹`. -/
theorem ratMod_mul_inv {q : ℕ} (hq : q.Prime) (b : ℕ) {r : ℚ} (hden : QIntegral q r)
    (hnum : ¬ (q : ℤ) ∣ r.num) : ratMod (q ^ b) r * ratMod (q ^ b) r⁻¹ = 1 := by
  have hr0 : r ≠ 0 := by
    intro h
    apply hnum
    rw [h]
    simp
  have hx : Nat.Coprime r.den (q ^ b) := FI.coprime_of_qIntegral hq b hden
  have hy : Nat.Coprime (r⁻¹).den (q ^ b) := by
    rw [Rat.den_inv_of_ne_zero hr0]
    have h : ¬ q ∣ r.num.natAbs := fun h => hnum (Int.ofNat_dvd_left.2 h)
    exact Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hq).2 h).symm
  rw [← ratMod_mul_of_coprime _ hx hy, mul_inv_cancel₀ hr0, FI.ratMod_one]

/-- The unit condition of a diagonal step: `u · u' ≡ 1 (mod q^b)` for `u = ratModNat (q^b) r`,
`u' = ratModNat (q^b) r⁻¹`. -/
theorem unit_mod {q : ℕ} (hq : q.Prime) (b : ℕ) {r : ℚ} (hden : QIntegral q r)
    (hnum : ¬ (q : ℤ) ∣ r.num) :
    (ratModNat (q ^ b) r * ratModNat (q ^ b) r⁻¹) % (q ^ b) = 1 % (q ^ b) := by
  have : NeZero (q ^ b) := ⟨pow_ne_zero _ hq.ne_zero⟩
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  simp only [ratModNat, ZMod.natCast_zmod_val]
  exact ratMod_mul_inv hq b hden hnum

/-- Diagonal entries that are units at `q`: `q`-integral with numerator prime to `q`. -/
def UnitDiag (q : ℕ) (E : Matrix (Fin mH) (Fin mH) ℚ) : Prop :=
  ∀ i, QIntegral q (E i i) ∧ ¬ (q : ℤ) ∣ (E i i).num

/-- The four factors of a valid factorization have unit diagonals. -/
theorem unitDiag_of_valid {q : ℕ} {A : Matrix (Fin mH) (Fin mH) ℚ} {F : FacData}
    (hV : F.Valid q A) :
    UnitDiag q F.E₁ ∧ UnitDiag q F.E₁' ∧ UnitDiag q F.E₂ ∧ UnitDiag q F.E₂' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, hN⟩ := hV
  exact ⟨fun i => ⟨(hQ i i).1, (hN i).1⟩, fun i => ⟨(hQ i i).2.1, (hN i).2.1⟩,
    fun i => ⟨(hQ i i).2.2.1, (hN i).2.2.1⟩, fun i => ⟨(hQ i i).2.2.2, (hN i).2.2.2⟩⟩

/-! ### Well-formedness of single steps -/

theorem wf_pair {L : Layout} {β : Type} {B : ℕ} {i j : Fin L.n}
    {g : Equiv.Perm (Fin (L.r i) × Fin (L.r j))} (hij : i ≠ j) (hi : L.r i ≤ B) (hj : L.r j ≤ B) :
    Step.WF (β := β) B (.elem (.pair i j g)) :=
  ⟨hij, hi, hj⟩

theorem wf_shift {L : Layout} {β : Type} {B t₀ t₁ : ℕ} {off : L.Addr → ℕ}
    (h01 : t₀ ≤ t₁) (h1n : t₁ ≤ L.n)
    (hoff : ∀ x y : L.Addr, (∀ i : Fin L.n, i.val < t₀ → x i = y i) → off x = off y) :
    Step.WF (β := β) B (.elem (.shift t₀ t₁ off)) :=
  ⟨h01, h1n, hoff⟩

theorem wf_unit {L : Layout} {β : Type} {B t₀ t₁ u u' : ℕ} (h01 : t₀ ≤ t₁) (h1n : t₁ ≤ L.n)
    (hu : (u * u') % L.blockRange t₀ t₁ = 1 % L.blockRange t₀ t₁) :
    Step.WF (β := β) B (.elem (.unit t₀ t₁ u u' : Elem L)) :=
  ⟨h01, h1n, hu⟩

theorem wf_prim {L : Layout} {β : Type} {W : ℕ} {Child : Type} {cwf : Child → Prop} {B : ℕ}
    (k : Fin W) {s : Step L β} (hs : Step.WF B s) : RoleOp.WF cwf B (.prim k s) :=
  hs

/-! ### Step lists of a node -/

/-- The lower-triangular steps on a radix-`q` chunk: units on the diagonal (unit diagonal entries),
shifts reading only earlier coordinate blocks. -/
theorem wf_lowerSteps {L : Layout} {β : Type} {q t₀ b : ℕ} (hq : q.Prime)
    (hn : t₀ + mH * b ≤ L.n) (hr : ∀ l : Fin L.n, t₀ ≤ l.val → l.val < t₀ + mH * b → L.r l = q)
    {E : Matrix (Fin mH) (Fin mH) ℚ} (hE : UnitDiag q E) :
    ∀ s ∈ lowerSteps (L := L) (β := β) (q ^ b) t₀ b E, Step.WF q s := by
  intro s hs
  obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact wf_unit (blk_fst_le_snd t₀ b i) (le_trans (blk_snd_le t₀ b i) hn)
      (by rw [blockRange_blk i hn hr]; exact unit_mod hq b (hE i).1 (hE i).2)
  · exact wf_shift (blk_fst_le_snd t₀ b i) (le_trans (blk_snd_le t₀ b i) hn)
      (fun x y hxy => Finset.sum_congr rfl (fun j hj =>
        congrArg (fun v => ratModNat (q ^ b) (E i j) * v)
          (blockVal_blk_congr j (blk_snd_le_fst_of_lt t₀ b (Finset.mem_filter.1 hj).2) hxy)))

/-- `D_i ← D_i − H_i`: shifts of the `D`-blocks reading `H`-blocks (which end before `d₀`). -/
theorem wf_subHSteps {L : Layout} {β : Type} {q h₀ d₀ b : ℕ} (hH : h₀ + mH * b ≤ d₀)
    (hD : d₀ + mH * b ≤ L.n) (R : ℕ) :
    ∀ s ∈ subHSteps (L := L) (β := β) R h₀ d₀ b, Step.WF q s := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
  have hle : (blk h₀ b i).2 ≤ (blk d₀ b i).1 :=
    le_trans (blk_snd_le h₀ b i) (le_trans hH (blk_fst_ge d₀ b i))
  exact wf_shift (blk_fst_le_snd d₀ b i) (le_trans (blk_snd_le d₀ b i) hD)
    (fun x y hxy => congrArg (fun v => R - v % R) (blockVal_blk_congr i hle hxy))

/-- `D_i ← H_i − D_i`: a unit `R − 1` and a shift reading `H_i`. -/
theorem wf_hMinusDSteps {L : Layout} {β : Type} {q h₀ d₀ b : ℕ} (hq : q.Prime)
    (hH : h₀ + mH * b ≤ d₀) (hD : d₀ + mH * b ≤ L.n)
    (hrD : ∀ l : Fin L.n, d₀ ≤ l.val → l.val < d₀ + mH * b → L.r l = q) :
    ∀ s ∈ hMinusDSteps (L := L) (β := β) (q ^ b) h₀ d₀ b, Step.WF q s := by
  intro s hs
  obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
  have hle : (blk h₀ b i).2 ≤ (blk d₀ b i).1 :=
    le_trans (blk_snd_le h₀ b i) (le_trans hH (blk_fst_ge d₀ b i))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact wf_unit (blk_fst_le_snd d₀ b i) (le_trans (blk_snd_le d₀ b i) hD)
      (by rw [blockRange_blk i hD hrD]; exact sub_one_mul_sub_one_mod (pow_pos hq.pos b))
  · exact wf_shift (blk_fst_le_snd d₀ b i) (le_trans (blk_snd_le d₀ b i) hD)
      (fun x y hxy => blockVal_blk_congr i hle hxy)

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of one edge (`shearOps`) is well formed: lower-triangular steps on both chunks,
and per pivot two shifts reading an `H`-block, a unit `R − 1` and a child call. -/
theorem wf_shearOps {L : Layout} {β : Type} {W : ℕ} {Child : Type} {cwf : Child → Prop}
    {q h₀ d₀ b : ℕ} (hq : q.Prime) (hH : h₀ + mH * b ≤ d₀) (hD : d₀ + mH * b ≤ L.n)
    (hrH : ∀ l : Fin L.n, h₀ ≤ l.val → l.val < h₀ + mH * b → L.r l = q)
    (hrD : ∀ l : Fin L.n, d₀ ≤ l.val → l.val < d₀ + mH * b → L.r l = q)
    {F : FacData} (h1 : UnitDiag q F.E₁) (h1' : UnitDiag q F.E₁') (h2 : UnitDiag q F.E₂)
    (h2' : UnitDiag q F.E₂') {childOf : Fin mH → Fin mH → Child}
    (hch : ∀ i j, cwf (childOf i j)) (kk : Fin W) :
    ∀ o ∈ shearOps (L := L) (β := β) (q ^ b) h₀ d₀ b kk F childOf, RoleOp.WF cwf q o := by
  have hHn : h₀ + mH * b ≤ L.n := by omega
  have hlow : ∀ (t₀ : ℕ) (E : Matrix (Fin mH) (Fin mH) ℚ), t₀ + mH * b ≤ L.n →
      (∀ l : Fin L.n, t₀ ≤ l.val → l.val < t₀ + mH * b → L.r l = q) → UnitDiag q E →
      ∀ o ∈ (lowerSteps (L := L) (β := β) (q ^ b) t₀ b E).map (RoleOp.prim (Child := Child) kk),
        RoleOp.WF cwf q o := by
    intro t₀ E hn hr hE o ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact wf_prim kk (wf_lowerSteps hq hn hr hE s hs)
  intro o ho
  unfold shearOps at ho
  simp only [List.mem_append] at ho
  rcases ho with (((ho | ho) | ho) | ho) | ho
  · exact hlow d₀ F.E₂ hD hrD h2 o ho
  · exact hlow h₀ F.E₁' hHn hrH h1' o ho
  · obtain ⟨p, -, ho⟩ := List.mem_flatMap.1 ho
    have hle : (blk h₀ b p.1).2 ≤ (blk d₀ b p.2).1 :=
      le_trans (blk_snd_le h₀ b p.1) (le_trans hH (blk_fst_ge d₀ b p.2))
    have hsh : Step.WF (β := β) q (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
        (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x))) :=
      wf_shift (blk_fst_le_snd d₀ b p.2) (le_trans (blk_snd_le d₀ b p.2) hD)
        (fun x y hxy => blockVal_blk_congr p.1 hle hxy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact wf_prim kk hsh
    · exact hch p.1 p.2
    · exact wf_prim kk (wf_unit (blk_fst_le_snd d₀ b p.2) (le_trans (blk_snd_le d₀ b p.2) hD)
        (by rw [blockRange_blk p.2 hD hrD]; exact sub_one_mul_sub_one_mod (pow_pos hq.pos b)))
    · exact wf_prim kk hsh
  · exact hlow h₀ F.E₁ hHn hrH h1 o ho
  · exact hlow d₀ F.E₂' hD hrD h2' o ho

/-! ### Gates, edges and the node -/

/-- Membership in the image of a filtered `univ` under an equivalence (stated for an arbitrary
`Fintype`, so that it is applied by rewriting, never by evaluating `univ`). -/
theorem mem_map_filter_iff {α γ : Type*} [Fintype α] (e : α ≃ γ) (p : α → Prop) [DecidablePred p]
    (k : γ) : k ∈ (Finset.univ.filter p).map e.toEmbedding ↔ p (e.symm k) := by
  rw [Finset.mem_map_equiv, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The gate at `(j, ι, r)` reads and changes only the roles touched at `(j, ι, r)`. -/
theorem wf_gateOpB {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    {cwf : Child → Prop} (B : ℕ) (j : Stage) (ι : Fix 100) (r : Fin 8) :
    RoleOp.WF cwf B (gateOpB (L := L) (β := β) (Child := Child) j ι r) := by
  simp only [gateOpB, RoleOp.WF, mem_map_filter_iff]
  refine ⟨fun v v' hvv' k hk => ?_, fun v k hk => ?_⟩
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hk
    refine FI.rowUpd_local (0 : ZMod 2) j ι r _ g _ _ (fun w' hw' => ?_) _ hg
    have h2 : (gateAt j ι r (roleIdxB.symm (roleIdxB w'))).isSome = true := by
      rw [Equiv.symm_apply_apply]
      exact Option.isSome_iff_exists.2
        ⟨g, FI.gateAt_eq_some_iff.2 ⟨hw', (FI.gateAt_eq_some_iff.1 hg).2⟩⟩
    exact hvv' (roleIdxB w') h2
  · have hnone : gateAt j ι r (roleIdxB.symm k) = none := by
      cases hg : gateAt j ι r (roleIdxB.symm k) with
      | none => rfl
      | some g => exact absurd (Option.isSome_iff_exists.2 ⟨g, hg⟩) hk
    exact (FI.rowUpd_untouched (0 : ZMod 2) j ι r _ _ _ hnone).trans (by simp)

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of the edge of `w` entering `v` is well formed (if there is one, its
factorization is valid). -/
theorem wf_edgeOpsB {L : Layout} {β : Type} {Child : Type} {cwf : Child → Prop} {q h₀ d₀ b : ℕ}
    (hq : q.Prime) (hH : h₀ + mH * b ≤ d₀) (hD : d₀ + mH * b ≤ L.n)
    (hrH : ∀ l : Fin L.n, h₀ ≤ l.val → l.val < h₀ + mH * b → L.r l = q)
    (hrD : ∀ l : Fin L.n, d₀ ≤ l.val → l.val < d₀ + mH * b → L.r l = q)
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hval : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {childOf : Fin mH → Fin mH → Child} (hch : ∀ i j, cwf (childOf i j))
    (w : Role .bit 100) (v : Vertex .bit 100) :
    ∀ o ∈ edgeOpsB (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf w v, RoleOp.WF cwf q o := by
  intro o ho
  unfold edgeOpsB at ho
  cases he : edgeInto w v with
  | none =>
    rw [he] at ho
    simp at ho
  | some e =>
    rw [he] at ho
    obtain ⟨h1, h1', h2, h2'⟩ := unitDiag_of_valid (hval w e (FI.edgeInto_mem he))
    exact wf_shearOps hq hH hD hrH hrD h1 h1' h2 h2' hch (roleIdxB w) o ho

/-- All role operations of a bit-network node are well formed, given well-formed edge programs. -/
theorem wf_bitNodeOps {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    {cwf : Child → Prop} {B R h₀ d₀ b : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    {childOf : Fin mH → Fin mH → Child}
    (hedge : ∀ (w : Role .bit 100) (v : Vertex .bit 100),
      ∀ o ∈ edgeOpsB (L := L) (β := β) R h₀ d₀ b fac childOf w v, RoleOp.WF cwf B o) :
    ∀ o ∈ bitNodeOps (L := L) (β := β) R h₀ d₀ b fac childOf, RoleOp.WF cwf B o := by
  intro o ho
  unfold bitNodeOps at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨j, -, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨ι, -, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨r, -, ho⟩ := List.mem_flatMap.1 ho
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
        cases hg : gateAt j ι r w with
        | none =>
          rw [hg] at ho
          simp at ho
        | some g =>
          rw [hg] at ho
          exact hedge w (.gate g) o ho
      · rw [List.mem_singleton] at ho
        subst ho
        exact wf_gateOpB B j ι r
    · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
      exact hedge w (.sink w) o ho
  · rw [List.mem_singleton] at ho
    subst ho
    trivial

/-! ### The induction on the depth -/

/-- Class-free hypotheses of the well-formedness induction (inherited by the children of a node). -/
structure WFHyps (L : Layout) (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (k h₀ d₀ : ℕ) : Prop where
  prime : q.Prime
  valid : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e)
  radix : ∀ i : Fin L.n, (h₀ ≤ i.val ∧ i.val < h₀ + mH ^ k) ∨ (d₀ ≤ i.val ∧ i.val < d₀ + mH ^ k) →
    L.r i = q
  hd : h₀ + mH ^ k ≤ d₀
  dn : d₀ + mH ^ k ≤ L.n

theorem interchangeProc_zero {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (h₀ d₀ : ℕ) :
    (interchangeProc (L := L) (β := β) q fac 0 h₀ d₀ : List (Step L β)) =
      if hh : h₀ < L.n ∧ d₀ < L.n then
        [Step.elem (Elem.pair ⟨h₀, hh.1⟩ ⟨d₀, hh.2⟩ (finSwapPerm _ _))]
      else [] :=
  rfl

theorem interchangeProc_succ {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀ : List (Model.Op L β (ProcK L β k))) =
      (subHSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim ++
        [Model.Op.node Wb Wb_pos (bitNodeOps (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
          (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
            (d₀ + j.val * mH ^ k)))] ++
        (hMinusDSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim := by
  simp only [interchangeProc]

/-- Depth `0`: one interchange of two distinct radix-`q` fields. -/
theorem wf_zero {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {h₀ d₀ : ℕ} (H : WFHyps L q fac 0 h₀ d₀) :
    ProcK.WF q 0 (interchangeProc (L := L) (β := β) q fac 0 h₀ d₀) := by
  obtain ⟨-, -, hrad, hhd, hdn⟩ := H
  rw [pow_zero] at hrad hhd hdn
  have hh : h₀ < L.n ∧ d₀ < L.n := ⟨by omega, by omega⟩
  intro s hs
  simp only [id] at hs
  rw [interchangeProc_zero (L := L) (β := β) q fac h₀ d₀, dif_pos hh, List.mem_singleton] at hs
  subst hs
  refine wf_pair (fun hij => ?_) (hrad ⟨h₀, hh.1⟩ (Or.inl ⟨le_refl h₀, Nat.lt_succ_self h₀⟩)).le
    (hrad ⟨d₀, hh.2⟩ (Or.inr ⟨le_refl d₀, Nat.lt_succ_self d₀⟩)).le
  have := Fin.mk.inj hij
  omega

/-- Membership in `A ++ [x] ++ B` (generic, so that no substitution happens in big contexts). -/
theorem forall_mem_append_singleton_append {α : Type*} {A B : List α} {x : α} {P : α → Prop}
    (hA : ∀ a ∈ A, P a) (hx : P x) (hB : ∀ b ∈ B, P b) : ∀ o ∈ A ++ [x] ++ B, P o := by
  intro o ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · exact hA o ho
    · rw [List.mem_singleton.1 ho]
      exact hx
  · exact hB o ho

/-- A list of class primitives is well formed if its steps are. -/
theorem forall_mem_map_prim {L : Layout} {β : Type} {Child : Type} {cwf : Child → Prop} {B : ℕ}
    {l : List (Step L β)} (h : ∀ s ∈ l, Step.WF B s) :
    ∀ o ∈ l.map (Model.Op.prim (Child := Child)), Op.WF cwf B o := by
  intro o ho
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
  exact h s hs

/-- `ProcK.WF` at depth `d + 1`, unfolded. -/
theorem procWF_succ {L : Layout} {β : Type} {B d : ℕ} {p : List (Model.Op L β (ProcK L β d))}
    (h : ∀ o ∈ p, Op.WF (ProcK.WF B d) B o) : ProcK.WF B (d + 1) p :=
  h

/-- `Op.WF` of a node, unfolded. -/
theorem opWF_node {L : Layout} {β : Type} {Child : Type} {cwf : Child → Prop} {B W : ℕ} {hW : 0 < W}
    {ops : List (RoleOp L β W Child)} (h : ∀ o ∈ ops, RoleOp.WF cwf B o) :
    Op.WF cwf B (Model.Op.node W hW ops) :=
  h

/-- The induction: `interchangeProc q fac k h₀ d₀` is well formed under `WFHyps`. -/
theorem wf_main {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k : ℕ) :
    ∀ h₀ d₀ : ℕ, WFHyps L q fac k h₀ d₀ →
      ProcK.WF q k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) := by
  induction k with
  | zero => exact fun h₀ d₀ H => wf_zero q fac H
  | succ k ih =>
    intro h₀ d₀ H
    obtain ⟨hq, hval, hrad, hhd, hdn⟩ := H
    rw [pow_succ'] at hrad hhd hdn
    have hrH : ∀ l : Fin L.n, h₀ ≤ l.val → l.val < h₀ + mH * mH ^ k → L.r l = q :=
      fun l h1 h2 => hrad l (Or.inl ⟨h1, h2⟩)
    have hrD : ∀ l : Fin L.n, d₀ ≤ l.val → l.val < d₀ + mH * mH ^ k → L.r l = q :=
      fun l h1 h2 => hrad l (Or.inr ⟨h1, h2⟩)
    have hch : ∀ i j : Fin mH, ProcK.WF q k (interchangeProc (L := L) (β := β) q fac k
        (h₀ + i.val * mH ^ k) (d₀ + j.val * mH ^ k)) := by
      intro i j
      have hi := fin_mul_add_le i (mH ^ k)
      have hj := fin_mul_add_le j (mH ^ k)
      refine ih _ _ ⟨hq, hval, fun l hl => ?_, by omega, by omega⟩
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hrH l (by omega) (by omega)
      · exact hrD l (by omega) (by omega)
    rw [interchangeProc_succ (L := L) (β := β) q fac k h₀ d₀]
    exact procWF_succ (forall_mem_append_singleton_append
      (forall_mem_map_prim (wf_subHSteps hhd hdn _))
      (opWF_node (wf_bitNodeOps (fun w v => wf_edgeOpsB hq hhd hdn hrH hrD hval hch w v)))
      (forall_mem_map_prim (wf_hMinusDSteps hq hhd hdn hrD)))

end InterchangeWFAux

/-- **Proposition A.7 (`prop:transfer11`) well-formedness** (`InterchangeProcWFStmt`, `AppCProc.lean`): under `InterchangeHyps`,
every primitive of `interchangeProc q fac k h₀ d₀` satisfies its side condition at the radix bound
`q` (two distinct radix-`q` fields per digit interchange; shift offsets reading only earlier fields;
invertible units; gates reading and changing only their touched roles; well-formed children). -/
theorem interchangeProcWF_holds : InterchangeProcWFStmt := by
  intro L β _ _ q fac k h₀ d₀ c H
  obtain ⟨hq, -, -, hval, hrad, hhd, hdn, -, -⟩ := H
  exact InterchangeWFAux.wf_main q fac k h₀ d₀ ⟨hq, hval, hrad, hhd, hdn⟩

end SubNLogN.Math.Networks
