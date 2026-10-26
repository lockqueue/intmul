import SubNLogN.Math.Networks.Proofs.InterchangeCorrectCoords

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part B2: the primitive steps of `interchangeProc` in chunk coordinates

Every primitive step used by `interchangeProc` is a class-restricted pull (`cpull`) that changes the
coordinates of one chunk by an explicit formula:
* `subHSteps`: pull `D ← D + H` (the step itself is `D ← D − H`);
* `hMinusDSteps`: pull `D ← H − D`;
* `lowerSteps E`: pull `X ← (E⁻¹ mod q^b) X` (the steps realize `X ← E X`);
* `swapBlocks` of two coordinate blocks / of two whole chunks: exchange of coordinates.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-! ### Helpers (A2): casts, chunk facts, composition of class-restricted pulls

Proof notes. Each step list is folded with `stp_foldl_flatMap`: if every per-index sublist acts as a
class-restricted pull `p i` preserving the row class, the whole list acts as the pull
`p i₁ ∘ ⋯ ∘ p iₙ`. For `subHSteps` / `hMinusDSteps` the per-index pulls change distinct coordinates
of `D` and read `H` (unchanged), so the composite is computed by `stp_foldr_coordwise`. For
`lowerSteps` the composite pull is forward substitution (`stp_foldr_lower`): coordinate `i`
becomes `u_i (X_i − Σ_{j<i} e_ij Y_j)`, which equals `Y_i` for `Y = (E' mod q^b) X`
(`stp_lower_key`, from `(E mod q^b)(E' mod q^b) = 1` and `u_i e_ii = 1`). -/

private theorem stp_mH_pos : 0 < mH := by norm_num [mH]

/-- An address exists only if the radix `q` of the chunk is positive. -/
private theorem stp_q_pos {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) : 0 < q := by
  have hb := hC.hb
  have hmb : 0 < mH * b := Nat.mul_pos stp_mH_pos hb
  have ht : t₀ < L.n := by have := hC.fits; omega
  have hr := hC.radix ⟨t₀, ht⟩ le_rfl (by show t₀ < t₀ + mH * b; omega)
  have hpos := (x ⟨t₀, ht⟩).pos
  rwa [hr] at hpos

private theorem stp_cast_shift {R a c : ℕ} (hR : 0 < R) :
    (((a + R - c % R) % R : ℕ) : ZMod R) = (a : ZMod R) - (c : ZMod R) := by
  have hc : c % R < R := Nat.mod_lt c hR
  rw [ZMod.natCast_mod, Nat.cast_sub (show c % R ≤ a + R by omega), Nat.cast_add,
    ZMod.natCast_self, ZMod.natCast_mod, add_zero]

private theorem stp_cast_unit {R a u : ℕ} :
    (((u * a) % R : ℕ) : ZMod R) = (u : ZMod R) * (a : ZMod R) := by
  rw [ZMod.natCast_mod, Nat.cast_mul]

private theorem stp_cast_neg {R a : ℕ} (hR : 0 < R) :
    ((R - a % R : ℕ) : ZMod R) = -(a : ZMod R) := by
  rw [Nat.cast_sub (Nat.mod_lt a hR).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

private theorem stp_cast_pred {R : ℕ} (hR : 0 < R) : ((R - 1 : ℕ) : ZMod R) = -1 := by
  rw [Nat.cast_sub (show 1 ≤ R by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]

private theorem stp_blk_le {t₀ b : ℕ} (i : Fin mH) : t₀ ≤ (blk t₀ b i).1 :=
  Nat.le_add_right _ _

private theorem stp_blk_fst_le_snd {t₀ b : ℕ} (i : Fin mH) : (blk t₀ b i).1 ≤ (blk t₀ b i).2 :=
  Nat.add_le_add_left (Nat.mul_le_mul_right b (Nat.le_add_right i.val 1)) t₀

private theorem stp_blk_snd_le {t₀ b : ℕ} (i : Fin mH) : (blk t₀ b i).2 ≤ t₀ + mH * b :=
  Nat.add_le_add_left (Nat.mul_le_mul_right b (show i.val + 1 ≤ mH from i.isLt)) t₀

/-- The composite of class-preserving pulls preserves the class. -/
private theorem stp_foldr_mem (c : RowClass L) {ι : Type*} (p : ι → L.Addr → L.Addr)
    (hp : ∀ i x, c.mem x → c.mem (p i x)) :
    ∀ (l : List ι) x, c.mem x → c.mem (l.foldr (fun i g => p i ∘ g) id x) := by
  intro l
  induction l with
  | nil => intro x hx; exact hx
  | cons i l ih => intro x hx; exact hp i _ (ih x hx)

/-- Folding per-index step lists, each acting as a class-preserving pull, gives the composite
pull (head of the list outermost). -/
private theorem stp_foldl_flatMap {β : Type} (c : RowClass L) {ι : Type*}
    (steps : ι → List (Step L β)) (p : ι → L.Addr → L.Addr) (hp : ∀ i x, c.mem x → c.mem (p i x))
    (hsteps : ∀ i (A : L.Addr → β),
      (steps i).foldl (fun A s => s.runIn c A) A = cpull c.mem (p i) A) :
    ∀ (l : List ι) (A : L.Addr → β), (l.flatMap steps).foldl (fun A s => s.runIn c A) A =
      cpull c.mem (l.foldr (fun i g => p i ∘ g) id) A := by
  intro l
  induction l with
  | nil => intro A; simp [cpull_id]
  | cons i l ih =>
    intro A
    rw [List.flatMap_cons, List.foldl_append, hsteps, ih, cpull_cpull]
    · rfl
    · exact stp_foldr_mem c p hp l

/-- Composite of pulls acting on distinct coordinates of one chunk. -/
private theorem stp_foldr_coordwise {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b)
    (p : Fin mH → L.Addr → L.Addr) (f : Fin mH → ZMod (q ^ b) → L.Addr → ZMod (q ^ b))
    (hp : ∀ i x Z, p i (setCoords L (q ^ b) t₀ b x Z) =
      setCoords L (q ^ b) t₀ b x (Function.update Z i (f i (Z i) x))) :
    ∀ (l : List (Fin mH)), l.Nodup → ∀ x,
      l.foldr (fun i g => p i ∘ g) id x = setCoords L (q ^ b) t₀ b x
        (fun i => if i ∈ l then f i (coords L (q ^ b) t₀ b x i) x
          else coords L (q ^ b) t₀ b x i) := by
  intro l
  induction l with
  | nil =>
    intro _ x
    simpa using (setCoords_coords hC x).symm
  | cons i l ih =>
    intro hnd x
    rw [List.nodup_cons] at hnd
    show p i (l.foldr (fun i g => p i ∘ g) id x) = _
    rw [ih hnd.2 x, hp]
    refine congrArg (setCoords L (q ^ b) t₀ b x) (funext fun i' => ?_)
    by_cases hi : i' = i
    · subst hi
      simp [hnd.1]
    · simp [hi]

/-! ### Forward substitution (for `lowerSteps`) -/

/-- Partial solution: coordinates `j < k` from `Y`, the others from `X`. -/
def stp_part {Q : ℕ} (k : ℕ) (Y X : Fin mH → ZMod Q) (j : Fin mH) : ZMod Q :=
  if j.val < k then Y j else X j

private theorem stp_part_of_lt {Q k : ℕ} (Y X : Fin mH → ZMod Q) {j : Fin mH} (h : j.val < k) :
    stp_part k Y X j = Y j := if_pos h

private theorem stp_part_of_ge {Q k : ℕ} (Y X : Fin mH → ZMod Q) {j : Fin mH} (h : k ≤ j.val) :
    stp_part k Y X j = X j := if_neg (by omega)

private theorem stp_map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

private theorem stp_range_succ_reverse (k : ℕ) :
    (List.range (k + 1)).reverse = k :: (List.range k).reverse := by
  rw [List.range_succ, List.reverse_append]
  rfl

/-- Composite of the forward-substitution pulls along `[k-1, …, 0]`. -/
private theorem stp_foldr_lower {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (p : Fin mH → L.Addr → L.Addr)
    (e : Matrix (Fin mH) (Fin mH) (ZMod (q ^ b))) (u : Fin mH → ZMod (q ^ b))
    (hp : ∀ i z, p i z = setCoords L (q ^ b) t₀ b z (Function.update (coords L (q ^ b) t₀ b z) i
      (u i * (coords L (q ^ b) t₀ b z i -
        ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i), e i j * coords L (q ^ b) t₀ b z j))))
    (x : L.Addr) (Y : Fin mH → ZMod (q ^ b))
    (hY : ∀ i, u i * (coords L (q ^ b) t₀ b x i -
      ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i), e i j * Y j) = Y i) :
    ∀ (l : List (Fin mH)) (k : ℕ), l.map Fin.val = (List.range k).reverse →
      l.foldr (fun i g => p i ∘ g) id x =
        setCoords L (q ^ b) t₀ b x (stp_part k Y (coords L (q ^ b) t₀ b x)) := by
  intro l
  induction l with
  | nil =>
    intro k hk
    cases k with
    | zero =>
      have h0 : stp_part 0 Y (coords L (q ^ b) t₀ b x) = coords L (q ^ b) t₀ b x := by
        funext j
        exact stp_part_of_ge Y _ (Nat.zero_le _)
      show x = _
      rw [h0, setCoords_coords hC]
    | succ k =>
      rw [stp_range_succ_reverse] at hk
      exact absurd hk.symm (List.cons_ne_nil _ _)
  | cons i l ih =>
    intro k hk
    cases k with
    | zero => exact absurd hk (List.cons_ne_nil _ _)
    | succ k =>
      rw [stp_range_succ_reverse, List.map_cons, List.cons.injEq] at hk
      obtain ⟨hik, hl⟩ := hk
      show p i (l.foldr (fun i g => p i ∘ g) id x) = _
      rw [ih k hl, hp, coords_setCoords hC, setCoords_setCoords, stp_part_of_ge Y _ hik.ge]
      have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
          e i j * stp_part k Y (coords L (q ^ b) t₀ b x) j =
          ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i), e i j * Y j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.mem_filter, Fin.lt_def] at hj
        rw [stp_part_of_lt Y _ (show j.val < k by omega)]
      rw [hsum, hY]
      refine congrArg (setCoords L (q ^ b) t₀ b x) (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, stp_part_of_lt Y _ (show j.val < k + 1 by omega)]
      · rw [Function.update_of_ne hj]
        have hjk : j.val ≠ k := fun h => hj (Fin.ext (h.trans hik.symm))
        by_cases hlt : j.val < k
        · rw [stp_part_of_lt Y _ hlt, stp_part_of_lt Y _ (show j.val < k + 1 by omega)]
        · rw [stp_part_of_ge Y _ (show k ≤ j.val by omega),
            stp_part_of_ge Y _ (show k + 1 ≤ j.val by omega)]

/-- Forward substitution solves `e Y = X` for lower-triangular `e` with `u_i e_ii = 1`. -/
private theorem stp_lower_key {R : ℕ} (e e' : Matrix (Fin mH) (Fin mH) (ZMod R))
    (u : Fin mH → ZMod R) (hlow : ∀ i j, i < j → e i j = 0) (hee : e * e' = 1)
    (hu : ∀ i, u i * e i i = 1) (X : Fin mH → ZMod R) (i : Fin mH) :
    u i * (X i - ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i), e i j * (e'.mulVec X) j) =
      (e'.mulVec X) i := by
  set Y := e'.mulVec X with hYdef
  have hEY : e.mulVec Y = X := by rw [hYdef, Matrix.mulVec_mulVec, hee, Matrix.one_mulVec]
  have h1 : X i = ∑ j, e i j * Y j := by
    calc X i = e.mulVec Y i := by rw [hEY]
      _ = ∑ j, e i j * Y j := rfl
  have hrow : X i = ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i), e i j * Y j +
      e i i * Y i := by
    have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin mH => ¬ j < i), e i j * Y j = e i i * Y i := by
      rw [Finset.sum_eq_single i]
      · intro j hj hji
        rw [Finset.mem_filter, not_lt] at hj
        rw [hlow i j (lt_of_le_of_ne hj.2 (Ne.symm hji)), zero_mul]
      · intro hi
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_irrefl i⟩) hi
    rw [h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin mH => j < i), h2]
  rw [hrow, add_sub_cancel_left, ← mul_assoc, hu, one_mul]

/-! ### Reduction modulo `q^b` of `q`-integral rationals (as in `AppCShearProofs`) -/

private theorem stp_qInt_add {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x + y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.add_den_dvd x y))).elim hx hy

private theorem stp_qInt_mul {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x * y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.mul_den_dvd x y))).elim hx hy

private theorem stp_qInt_zero {q : ℕ} (hq : q.Prime) : QIntegral q 0 := by
  intro h
  have h1 : (0 : ℚ).den = 1 := by simp
  rw [h1, Nat.dvd_one] at h
  exact hq.ne_one h

private theorem stp_qInt_inv {q : ℕ} (hq : q.Prime) {r : ℚ} (hn : ¬ (q : ℤ) ∣ r.num) :
    QIntegral q r⁻¹ := by
  intro h
  rw [Rat.den_inv] at h
  split_ifs at h with h0
  · exact hq.ne_one (Nat.dvd_one.mp h)
  · exact hn (Int.ofNat_dvd_left.mpr h)

private theorem stp_den_mul_inv {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r) :
    (r.den : ZMod (q ^ b)) * (r.den : ZMod (q ^ b))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _
    (Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hq).mpr hr).symm)

private theorem stp_ratMod_eq_of_mul {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r)
    (n d : ℤ) (h : r * d = n) (iv : ZMod (q ^ b)) (hiv : (d : ZMod (q ^ b)) * iv = 1) :
    ratMod (q ^ b) r = n * iv := by
  have hden := stp_den_mul_inv b hq hr
  have key : (r.num : ℚ) * d = n * r.den := by
    rw [← Rat.mul_den_eq_num r, ← h]
    ring
  have keyZ : r.num * d = n * (r.den : ℤ) := by exact_mod_cast key
  have keyM : (r.num : ZMod (q ^ b)) * (d : ZMod (q ^ b)) =
      (n : ZMod (q ^ b)) * (r.den : ZMod (q ^ b)) := by
    have := congrArg (Int.cast : ℤ → ZMod (q ^ b)) keyZ
    push_cast at this
    exact this
  unfold ratMod
  linear_combination (-((r.num : ZMod (q ^ b)) * (r.den : ZMod (q ^ b))⁻¹)) * hiv +
    (iv * (r.den : ZMod (q ^ b))⁻¹) * keyM + (iv * (n : ZMod (q ^ b))) * hden

private theorem stp_ratMod_add {q : ℕ} (b : ℕ) (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : ratMod (q ^ b) (x + y) = ratMod (q ^ b) x + ratMod (q ^ b) y := by
  have hdx := stp_den_mul_inv b hq hx
  have hdy := stp_den_mul_inv b hq hy
  rw [stp_ratMod_eq_of_mul b hq (stp_qInt_add hq hx hy) (x.num * y.den + y.num * x.den)
    (x.den * y.den) ?_ ((x.den : ZMod (q ^ b))⁻¹ * (y.den : ZMod (q ^ b))⁻¹) ?_]
  · unfold ratMod
    push_cast
    linear_combination ((x.num : ZMod (q ^ b)) * (x.den : ZMod (q ^ b))⁻¹) * hdy +
      ((y.num : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx
  · push_cast
    rw [← Rat.mul_den_eq_num x, ← Rat.mul_den_eq_num y]
    ring
  · push_cast
    linear_combination ((y.den : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx + hdy

private theorem stp_ratMod_mul {q : ℕ} (b : ℕ) (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : ratMod (q ^ b) (x * y) = ratMod (q ^ b) x * ratMod (q ^ b) y := by
  have hdx := stp_den_mul_inv b hq hx
  have hdy := stp_den_mul_inv b hq hy
  rw [stp_ratMod_eq_of_mul b hq (stp_qInt_mul hq hx hy) (x.num * y.num) (x.den * y.den) ?_
    ((x.den : ZMod (q ^ b))⁻¹ * (y.den : ZMod (q ^ b))⁻¹) ?_]
  · unfold ratMod
    push_cast
    ring
  · push_cast
    rw [← Rat.mul_den_eq_num x, ← Rat.mul_den_eq_num y]
    ring
  · push_cast
    linear_combination ((y.den : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx + hdy

private theorem stp_ratMod_sum {q : ℕ} (b : ℕ) (hq : q.Prime) {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, QIntegral q (f i)) :
    ratMod (q ^ b) (∑ i ∈ s, f i) = ∑ i ∈ s, ratMod (q ^ b) (f i) ∧
      QIntegral q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp [ratMod]
    · rw [Finset.sum_empty]
      exact stp_qInt_zero hq
  | insert a s ha ih =>
    have hfa : QIntegral q (f a) := hf a (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨by rw [stp_ratMod_add b hq hfa ih2, ih1], stp_qInt_add hq hfa ih2⟩

private theorem stp_ratMod_zero (Q : ℕ) : ratMod Q 0 = 0 := by
  simp [ratMod]

private theorem stp_ratMod_one (Q : ℕ) : ratMod Q 1 = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := Q) 1 (Nat.coprime_one_left Q)
  simp only [Nat.cast_one, one_mul] at h
  simp [ratMod, h]

/-- `E E' = 1` survives reduction modulo `q^b` (all entries `q`-integral). -/
private theorem stp_map_mul_eq_one {q : ℕ} (b : ℕ) (hq : q.Prime) {n : ℕ}
    (E E' : Matrix (Fin n) (Fin n) ℚ) (hEE : E * E' = 1)
    (hint : ∀ i j, QIntegral q (E i j) ∧ QIntegral q (E' i j)) :
    E.map (ratMod (q ^ b)) * E'.map (ratMod (q ^ b)) = 1 := by
  ext i j
  have h1 : ((E * E').map (ratMod (q ^ b))) i j =
      (E.map (ratMod (q ^ b)) * E'.map (ratMod (q ^ b))) i j := by
    simp only [Matrix.map_apply, Matrix.mul_apply]
    rw [(stp_ratMod_sum b hq Finset.univ (fun k => E i k * E' k j)
      (fun k _ => stp_qInt_mul hq (hint i k).1 (hint k j).2)).1]
    exact Finset.sum_congr rfl fun k _ => stp_ratMod_mul b hq (hint i k).1 (hint k j).2
  rw [← h1, hEE, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact stp_ratMod_one _
  · exact stp_ratMod_zero _

/-- The reduced inverse of a diagonal entry with numerator prime to `q` inverts it. -/
private theorem stp_diag_inv {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r)
    (hn : ¬ (q : ℤ) ∣ r.num) : ratMod (q ^ b) r⁻¹ * ratMod (q ^ b) r = 1 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  rw [← stp_ratMod_mul b hq (stp_qInt_inv hq hn) hr, inv_mul_cancel₀ hr0, stp_ratMod_one]

/-! ### Whole chunks as mixed-radix numbers (for `swapBlocks_chunk_runIn`) -/

private theorem stp_blockRange_tail {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (i : Fin mH) :
    L.blockRange (blk t₀ b i).2 (t₀ + mH * b) = q ^ (mH * b - (i.val + 1) * b) := by
  rw [blockRange_eq_pow (stp_blk_snd_le i) hC.fits
    (fun j hj1 hj2 => hC.radix j (le_trans (stp_blk_le i) (le_trans (stp_blk_fst_le_snd i) hj1))
      hj2)]
  congr 1
  simp only [blk]
  omega

/-- Coordinate `i` is the `i`-th radix-`q^b` digit of the whole chunk value. -/
private theorem stp_coords_digits {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr)
    (i : Fin mH) :
    coords L (q ^ b) t₀ b x i = ((L.blockVal t₀ (t₀ + mH * b) x /
      q ^ (mH * b - (i.val + 1) * b) % q ^ b : ℕ) : ZMod (q ^ b)) := by
  unfold coords
  rw [blockVal_sub (stp_blk_le i) (stp_blk_fst_le_snd i) (stp_blk_snd_le i) x,
    stp_blockRange_tail hC i, blockRange_blk hC i]

/-- Overwriting the whole chunk with `V` sets its coordinates to the digits of `V`. -/
private theorem stp_blockSet_chunk {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) (V : ℕ)
    (X : Fin mH → ZMod (q ^ b))
    (hX : ∀ i, X i = ((V / q ^ (mH * b - (i.val + 1) * b) % q ^ b : ℕ) : ZMod (q ^ b))) :
    L.blockSet t₀ (t₀ + mH * b) x V = setCoords L (q ^ b) t₀ b x X := by
  apply eq_of_coords hC
  · intro j hj
    rw [blockSet_apply_of_not x V j hj, setCoords_of_not x X j hj]
  · rw [coords_setCoords hC]
    funext i
    unfold coords
    rw [blockVal_sub_blockSet (stp_blk_le i) (stp_blk_fst_le_snd i) (stp_blk_snd_le i) x V,
      stp_blockRange_tail hC i, blockRange_blk hC i, hX i]

/-! ### Elementary steps on coordinate blocks -/

theorem shift_pull {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (i : Fin mH) (off : L.Addr → ℕ)
    (x : L.Addr) :
    (Elem.shift (blk t₀ b i).1 (blk t₀ b i).2 off).pull x =
      setCoords L (q ^ b) t₀ b x (Function.update (coords L (q ^ b) t₀ b x) i
        (coords L (q ^ b) t₀ b x i - (off x : ZMod (q ^ b)))) := by
  have hR : 0 < q ^ b := pow_pos (stp_q_pos hC x) b
  show _ = setCoords L (q ^ b) t₀ b x (Function.update (coords L (q ^ b) t₀ b x) i
    ((L.blockVal (blk t₀ b i).1 (blk t₀ b i).2 x : ZMod (q ^ b)) - (off x : ZMod (q ^ b))))
  simp only [Elem.pull]
  rw [blockRange_blk hC i, blockSet_blk hC, stp_cast_shift hR]

theorem unit_pull {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (i : Fin mH) (u u' : ℕ) (x : L.Addr) :
    (Elem.unit (blk t₀ b i).1 (blk t₀ b i).2 u u').pull x =
      setCoords L (q ^ b) t₀ b x (Function.update (coords L (q ^ b) t₀ b x) i
        ((u' : ZMod (q ^ b)) * coords L (q ^ b) t₀ b x i)) := by
  show _ = setCoords L (q ^ b) t₀ b x (Function.update (coords L (q ^ b) t₀ b x) i
    ((u' : ZMod (q ^ b)) * (L.blockVal (blk t₀ b i).1 (blk t₀ b i).2 x : ZMod (q ^ b))))
  simp only [Elem.pull]
  rw [blockRange_blk hC i, blockSet_blk hC, stp_cast_unit]

/-! ### The step lists of `interchangeProc` -/

/-- `subHSteps` (`D ← D − H`) acts by the pull `D ← D + H`. -/
theorem run_subHSteps {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (c : RowClass L)
    (hc : c.row.val < h₀) {β : Type} (A : L.Addr → β) :
    (subHSteps (L := L) (β := β) (q ^ b) h₀ d₀ b).foldl (fun A s => s.runIn c A) A =
      cpull c.mem (fun x => setCoords L (q ^ b) d₀ b x
        (coords L (q ^ b) d₀ b x + coords L (q ^ b) h₀ b x)) A := by
  have hcD : c.row.val < d₀ := lt_of_lt_of_le hc (le_trans (Nat.le_add_right _ _) hT.HD)
  let p : Fin mH → L.Addr → L.Addr := fun i => (Elem.shift (L := L) (blk d₀ b i).1 (blk d₀ b i).2
      (fun x => q ^ b - L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x % q ^ b)).pull
  have hpx : ∀ i x, p i x = setCoords L (q ^ b) d₀ b x (Function.update (coords L (q ^ b) d₀ b x)
      i (coords L (q ^ b) d₀ b x i + coords L (q ^ b) h₀ b x i)) := by
    intro i x
    show _ = setCoords L (q ^ b) d₀ b x (Function.update (coords L (q ^ b) d₀ b x) i
      (coords L (q ^ b) d₀ b x i + (L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x : ZMod (q ^ b))))
    show (Elem.shift _ _ _).pull x = _
    rw [shift_pull hT.D, stp_cast_neg (pow_pos (stp_q_pos hT.D x) b), sub_neg_eq_add]
  have hmem : ∀ i x, c.mem x → c.mem (p i x) := fun i x hx => by
    rw [hpx]; exact (mem_setCoords c hcD _ _).2 hx
  rw [subHSteps, List.map_eq_flatMap]
  refine (stp_foldl_flatMap c _ p hmem ?_ _ A).trans ?_
  · intro i A
    rfl
  · apply cpull_congr
    intro x _
    rw [stp_foldr_coordwise hT.D p (fun i v y => v + coords L (q ^ b) h₀ b y i) ?_ _
      (List.nodup_finRange mH) x]
    · refine congrArg (setCoords L (q ^ b) d₀ b x) (funext fun i => ?_)
      simp only [List.mem_finRange, if_true, Pi.add_apply]
    · intro i y Z
      rw [hpx, coords_setCoords hT.D, coords_setCoords_D hT, setCoords_setCoords]

/-- `hMinusDSteps` (`D ← H − D`) acts by the pull `D ← H − D`. -/
theorem run_hMinusDSteps {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (c : RowClass L)
    (hc : c.row.val < h₀) {β : Type} (A : L.Addr → β) :
    (hMinusDSteps (L := L) (β := β) (q ^ b) h₀ d₀ b).foldl (fun A s => s.runIn c A) A =
      cpull c.mem (fun x => setCoords L (q ^ b) d₀ b x
        (coords L (q ^ b) h₀ b x - coords L (q ^ b) d₀ b x)) A := by
  have hcD : c.row.val < d₀ := lt_of_lt_of_le hc (le_trans (Nat.le_add_right _ _) hT.HD)
  let pu : Fin mH → L.Addr → L.Addr := fun i =>
    (Elem.unit (L := L) (blk d₀ b i).1 (blk d₀ b i).2 (q ^ b - 1) (q ^ b - 1)).pull
  let ps : Fin mH → L.Addr → L.Addr := fun i => (Elem.shift (L := L) (blk d₀ b i).1
    (blk d₀ b i).2 (fun x => L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x)).pull
  have hpu : ∀ i x, pu i x = setCoords L (q ^ b) d₀ b x (Function.update (coords L (q ^ b) d₀ b x)
      i (-coords L (q ^ b) d₀ b x i)) := by
    intro i x
    show (Elem.unit _ _ _ _).pull x = _
    rw [unit_pull hT.D, stp_cast_pred (pow_pos (stp_q_pos hT.D x) b), neg_one_mul]
  have hps : ∀ i x, ps i x = setCoords L (q ^ b) d₀ b x (Function.update (coords L (q ^ b) d₀ b x)
      i (coords L (q ^ b) d₀ b x i - coords L (q ^ b) h₀ b x i)) := by
    intro i x
    show (Elem.shift _ _ _).pull x = _
    rw [shift_pull hT.D]
    rfl
  have hmu : ∀ i x, c.mem x → c.mem (pu i x) := fun i x hx => by
    rw [hpu]; exact (mem_setCoords c hcD _ _).2 hx
  have hms : ∀ i x, c.mem x → c.mem (ps i x) := fun i x hx => by
    rw [hps]; exact (mem_setCoords c hcD _ _).2 hx
  have hp : ∀ i y Z, pu i (ps i (setCoords L (q ^ b) d₀ b y Z)) = setCoords L (q ^ b) d₀ b y
      (Function.update Z i (coords L (q ^ b) h₀ b y i - Z i)) := by
    intro i y Z
    rw [hps, coords_setCoords hT.D, coords_setCoords_D hT, setCoords_setCoords, hpu,
      coords_setCoords hT.D, setCoords_setCoords, Function.update_idem, Function.update_self,
      neg_sub]
  rw [hMinusDSteps]
  refine (stp_foldl_flatMap c _ (fun i => pu i ∘ ps i) (fun i x hx => hmu i _ (hms i x hx)) ?_
    _ A).trans ?_
  · intro i A
    exact cpull_cpull c.mem (pu i) (ps i) (hms i) A
  · apply cpull_congr
    intro x _
    rw [stp_foldr_coordwise hT.D (fun i => pu i ∘ ps i)
      (fun i v y => coords L (q ^ b) h₀ b y i - v) (fun i y Z => hp i y Z) _
      (List.nodup_finRange mH) x]
    refine congrArg (setCoords L (q ^ b) d₀ b x) (funext fun i => ?_)
    simp only [List.mem_finRange, if_true, Pi.sub_apply]

/-- `lowerSteps E` on the chunk at `t₀` (realizing `X ← E X`) acts by the pull `X ← (E⁻¹ mod q^b) X`
(`E` lower triangular, `E E' = 1`, all entries `q`-integral, diagonal numerators prime to `q`). -/
theorem run_lowerSteps {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (hq : q.Prime) (c : RowClass L)
    (hc : c.row.val < t₀) (E E' : Matrix (Fin mH) (Fin mH) ℚ) (hE : IsLowerTri E)
    (hEE : E * E' = 1) (hint : ∀ i j, QIntegral q (E i j) ∧ QIntegral q (E' i j))
    (hdiag : ∀ i, ¬ (q : ℤ) ∣ (E i i).num) {β : Type} (A : L.Addr → β) :
    (lowerSteps (L := L) (β := β) (q ^ b) t₀ b E).foldl (fun A s => s.runIn c A) A =
      cpull c.mem (fun x => setCoords L (q ^ b) t₀ b x
        ((E'.map (ratMod (q ^ b))).mulVec (coords L (q ^ b) t₀ b x))) A := by
  have : NeZero (q ^ b) := ⟨pow_ne_zero b hq.ne_zero⟩
  have hcast : ∀ r : ℚ, ((ratModNat (q ^ b) r : ℕ) : ZMod (q ^ b)) = ratMod (q ^ b) r :=
    fun r => ZMod.natCast_zmod_val _
  let pu : Fin mH → L.Addr → L.Addr := fun i => (Elem.unit (L := L) (blk t₀ b i).1 (blk t₀ b i).2
      (ratModNat (q ^ b) (E i i)) (ratModNat (q ^ b) (E i i)⁻¹)).pull
  let ps : Fin mH → L.Addr → L.Addr := fun i => (Elem.shift (L := L) (blk t₀ b i).1
      (blk t₀ b i).2 (fun x => ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
        ratModNat (q ^ b) (E i j) * L.blockVal (blk t₀ b j).1 (blk t₀ b j).2 x)).pull
  have hpu : ∀ i z, pu i z = setCoords L (q ^ b) t₀ b z (Function.update
      (coords L (q ^ b) t₀ b z) i (ratMod (q ^ b) (E i i)⁻¹ * coords L (q ^ b) t₀ b z i)) := by
    intro i z
    show (Elem.unit _ _ _ _).pull z = _
    rw [unit_pull hC, hcast]
  have hps : ∀ i z, ps i z = setCoords L (q ^ b) t₀ b z (Function.update
      (coords L (q ^ b) t₀ b z) i (coords L (q ^ b) t₀ b z i -
        ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
          ratMod (q ^ b) (E i j) * coords L (q ^ b) t₀ b z j)) := by
    intro i z
    have hsum : ((∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
        ratModNat (q ^ b) (E i j) * L.blockVal (blk t₀ b j).1 (blk t₀ b j).2 z : ℕ) :
          ZMod (q ^ b)) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
          ratMod (q ^ b) (E i j) * coords L (q ^ b) t₀ b z j := by
      push_cast
      simp only [hcast]
      rfl
    show (Elem.shift _ _ _).pull z = _
    rw [shift_pull hC, hsum]
  have hmu : ∀ i x, c.mem x → c.mem (pu i x) := fun i x hx => by
    rw [hpu]; exact (mem_setCoords c hc _ _).2 hx
  have hms : ∀ i x, c.mem x → c.mem (ps i x) := fun i x hx => by
    rw [hps]; exact (mem_setCoords c hc _ _).2 hx
  have hp : ∀ i z, pu i (ps i z) = setCoords L (q ^ b) t₀ b z (Function.update
      (coords L (q ^ b) t₀ b z) i (ratMod (q ^ b) (E i i)⁻¹ * (coords L (q ^ b) t₀ b z i -
        ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
          ratMod (q ^ b) (E i j) * coords L (q ^ b) t₀ b z j))) := by
    intro i z
    rw [hps, hpu, coords_setCoords hC, setCoords_setCoords, Function.update_idem,
      Function.update_self]
  rw [lowerSteps]
  refine (stp_foldl_flatMap c _ (fun i => pu i ∘ ps i) (fun i x hx => hmu i _ (hms i x hx)) ?_
    _ A).trans ?_
  · intro i A
    exact cpull_cpull c.mem (pu i) (ps i) (hms i) A
  · apply cpull_congr
    intro x _
    have hlow : ∀ i j : Fin mH, i < j → (E.map (ratMod (q ^ b))) i j = 0 := by
      intro i j hij
      rw [Matrix.map_apply, hE i j hij, stp_ratMod_zero]
    have hee := stp_map_mul_eq_one b hq E E' hEE hint
    have hu : ∀ i, ratMod (q ^ b) (E i i)⁻¹ * (E.map (ratMod (q ^ b))) i i = 1 := fun i =>
      stp_diag_inv b hq (hint i i).1 (hdiag i)
    have hY := stp_lower_key (E.map (ratMod (q ^ b))) (E'.map (ratMod (q ^ b)))
      (fun i => ratMod (q ^ b) (E i i)⁻¹) hlow hee hu (coords L (q ^ b) t₀ b x)
    rw [stp_foldr_lower hC (fun i => pu i ∘ ps i) (E.map (ratMod (q ^ b)))
      (fun i => ratMod (q ^ b) (E i i)⁻¹) (fun i z => hp i z) x _ hY ((List.finRange mH).reverse)
      mH (by rw [List.map_reverse, stp_map_val_finRange])]
    exact congrArg (setCoords L (q ^ b) t₀ b x) (funext fun j => stp_part_of_lt _ _ j.isLt)

/-- `swapBlocks` of coordinate block `i` of `H` and coordinate block `j` of `D` exchanges them. -/
theorem swapBlocks_blk_runIn {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (c : RowClass L)
    (i j : Fin mH) {β : Type} (A : L.Addr → β) :
    (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn c A =
      cpull c.mem (fun x => setCoords L (q ^ b) d₀ b
        (setCoords L (q ^ b) h₀ b x (Function.update (coords L (q ^ b) h₀ b x) i (coords L (q ^ b) d₀ b x j)))
        (Function.update (coords L (q ^ b) d₀ b x) j (coords L (q ^ b) h₀ b x i))) A := by
  have e1 : h₀ + i.val * b + b = (blk h₀ b i).2 := by simp only [blk]; ring
  have e2 : d₀ + j.val * b + b = (blk d₀ b j).2 := by simp only [blk]; ring
  funext x
  simp only [Step.runIn, Step.run, cpull]
  split_ifs with hx
  · refine congrArg A ?_
    rw [e1, e2]
    show L.blockSet (blk d₀ b j).1 (blk d₀ b j).2 (L.blockSet (blk h₀ b i).1 (blk h₀ b i).2 x
      (L.blockVal (blk d₀ b j).1 (blk d₀ b j).2 x)) (L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x) =
      setCoords L (q ^ b) d₀ b (setCoords L (q ^ b) h₀ b x (Function.update
        (coords L (q ^ b) h₀ b x) i (L.blockVal (blk d₀ b j).1 (blk d₀ b j).2 x : ZMod (q ^ b))))
        (Function.update (coords L (q ^ b) d₀ b x) j
          (L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x : ZMod (q ^ b)))
    rw [blockSet_blk hT.H, blockSet_blk hT.D, coords_setCoords_H hT]
  · rfl

/-- `swapBlocks` of the two whole chunks exchanges all coordinates. -/
theorem swapBlocks_chunk_runIn {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (c : RowClass L)
    {β : Type} (A : L.Addr → β) :
    (Step.swapBlocks h₀ d₀ (mH * b) : Step L β).runIn c A =
      cpull c.mem (fun x => setCoords L (q ^ b) d₀ b
        (setCoords L (q ^ b) h₀ b x (coords L (q ^ b) d₀ b x)) (coords L (q ^ b) h₀ b x)) A := by
  funext x
  simp only [Step.runIn, Step.run, cpull]
  split_ifs with hx
  · refine congrArg A ?_
    rw [stp_blockSet_chunk hT.H x _ (coords L (q ^ b) d₀ b x) (fun i => stp_coords_digits hT.D x i),
      stp_blockSet_chunk hT.D _ _ (coords L (q ^ b) h₀ b x) (fun i => stp_coords_digits hT.H x i)]
  · rfl

end InterchangeCorrect

end SubNLogN.Math.Networks
