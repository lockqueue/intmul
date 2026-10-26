import Contracts.W6
import Contracts.W9.Common
import WP.W9fW.Builders

/-!
# WP.W9fF.ColPure — pure value/width facts for the forward column core (S1)

* `zpE`, `zhE`: the entries of W6's reciprocal builders `W8.zPartFwdBarrett` / `W8.zHomFwdBarrett`
  as plain recurrences (`read1D_zPartFwdBarrett`, `read1D_zHomFwdBarrett`; prefix stability of
  `Array.push`).
* `z0E`, `outE`: the class-B boundary value and the combined outputs;
  `solveFwdBarrett_toList` gives the solver as a list, and `outE_zero` says output 0 is `Z0`.
* widths: `z0E_entryW` (from the output-width hypothesis), `zpE_entryW`, `zhE_entryW`
  (W9fW's builder widths).
* block/entry symbol facts and `bitLen` facts used by the machine programs.
-/

namespace WP.W9fF

open IntMul IntMulTM.Contracts TMFw TMFw.Contracts TMFw.Contracts.W9

/-! ## The builders as recurrences -/

def zpE (q H : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | k + 1 => W8.recStepBarrett q H μ a c (read1D Y (k + 1)) (zpE q H μ a c Y k)

def zhE (q H : ℕ) (μ a c : ℤ) : ℕ → ℤ × ℤ
  | 0 => (((2 ^ (q + 2) : ℕ) : ℤ), 0)
  | k + 1 => W8.recStepBarrett q H μ a c (0, 0) (zhE q H μ a c k)

theorem size_zPartFwdBarrett (q H : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    ∀ n, (W8.zPartFwdBarrett q H μ a c Y n).size = n + 1
  | 0 => rfl
  | n + 1 => by
    simp only [W8.zPartFwdBarrett, Array.size_push, size_zPartFwdBarrett q H μ a c Y n]

theorem size_zHomFwdBarrett (q H : ℕ) (μ a c : ℤ) :
    ∀ n, (W8.zHomFwdBarrett q H μ a c n).size = n + 1
  | 0 => rfl
  | n + 1 => by
    simp only [W8.zHomFwdBarrett, Array.size_push, size_zHomFwdBarrett q H μ a c n]

theorem read1D_zPartFwdBarrett (q H : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    ∀ n u, u ≤ n → read1D (W8.zPartFwdBarrett q H μ a c Y n) u = zpE q H μ a c Y u
  | 0, u, hu => by
    have hu0 : u = 0 := by omega
    subst hu0
    rfl
  | n + 1, u, hu => by
    have hs := size_zPartFwdBarrett q H μ a c Y n
    simp only [W8.zPartFwdBarrett]
    rw [read1D_push _ _ u (by omega), hs]
    split_ifs with h
    · exact read1D_zPartFwdBarrett q H μ a c Y n u (by omega)
    · have hu' : u = n + 1 := by omega
      subst hu'
      show _ = W8.recStepBarrett q H μ a c (read1D Y (n + 1)) (zpE q H μ a c Y n)
      rw [read1D_zPartFwdBarrett q H μ a c Y n n le_rfl]

theorem read1D_zHomFwdBarrett (q H : ℕ) (μ a c : ℤ) :
    ∀ n u, u ≤ n → read1D (W8.zHomFwdBarrett q H μ a c n) u = zhE q H μ a c u
  | 0, u, hu => by
    have hu0 : u = 0 := by omega
    subst hu0
    rfl
  | n + 1, u, hu => by
    have hs := size_zHomFwdBarrett q H μ a c n
    simp only [W8.zHomFwdBarrett]
    rw [read1D_push _ _ u (by omega), hs]
    split_ifs with h
    · exact read1D_zHomFwdBarrett q H μ a c n u (by omega)
    · have hu' : u = n + 1 := by omega
      subst hu'
      show _ = W8.recStepBarrett q H μ a c (0, 0) (zhE q H μ a c n)
      rw [read1D_zHomFwdBarrett q H μ a c n n le_rfl]

/-! ## Boundary value and outputs -/

def z0E (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) : ℤ × ℤ :=
  gRatioQuantize q (read1D Y 0) (c, 0) (zpE q H μ a c Y (t1 - 1)) (a, 0) (c, 0) (zhE q H μ a c (t1 - 1))

def outE (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) (u : ℕ) : ℤ × ℤ :=
  gCombineQuantize q (zpE q H μ a c Y u) (z0E q H t1 μ a c Y) (zhE q H μ a c u)

/-- The scan's output tape as a list. -/
theorem toList_runSequentialScanSteps {α : Type} (f : ℕ → α) :
    ∀ n, (runSequentialScanSteps f n).outTape.toList = (List.range n).map f
  | 0 => by simp [runSequentialScanSteps]
  | n + 1 => by
    simp only [runSequentialScanSteps, scanHeadStep, Array.toList_push,
      runSequentialScanSteps_inHead, toList_runSequentialScanSteps f n, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]

theorem solveFwdBarrett_toList (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    (W8.solveFwdBarrett q H t1 μ a c Y).toList = (List.range t1).map (outE q H t1 μ a c Y) := by
  simp only [W8.solveFwdBarrett]
  rw [toList_runSequentialScanSteps]
  apply List.map_congr_left
  intro u hu
  have hu' : u < t1 := List.mem_range.mp hu
  simp only [outE, z0E]
  rw [read1D_zPartFwdBarrett q H μ a c Y (t1 - 1) u (by omega),
    read1D_zHomFwdBarrett q H μ a c (t1 - 1) u (by omega),
    read1D_zPartFwdBarrett q H μ a c Y (t1 - 1) (t1 - 1) le_rfl,
    read1D_zHomFwdBarrett q H μ a c (t1 - 1) (t1 - 1) le_rfl]

/-- `divRoundPow2 (x·2^s) s = x` for `s ≥ 1`. -/
theorem divRoundPow2_mul_pow (x : ℤ) (s : ℕ) (hs : 1 ≤ s) :
    divRoundPow2 (x * ((2 ^ s : ℕ) : ℤ)) s = x := by
  unfold divRoundPow2
  rw [if_neg (by omega)]
  have hpos : (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) := by positivity
  have hlt : ((2 ^ (s - 1) : ℕ) : ℤ) < ((2 ^ s : ℕ) : ℤ) := by
    exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [add_comm, Int.add_mul_ediv_right _ _ hpos.ne',
    Int.ediv_eq_zero_of_lt (by positivity) hlt, zero_add]

/-- Combining with `zPart = 0` and `zHom = 2^(q+2)` returns the boundary value. -/
theorem gCombineQuantize_zero_unit (q : ℕ) (b : ℤ × ℤ) :
    gCombineQuantize q (0, 0) b (((2 ^ (q + 2) : ℕ) : ℤ), 0) = b := by
  rw [W8_gCombineQuantize_shift_holds]
  obtain ⟨b1, b2⟩ := b
  simp only [zero_mul, mul_zero, sub_zero, zero_add]
  rw [divRoundPow2_mul_pow _ _ (by omega), divRoundPow2_mul_pow _ _ (by omega)]

theorem outE_zero (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    outE q H t1 μ a c Y 0 = z0E q H t1 μ a c Y :=
  gCombineQuantize_zero_unit q (z0E q H t1 μ a c Y)

/-! ## Widths -/

theorem z0E_entryW {q H t1 : ℕ} {μ a c : ℤ} {Y : Array (ℤ × ℤ)} (ht : 1 ≤ t1)
    (h : ArrW H (W8.solveFwdBarrett q H t1 μ a c Y)) : EntryW H (z0E q H t1 μ a c Y) := by
  apply h
  rw [solveFwdBarrett_toList, ← outE_zero q H t1 μ a c Y]
  exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩

theorem zpE_entryW {q H n k : ℕ} {μ a c : ℤ} {Y : Array (ℤ × ℤ)} (ha : 0 < a)
    (hμ : μ = ((2 ^ H : ℕ) : ℤ) / a) (hb : W8.zPartFwdBound q H a c Y n) (hk : k ≤ n) :
    EntryW (H + 1) (zpE q H μ a c Y k) := by
  subst hμ
  rw [← read1D_zPartFwdBarrett q H _ a c Y n k hk]
  exact WP.W9fW.zPartFwdBarrett_entryW q H a c Y n ha hb k

theorem zhE_entryW {q H n k : ℕ} {μ a c : ℤ} (ha : 0 < a) (hμ : μ = ((2 ^ H : ℕ) : ℤ) / a)
    (hqH : q + 2 ≤ H) (hb : W8.zHomFwdBound q H a c n) (hk : k ≤ n) :
    EntryW (H + 1) (zhE q H μ a c k) := by
  subst hμ
  rw [← read1D_zHomFwdBarrett q H _ a c n k hk]
  exact WP.W9fW.zHomFwdBarrett_entryW q H a c n ha hqH hb k

/-! ## Blocks, entries, bit lengths -/

theorem blkE_nil : blkE [] = [] := by simp [blkE, blk]

theorem blkE_cons (z : ℤ × ℤ) (zs : List (ℤ × ℤ)) : blkE (z :: zs) = entrySyms z ++ blkE zs := by
  simp [blkE, blk]

theorem blkE_append (xs ys : List (ℤ × ℤ)) : blkE (xs ++ ys) = blkE xs ++ blkE ys := by
  simp [blkE, blk]

theorem entrySyms_append_head (z : ℤ × ℤ) (r : List Sym) :
    (entrySyms z ++ r).head? = some (sgnSym z.1) := by
  simp [entrySyms, intSyms]

theorem sgnSym_pos_or_neg (x : ℤ) : sgnSym x = Sym.pos ∨ sgnSym x = Sym.neg := by
  unfold sgnSym
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem toList_drop_eq (Y : Array (ℤ × ℤ)) (k : ℕ) (hk : k < Y.size) :
    Y.toList.drop k = read1D Y k :: Y.toList.drop (k + 1) := by
  have hk' : k < Y.toList.length := by simpa using hk
  rw [List.drop_eq_getElem_cons hk']
  congr 1
  simp [read1D, hk]

theorem bitLen_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  rw [bitLen, IntMulTM.length_encodeNat, Nat.size_pow]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen, IntMulTM.length_encodeNat, Nat.size_le]
  exact Nat.lt_two_pow_self

theorem bitLen_mu {H : ℕ} {a : ℤ} {μ : ℕ} (ha : 0 < a) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) :
    bitLen μ ≤ H + 1 := by
  have _hpos : 0 ≤ a := ha.le
  have h2 : ((2 ^ H : ℕ) : ℤ) / a ≤ ((2 ^ H : ℕ) : ℤ) := Int.ediv_le_self _ (by positivity)
  have h3 : (μ : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := hμ ▸ h2
  have h4 : μ ≤ 2 ^ H := by exact_mod_cast h3
  rw [bitLen, IntMulTM.length_encodeNat, Nat.size_le]
  calc μ ≤ 2 ^ H := h4
    _ < 2 ^ (H + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self H)

#assert_std_axioms size_zPartFwdBarrett size_zHomFwdBarrett read1D_zPartFwdBarrett
  read1D_zHomFwdBarrett toList_runSequentialScanSteps solveFwdBarrett_toList divRoundPow2_mul_pow
  gCombineQuantize_zero_unit outE_zero z0E_entryW zpE_entryW zhE_entryW blkE_nil blkE_cons
  blkE_append entrySyms_append_head sgnSym_pos_or_neg toList_drop_eq bitLen_two_pow bitLen_le_self
  bitLen_mu

end WP.W9fF
