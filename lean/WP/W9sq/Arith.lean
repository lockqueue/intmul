import WP.W9sq.Host

/-!
# WP.W9sq.Arith — value facts for the square stage

* `sqE q e = gConj (gMulScaled q e e)` is entry `u` of `rootSquareV` (`rootSquareV_toList`).
* `divRoundPow2` with `q > 0` by the sign of its argument (`Int` division is floor division):
  `w ≥ 0 ↦ (|w| + 2^(q-1)) / 2^q`, `w < 0 ↦ -((|w| + 2^(q-1) - 1) / 2^q)` (natural division).
  `rnd` is the machine's rounding (one `addNat`, one `shrVar`, one `attachSign` per branch).
* Encodings: doubling a positive natural pushes one `0` bit; bit-length bounds of products.
-/

namespace WP.W9sq

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-! ## The entry map -/

/-- Entry `u` of `rootSquareV p0 K0 z` is `sqE (p0 + 2) z_u`. -/
def sqE (q : ℕ) (e : ℤ × ℤ) : ℤ × ℤ := gConj (gMulScaled q e e)

theorem sqE_eq (q : ℕ) (e : ℤ × ℤ) :
    sqE q e = (divRoundPow2 (e.1 * e.1 - e.2 * e.2) q, -divRoundPow2 (e.1 * e.2 + e.2 * e.1) q) :=
  rfl

theorem toList_runSeq {α : Type} (f : ℕ → α) :
    ∀ n, (runSequentialScanSteps f n).outTape.toList = (List.range n).map f
  | 0 => rfl
  | n + 1 => by
    simp [runSequentialScanSteps, scanHeadStep, toList_runSeq f n, List.range_succ]

theorem rootSquareV_toList (p0 K0 : ℕ) (z : Array (ℤ × ℤ)) (hz : z.size = 2 ^ K0) :
    (rootSquareV p0 K0 z).toList = z.toList.map (sqE (p0 + 2)) := by
  unfold rootSquareV
  rw [toList_runSeq]
  apply List.ext_getElem
  · simp [hz]
  · intro i h1 h2
    have hi : i < z.size := by simp at h2; omega
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    unfold read1D
    rw [dif_pos hi]
    rfl

/-! ## Rounding by the sign -/

theorem ediv_eq_of {a d qq r : ℤ} (hd : 0 < d) (h : r + d * qq = a) (h0 : 0 ≤ r) (h1 : r < d) :
    a / d = qq := by
  rw [← h, Int.add_mul_ediv_left r qq (ne_of_gt hd), Int.ediv_eq_zero_of_lt h0 h1, zero_add]

theorem pos_aux (n h d : ℕ) (hd : 0 < d) :
    ((n : ℤ) + (h : ℤ)) / (d : ℤ) = (((n + h) / d : ℕ) : ℤ) := by
  have hm := Nat.mod_add_div (n + h) d
  have hl := Nat.mod_lt (n + h) hd
  apply ediv_eq_of (r := (((n + h) % d : ℕ) : ℤ)) (by exact_mod_cast hd)
  · exact_mod_cast hm
  · positivity
  · exact_mod_cast hl

theorem neg_aux (n h d : ℕ) (hh : 1 ≤ h) (hd : d = 2 * h) :
    (-(n : ℤ) + (h : ℤ)) / (d : ℤ) = -(((n + (h - 1)) / d : ℕ) : ℤ) := by
  have hdpos : 0 < d := by omega
  have hm := Nat.mod_add_div (n + (h - 1)) d
  have hl := Nat.mod_lt (n + (h - 1)) hdpos
  set R := (n + (h - 1)) % d
  set Q := (n + (h - 1)) / d
  have e1 : (R : ℤ) + (d : ℤ) * (Q : ℤ) = (n : ℤ) + (h : ℤ) - 1 := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hm
    push_cast [Nat.cast_sub hh] at this
    linarith
  have e2 : (d : ℤ) = 2 * (h : ℤ) := by exact_mod_cast hd
  apply ediv_eq_of (r := (d : ℤ) - 1 - (R : ℤ)) (by omega)
  · linarith
  · omega
  · omega

theorem divRoundPow2_of_nonneg {w : ℤ} {q : ℕ} (hq : 0 < q) (hw : 0 ≤ w) :
    divRoundPow2 w q = (((w.natAbs + 2 ^ (q - 1)) / 2 ^ q : ℕ) : ℤ) := by
  unfold divRoundPow2
  rw [if_neg (by omega)]
  have hw' : w = ((w.natAbs : ℕ) : ℤ) := by omega
  conv_lhs => rw [hw']
  exact pos_aux _ _ _ (by positivity)

theorem divRoundPow2_of_neg {w : ℤ} {q : ℕ} (hq : 0 < q) (hw : w < 0) :
    divRoundPow2 w q = -(((w.natAbs + (2 ^ (q - 1) - 1)) / 2 ^ q : ℕ) : ℤ) := by
  unfold divRoundPow2
  rw [if_neg (by omega)]
  have hw' : w = -((w.natAbs : ℕ) : ℤ) := by omega
  conv_lhs => rw [hw']
  exact neg_aux _ _ _ Nat.one_le_two_pow (by rw [← pow_succ']; congr 1; omega)

/-- The machine's rounding: magnitude `(|w| + H) / 2^q` (sign `pos`) or `(|w| + (H-1)) / 2^q`
(sign `neg`), with the compile-time signs `bneg` / `bpos` attached. -/
def rnd (bneg bpos : Bool) (H q : ℕ) (w : ℤ) : ℤ :=
  if w < 0 then
    (if bneg then -(((w.natAbs + (H - 1)) / 2 ^ q : ℕ) : ℤ)
      else (((w.natAbs + (H - 1)) / 2 ^ q : ℕ) : ℤ))
  else
    (if bpos then -(((w.natAbs + H) / 2 ^ q : ℕ) : ℤ) else (((w.natAbs + H) / 2 ^ q : ℕ) : ℤ))

theorem rnd_re {q : ℕ} (hq : 0 < q) (w : ℤ) : rnd true false (2 ^ (q - 1)) q w = divRoundPow2 w q := by
  unfold rnd
  by_cases hw : w < 0
  · rw [if_pos hw, if_pos rfl, divRoundPow2_of_neg hq hw]
  · rw [if_neg hw, if_neg Bool.false_ne_true, divRoundPow2_of_nonneg hq (by omega)]

theorem rnd_im {q : ℕ} (hq : 0 < q) (w : ℤ) :
    rnd false true (2 ^ (q - 1)) q w = -divRoundPow2 w q := by
  unfold rnd
  by_cases hw : w < 0
  · rw [if_pos hw, if_neg Bool.false_ne_true, divRoundPow2_of_neg hq hw, neg_neg]
  · rw [if_neg hw, if_pos rfl, divRoundPow2_of_nonneg hq (by omega)]

/-! ## Encodings and bit lengths -/

theorem natSyms_double {n : ℕ} (hn : 0 < n) : natSyms (2 * n) = Sym.bit false :: natSyms n := by
  unfold natSyms
  rw [two_mul, encodeNat_add, if_neg]
  · rfl
  · rw [encodeNat_eq_nil_iff]
    omega

theorem natSyms_double_add_one (n : ℕ) : natSyms (2 * n + 1) = Sym.bit true :: natSyms n := by
  unfold natSyms
  rw [two_mul, encodeNat_add_add_one]
  rfl

theorem natSyms_one' : natSyms 1 = [Sym.bit true] := by
  have h := natSyms_double_add_one 0
  simpa [natSyms, encodeNat_zero] using h

theorem natSyms_two_pow_succ (k : ℕ) : natSyms (2 ^ (k + 1)) = Sym.bit false :: natSyms (2 ^ k) := by
  rw [pow_succ', natSyms_double (by positivity)]

theorem bitLen_natAbs_mul_le {x y : ℤ} {w : ℕ} (hx : bitLen x.natAbs ≤ w) (hy : bitLen y.natAbs ≤ w) :
    bitLen (x * y).natAbs ≤ 2 * w := by
  rw [Int.natAbs_mul]
  have := bitLen_mul_le x.natAbs y.natAbs
  omega

theorem bitLen_natAbs_add_le {u v : ℤ} {w : ℕ} (hu : bitLen u.natAbs ≤ w) (hv : bitLen v.natAbs ≤ w) :
    bitLen (u + v).natAbs ≤ w + 1 := by
  have h1 := bitLen_mono (Int.natAbs_add_le u v)
  have h2 := bitLen_add_le u.natAbs v.natAbs
  omega

theorem bitLen_natAbs_sub_le {u v : ℤ} {w : ℕ} (hu : bitLen u.natAbs ≤ w) (hv : bitLen v.natAbs ≤ w) :
    bitLen (u - v).natAbs ≤ w + 1 := by
  have h1 := bitLen_mono (Int.natAbs_sub_le u v)
  have h2 := bitLen_add_le u.natAbs v.natAbs
  omega

theorem bitLen_pred_le (n : ℕ) : bitLen (n - 1) ≤ bitLen n := bitLen_mono (Nat.sub_le n 1)

#assert_std_axioms sqE_eq toList_runSeq rootSquareV_toList ediv_eq_of pos_aux neg_aux
  divRoundPow2_of_nonneg divRoundPow2_of_neg rnd_re rnd_im natSyms_double natSyms_double_add_one
  natSyms_one' natSyms_two_pow_succ bitLen_natAbs_mul_le bitLen_natAbs_add_le bitLen_natAbs_sub_le
  bitLen_pred_le

end WP.W9sq
