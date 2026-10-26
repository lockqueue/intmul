import WP.W9fC.Data

/-!
# WP.W9fC.Facts — symbol, list and size facts used by the phase proofs

* `Vals.ext'`; `natSyms_zero`; membership of the guard / marks / separators in encodings.
* Heads: `optIsBit_head_natSyms` (the counter test), `Dat.head_trAt` (the column-loop test).
* `bitLen` facts (`bl_mono`, `bl_two_pow`; the proofs follow `WP.W7k2.Arith`), the header split
  `c0_split` and the header length bound `hdrLen_ge`.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

theorem Vals.ext' {V V' : Vals} (h1 : V.w0 = V'.w0) (h2 : V.tr = V'.tr) (h3 : V.tl = V'.tl)
    (h4 : V.c3 = V'.c3) (h5 : V.rq = V'.rq) (h6 : V.c0 = V'.c0) (h7 : V.sm = V'.sm)
    (h8 : V.sm2 = V'.sm2) (h9 : V.st = V'.st) (h10 : V.sa = V'.sa) (h11 : V.sct = V'.sct)
    (h12 : V.scw = V'.scw) : V = V' := by
  cases V
  cases V'
  simp only [Vals.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem isBit_of_mem_natSyms {n : ℕ} {x : Sym} (hx : x ∈ natSyms n) : x.isBit = true := by
  simp only [natSyms, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  rfl

theorem not_mem_natSyms {n : ℕ} {x : Sym} (hx : x.isBit = false) : x ∉ natSyms n := fun h => by
  rw [isBit_of_mem_natSyms h] at hx
  exact Bool.noConfusion hx

theorem termOK_guard (l : List Sym) : TermOK (symGuard :: l) := TermOK.cons rfl l

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

theorem mem_entrySyms {z : ℤ × ℤ} {x : Sym} (hx : x ∈ entrySyms z) :
    isDataSym x = true ∨ x = Sym.sep := by
  unfold entrySyms at hx
  rw [List.mem_append, List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | rfl | h | rfl
  · exact Or.inl (isData_intSyms _ _ h)
  · exact Or.inl rfl
  · exact Or.inl (isData_intSyms _ _ h)
  · exact Or.inr rfl

theorem mem_blkE {v : List (ℤ × ℤ)} {x : Sym} (hx : x ∈ blkE v) :
    isDataSym x = true ∨ x = Sym.sep := by
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨z, -, rfl⟩, hx⟩ := hx
  exact mem_entrySyms hx

theorem guard_not_mem_blkE (v : List (ℤ × ℤ)) : symGuard ∉ blkE v := fun h =>
  (mem_blkE h).elim (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

theorem guard_not_mem_rev_blkE (v : List (ℤ × ℤ)) : symGuard ∉ (blkE v).reverse := by
  rw [List.mem_reverse]
  exact guard_not_mem_blkE v

/-- The payload of an entry record. -/
def recD (z : ℤ × ℤ) : List Sym := intSyms z.1 ++ Sym.sep2 :: intSyms z.2

theorem isData_recD (z : ℤ × ℤ) : ∀ x ∈ recD z, isDataSym x = true := by
  intro x hx
  unfold recD at hx
  rw [List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h
  · exact isData_intSyms _ _ h
  · rfl
  · exact isData_intSyms _ _ h

theorem sep_not_mem_recD (z : ℤ × ℤ) : Sym.sep ∉ recD z := fun h =>
  absurd (isData_recD z _ h) (by decide)

theorem entrySyms_append (z : ℤ × ℤ) (rest : List Sym) :
    entrySyms z ++ rest = recD z ++ Sym.sep :: rest := by
  simp [entrySyms, recD]

theorem length_recD (z : ℤ × ℤ) : (recD z).length + 1 = (entrySyms z).length := by
  simp only [entrySyms, recD, List.length_append, List.length_cons, List.length_nil]
  omega

theorem blkE_cons (z : ℤ × ℤ) (v : List (ℤ × ℤ)) : blkE (z :: v) = entrySyms z ++ blkE v := by
  simp [blkE, blk]

theorem blkE_nil : blkE [] = [] := rfl

theorem entrySyms_eq_recD (z : ℤ × ℤ) : entrySyms z = recD z ++ [Sym.sep] := by
  simp [entrySyms, recD]

theorem optIsBit_head_natSyms (n : ℕ) {rest : List Sym} (hrest : TermOK rest) :
    optIsBit (natSyms n ++ rest).head? = decide (0 < n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [natSyms_zero, List.nil_append, optIsBit_head?_of_termOK hrest]
    rfl
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => exact absurd ((encodeNat_eq_nil_iff n).1 h) (by omega)
      | cons b l => exact ⟨b, l, rfl⟩
    rw [natSyms, hbl, decide_eq_true hn]
    rfl

variable {m : ℕ}

theorem Dat.head_trAt (D : Dat m) (u2 : ℕ) :
    isDataR (D.trAt u2).head? = decide (u2 < D.h.r) := by
  by_cases hu : u2 < D.h.r
  · rw [D.trAt_succ hu, D.recOf_eq, decide_eq_true hu]
    simp only [postRecSyms, intSyms, List.cons_append, List.head?_cons]
    show isDataSym (sgnSym _) = true
    unfold sgnSym
    split <;> rfl
  · rw [decide_eq_false hu]
    unfold Dat.trAt
    rw [List.drop_of_length_le (by simp; omega)]
    rfl

/-! ## `bitLen` -/

theorem bl_double_add_one (k : ℕ) : bitLen (2 * k + 1) = bitLen k + 1 := by
  unfold bitLen
  rw [two_mul, encodeNat_add_add_one]
  rfl

theorem bl_double (k : ℕ) (hk : 0 < k) : bitLen (2 * k) = bitLen k + 1 := by
  unfold bitLen
  rw [two_mul, encodeNat_add, if_neg]
  · rfl
  · rw [encodeNat_eq_nil_iff]
    omega

theorem bl_div2 (n : ℕ) (h : 0 < n) : bitLen n = bitLen (n / 2) + 1 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [bl_double k (by omega)]
    congr 2
    omega
  · rw [bl_double_add_one]
    congr 2
    omega

theorem bl_eq_zero_iff (n : ℕ) : bitLen n = 0 ↔ n = 0 := by
  unfold bitLen
  rw [List.length_eq_zero_iff, encodeNat_eq_nil_iff]

theorem bl_le_iff : ∀ (k n : ℕ), bitLen n ≤ k ↔ n < 2 ^ k
  | 0, n => by
    rw [Nat.le_zero, bl_eq_zero_iff, pow_zero]
    omega
  | k + 1, n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bitLen_zero']
      exact ⟨fun _ => by positivity, fun _ => by omega⟩
    · rw [bl_div2 n hn, Nat.add_le_add_iff_right, bl_le_iff k (n / 2), pow_succ]
      omega

theorem bl_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b :=
  (bl_le_iff _ a).mpr (lt_of_le_of_lt h ((bl_le_iff _ b).mp le_rfl))

theorem bl_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have h1 : bitLen (2 ^ k) ≤ k + 1 := (bl_le_iff _ _).mpr (by rw [pow_succ]; omega)
  have h2 : ¬ bitLen (2 ^ k) ≤ k := fun h => by
    have := (bl_le_iff k (2 ^ k)).mp h
    omega
  omega

/-! ## The POST header -/

theorem c0_split {h : PostHdr} {σ : BLoc m → List Sym} (hc : PostCtx h σ) :
    ∃ rest3 : List Sym, σ (.inl .C0) = natSyms h.p ++ Sym.mark ::
      (natSyms h.pSub ++ Sym.mark :: (natSyms h.t1 ++ Sym.mark :: rest3)) := by
  obtain ⟨r0, hr0⟩ := hc
  refine ⟨hdrSyms [h.r, natLog2Fuel h.t1 h.t1, natLog2Fuel h.r h.r, h.pChild, barrettH h.pSub] ++
    r0, ?_⟩
  rw [hr0]
  simp [hdrSyms, postFields, List.append_assoc]

theorem hdrLen_ge (h : PostHdr) :
    bitLen h.p + bitLen h.pSub + bitLen h.t1 + bitLen h.r + 4 ≤ h.hdrLen := by
  simp only [PostHdr.hdrLen, hdrSyms, postFields, List.flatMap_cons, List.flatMap_nil,
    List.length_append, length_natSyms, List.length_singleton, List.length_nil]
  omega

#assert_std_axioms Vals.ext' natSyms_zero isBit_of_mem_natSyms not_mem_natSyms termOK_guard
  termOK_mark mem_entrySyms mem_blkE guard_not_mem_blkE guard_not_mem_rev_blkE isData_recD
  sep_not_mem_recD entrySyms_append length_recD blkE_cons blkE_nil entrySyms_eq_recD
  optIsBit_head_natSyms Dat.head_trAt
  bl_double_add_one bl_double bl_div2 bl_eq_zero_iff bl_le_iff bl_mono bl_two_pow c0_split
  hdrLen_ge

end WP.W9fC
