import WP.W9c.BlockPackOps

/-!
# WP.W9c.BlockPackQuant — quantize one magnitude in place

`quantP`: with `|v|` on `x` (followed by `sep`) and the sign symbol of `v` on top of `SG`,
replace `|v|` by `qMag p_in q v` (`ht_quant`). With `u = p_in + 1` on `U`: if `u < q`, shift left
by `q - u`; otherwise decrement when `v < 0` and shift right by `u - q`; then `(· + 1) / 2`.
`SH` holds the shift amount. Cost `≤ 12·C·U + 12` for any `U ≥ 2(B + p_in + q + 2)`.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- The shifted magnitude before rounding. -/
def qX (p_in q : ℕ) (v : ℤ) : ℕ :=
  if p_in + 1 < q then v.natAbs * 2 ^ (q - (p_in + 1))
  else (if v < 0 then v.natAbs - 1 else v.natAbs) / 2 ^ (p_in + 1 - q)

theorem qMag_eq_qX (p_in q : ℕ) (v : ℤ) : qMag p_in q v = (qX p_in q v + 1) / 2 := rfl

theorem qX_L {p_in q : ℕ} (v : ℤ) (h : p_in + 1 < q) :
    qX p_in q v = v.natAbs * 2 ^ (q - (p_in + 1)) := if_pos h

theorem qX_R {p_in q : ℕ} (v : ℤ) (h : ¬ p_in + 1 < q) :
    qX p_in q v = (if v < 0 then v.natAbs - 1 else v.natAbs) / 2 ^ (p_in + 1 - q) := if_neg h

theorem bitLen_qX (p_in q B : ℕ) (v : ℤ) (hB : bitLen v.natAbs ≤ B) :
    bitLen (qX p_in q v) ≤ B + q := by
  apply bitLen_le_of_lt
  have hv : v.natAbs < 2 ^ B := (bitLen_le_iff B _).mp hB
  have hBq : 2 ^ B ≤ 2 ^ (B + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold qX
  split_ifs with h1 h2
  · calc v.natAbs * 2 ^ (q - (p_in + 1)) < 2 ^ B * 2 ^ (q - (p_in + 1)) :=
          Nat.mul_lt_mul_of_pos_right hv (by positivity)
      _ = 2 ^ (B + (q - (p_in + 1))) := by rw [pow_add]
      _ ≤ 2 ^ (B + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have : (v.natAbs - 1) / 2 ^ (p_in + 1 - q) ≤ v.natAbs - 1 := Nat.div_le_self _ _
    omega
  · have : v.natAbs / 2 ^ (p_in + 1 - q) ≤ v.natAbs := Nat.div_le_self _ _
    omega

theorem ordOf_lt_iff (a b : ℕ) : Lib.ordOf a b = .lt ↔ a < b := by
  unfold Lib.ordOf
  split_ifs with h1 h2 <;> simp_all

theorem sgnSym_eq_neg (v : ℤ) : sgnSym v = Sym.neg ↔ v < 0 := by
  unfold sgnSym
  split_ifs with h <;> simp_all

theorem termOK_sep (l : List Sym) : TermOK (Sym.sep :: l) := TermOK.cons rfl l

theorem ones_le_bitLen (x : ℕ) : ones (encodeNat x) ≤ bitLen x := ones_le_length _

theorem zerosLead_le_bitLen (x : ℕ) : zerosLead (encodeNat x) ≤ bitLen x := zerosLead_le_length _

section

variable (K : Kit)

/-- Quantize the magnitude on `x` in place (sign of the number on top of `SG`). -/
def quantP : BProg 6 8 K.Reg :=
  (cCopy K kP kU).seq <|
  (cInc K kU).seq <|
  (cCmpIte K kU kQ (fun o => decide (o = .lt))
    ((cSub K kQ kU kSH).seq ((cShl K kX kSH).seq (cDrop K kSH)))
    ((cSub K kU kQ kSH).seq
      ((ifTopP K.lS1 kSG (fun x => decide (x = Sym.neg)) (cDec K kX) skipP).seq
        ((cShr K kX kSH).seq (cDrop K kSH))))).seq <|
  (cDrop K kU).seq <|
  (cInc K kX).seq (cShr1 K kX)

theorem quantP_closed : (quantP K).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _,
    cCmpIte_closed _ _ _ ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
      ⟨callI_closed _ _ _ _, ifTopP_closed _ _ _ (callI_closed _ _ _ _) trivial,
        callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

end

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- **Quantization step.** -/
theorem ht_quant (hK : K.OK C) (r : HS) (v : ℤ) (p_in q B U : ℕ) (rest ra rb sg0 : List Sym)
    (hra : TermOK ra) (hrb : TermOK rb)
    (hx : r.x = natSyms v.natAbs ++ Sym.sep :: rest) (hsg : r.sg = sgnSym v :: sg0)
    (hp : r.p = natSyms p_in ++ ra) (hq : r.q = natSyms q ++ rb)
    (hu : TermOK r.u) (hsh : TermOK r.sh) (hB : bitLen v.natAbs ≤ B)
    (hU : 2 * (B + p_in + q + 2) ≤ U) :
    HT ρ r.f (quantP K) (r.set kX (natSyms (qMag p_in q v) ++ Sym.sep :: rest)).f
      (12 * (C * U) + 12) := by
  have bP := bitLen_le_self p_in
  have bP1 := bitLen_le_self (p_in + 1)
  have bQ := bitLen_le_self q
  have cU : ∀ x, x ≤ U → C * x ≤ C * U := fun x hx => Nat.mul_le_mul_left C hx
  -- U := p_in, then p_in + 1
  let r1 := r.set kU (natSyms p_in ++ r.u)
  let r2 := r.set kU (natSyms (p_in + 1) ++ r.u)
  have h1 : HT ρ r.f (cCopy K kP kU) r1.f (C * (bitLen p_in + 1)) :=
    ht_copy hK r kP kU (by decide) p_in ra hra hp
  have h2 : HT ρ r1.f (cInc K kU) r2.f (C * (ones (encodeNat p_in) + 1)) :=
    ht_inc hK r1 kU p_in r.u hu rfl
  -- the branch, up to the shifted magnitude `qX`
  have h3 : HT ρ r2.f
      (cCmpIte K kU kQ (fun o => decide (o = .lt))
        ((cSub K kQ kU kSH).seq ((cShl K kX kSH).seq (cDrop K kSH)))
        ((cSub K kU kQ kSH).seq
          ((ifTopP K.lS1 kSG (fun x => decide (x = Sym.neg)) (cDec K kX) skipP).seq
            ((cShr K kX kSH).seq (cDrop K kSH)))))
      (r2.set kX (natSyms (qX p_in q v) ++ Sym.sep :: rest)).f
      (C * (bitLen (p_in + 1) + bitLen q + 1) + (max (4 * (C * U) + 3) (4 * (C * U) + 3) + 1)) := by
    refine ht_cmpIte hK r2 (r2.set kX (natSyms (qX p_in q v) ++ Sym.sep :: rest)) kU kQ
      (by decide) (p_in + 1) q r.u rb hu hrb rfl hq _ _ _ ?_ ?_
    · intro hc
      have hlt : p_in + 1 < q := (ordOf_lt_iff _ _).mp (of_decide_eq_true hc)
      rw [qX_L v hlt]
      let a1 := r2.set kSH (natSyms (q - (p_in + 1)) ++ r.sh)
      let a2 := a1.set kX (natSyms (v.natAbs * 2 ^ (q - (p_in + 1))) ++ Sym.sep :: rest)
      have s1 : HT ρ r2.f (cSub K kQ kU kSH) a1.f (C * (bitLen q + bitLen (p_in + 1) + 1)) :=
        ht_sub hK r2 kQ kU kSH (by decide) q (p_in + 1) rb r.u hrb hu hlt.le hq rfl
      have s2 : HT ρ a1.f (cShl K kX kSH) a2.f
          (C * (q - (p_in + 1) + bitLen (q - (p_in + 1)) + 1)) :=
        ht_shl hK a1 kX kSH (by decide) v.natAbs (q - (p_in + 1)) (Sym.sep :: rest) r.sh
          (termOK_sep _) hsh hx rfl
      have s3 : HT ρ a2.f (cDrop K kSH) (a2.set kSH r.sh).f
          (C * (bitLen (q - (p_in + 1)) + 1)) :=
        ht_drop hK a2 kSH (q - (p_in + 1)) r.sh hsh rfl
      refine (HT.seq s1 (HT.seq s2 s3)).of_eq rfl ?_
      have e1 := cU (bitLen q + bitLen (p_in + 1) + 1) (by omega)
      have e2 := cU (q - (p_in + 1) + bitLen (q - (p_in + 1)) + 1)
        (by have := bitLen_le_self (q - (p_in + 1)); omega)
      have e3 := cU (bitLen (q - (p_in + 1)) + 1)
        (by have := bitLen_le_self (q - (p_in + 1)); omega)
      omega
    · intro hc
      have hge : ¬ p_in + 1 < q := fun h =>
        absurd (decide_eq_true ((ordOf_lt_iff _ _).mpr h)) (by rw [hc]; decide)
      rw [qX_R v hge]
      let a1 := r2.set kSH (natSyms (p_in + 1 - q) ++ r.sh)
      have s1 : HT ρ r2.f (cSub K kU kQ kSH) a1.f (C * (bitLen (p_in + 1) + bitLen q + 1)) :=
        ht_sub hK r2 kU kQ kSH (by decide) (p_in + 1) q r.u rb hu hrb (by omega) rfl hq
      -- conditional decrement
      have s2 : HT ρ a1.f
          (ifTopP K.lS1 kSG (fun x => decide (x = Sym.neg)) (cDec K kX) skipP)
          (a1.set kX (natSyms (if v < 0 then v.natAbs - 1 else v.natAbs) ++ Sym.sep :: rest)).f
          (1 + (max (C * U + 1) (C * U + 1) + 1)) := by
        have hsg' : (a1.f kSG).head? = some (sgnSym v) := by
          show r.sg.head? = _
          rw [hsg]
          rfl
        refine ht_ifTop a1 _ kSG _ _ _ ?_ ?_
        · intro hc2
          rw [hsg'] at hc2
          have hv : v < 0 := (sgnSym_eq_neg v).mp (of_decide_eq_true hc2)
          rw [if_pos hv]
          have ha : 1 ≤ v.natAbs := by omega
          have d1 : HT ρ a1.f (cDec K kX)
              (a1.set kX (natSyms (v.natAbs - 1) ++ Sym.sep :: rest)).f
              (C * (zerosLead (encodeNat (v.natAbs - 1 + 1)) + 1)) :=
            ht_dec hK a1 kX (v.natAbs - 1) (Sym.sep :: rest) (termOK_sep _)
              (by show r.x = _; rw [hx, Nat.sub_add_cancel ha])
          refine d1.of_eq rfl ?_
          have hz := zerosLead_le_bitLen (v.natAbs - 1 + 1)
          rw [Nat.sub_add_cancel ha] at hz
          have e := cU (zerosLead (encodeNat (v.natAbs - 1 + 1)) + 1)
            (by rw [Nat.sub_add_cancel ha]; omega)
          omega
        · intro hc2
          rw [hsg'] at hc2
          have hv : ¬ v < 0 := fun h =>
            absurd (decide_eq_true ((sgnSym_eq_neg v).mpr h)) (by
              have : decide (sgnSym v = Sym.neg) = false := hc2
              rw [this]; decide)
          rw [if_neg hv]
          have e : a1.set kX (natSyms v.natAbs ++ Sym.sep :: rest) = a1 := by
            rw [← hx]
            rfl
          rw [e]
          exact (ht_skip a1).mono (by omega)
      have mle : (if v < 0 then v.natAbs - 1 else v.natAbs) ≤ v.natAbs := by split_ifs <;> omega
      let a2 := a1.set kX (natSyms (if v < 0 then v.natAbs - 1 else v.natAbs) ++ Sym.sep :: rest)
      let a3 := a2.set kX (natSyms ((if v < 0 then v.natAbs - 1 else v.natAbs) /
        2 ^ (p_in + 1 - q)) ++ Sym.sep :: rest)
      have s3 : HT ρ a2.f (cShr K kX kSH) a3.f
          (C * (min (p_in + 1 - q) (bitLen (if v < 0 then v.natAbs - 1 else v.natAbs)) +
            bitLen (p_in + 1 - q) + 1)) :=
        ht_shr hK a2 kX kSH (by decide) (if v < 0 then v.natAbs - 1 else v.natAbs)
          (p_in + 1 - q) (Sym.sep :: rest) r.sh (termOK_sep _) hsh rfl rfl
      have s4 : HT ρ a3.f (cDrop K kSH) (a3.set kSH r.sh).f (C * (bitLen (p_in + 1 - q) + 1)) :=
        ht_drop hK a3 kSH (p_in + 1 - q) r.sh hsh rfl
      refine (HT.seq s1 (HT.seq s2 (HT.seq s3 s4))).of_eq rfl ?_
      have bm := bitLen_mono mle
      have e1 := cU (bitLen (p_in + 1) + bitLen q + 1) (by omega)
      have e3 := cU (min (p_in + 1 - q) (bitLen (if v < 0 then v.natAbs - 1 else v.natAbs)) +
        bitLen (p_in + 1 - q) + 1)
        (by have := bitLen_le_self (p_in + 1 - q); have := min_le_right (p_in + 1 - q)
              (bitLen (if v < 0 then v.natAbs - 1 else v.natAbs)); omega)
      have e4 := cU (bitLen (p_in + 1 - q) + 1) (by have := bitLen_le_self (p_in + 1 - q); omega)
      rw [max_self]
      omega
  -- drop `U`, round
  let r3 := r2.set kX (natSyms (qX p_in q v) ++ Sym.sep :: rest)
  let r4 := r3.set kU r.u
  let r5 := r4.set kX (natSyms (qX p_in q v + 1) ++ Sym.sep :: rest)
  have h4 : HT ρ r3.f (cDrop K kU) r4.f (C * (bitLen (p_in + 1) + 1)) :=
    ht_drop hK r3 kU (p_in + 1) r.u hu rfl
  have h5 : HT ρ r4.f (cInc K kX) r5.f (C * (ones (encodeNat (qX p_in q v)) + 1)) :=
    ht_inc hK r4 kX (qX p_in q v) (Sym.sep :: rest) (termOK_sep _) rfl
  have h6 : HT ρ r5.f (cShr1 K kX)
      (r5.set kX (natSyms ((qX p_in q v + 1) / 2) ++ Sym.sep :: rest)).f (C * 2) :=
    ht_shr1 hK r5 kX (qX p_in q v + 1) (Sym.sep :: rest) (termOK_sep _) rfl
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 (HT.seq h5 h6))))).of_eq rfl ?_
  have bX := bitLen_qX p_in q B v hB
  have o1 := ones_le_bitLen p_in
  have o2 := ones_le_bitLen (qX p_in q v)
  have e1 := cU (bitLen p_in + 1) (by omega)
  have e2 := cU (ones (encodeNat p_in) + 1) (by omega)
  have e3 := cU (bitLen (p_in + 1) + bitLen q + 1) (by omega)
  have e4 := cU (bitLen (p_in + 1) + 1) (by omega)
  have e5 := cU (ones (encodeNat (qX p_in q v)) + 1) (by omega)
  have e6 := cU 2 (by omega)
  rw [max_self]
  omega

#assert_std_axioms qMag_eq_qX qX_L qX_R bitLen_qX ordOf_lt_iff sgnSym_eq_neg termOK_sep
  ones_le_bitLen zerosLead_le_bitLen quantP_closed ht_quant

end WP.W9c.BlockPack
