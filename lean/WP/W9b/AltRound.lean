import WP.W9b.AltOps

/-!
# WP.W9b.AltRound — the signed rounding shift `z := divRoundPow2 z d` on the machine (`d ≥ 1`)

`divRoundPow2 z d = ⌊(z + 2^(d−1)) / 2^d⌋` (`divRoundPow2_pos`). The machine:
1. builds `2^(d−1)` on `F` (`1 · 2^(d−1)` by `W3_shlVar`, counter `E := d − 1`);
2. `Y := z + 2^(d−1)` (`W3_addInt`), drops `F`, `E`, `z`;
3. floor shift of `Y` by `d` (`W3_shrVar`), by the sign of `Y` (`ediv_two_pow_of_nonneg/neg`):
   `|y| / 2^d` with `pos`, or `(|y| − 1) / 2^d + 1` with `neg` (`dec`/`inc` from the framework);
4. moves the result `Y → G → z` (two guard moves keep the symbol order).
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability
open IntMul (divRoundPow2)

theorem rs_peek {K : Type} [DecidableEq K] (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun r => r = (S k).head?) 1 :=
  Runs.of_eval fun v => ⟨(S k).head?, 1, eval_peek' [] k (fun _ o => o) v S _ rfl, rfl, le_rfl⟩

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  have h := encodeNat_add_add_one 0
  simp only [Nat.add_zero, Nat.zero_add] at h
  simp [natSyms, h, encodeNat_zero]

theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  refine bitLen_le_of_lt_two_pow ?_
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

section Round

variable (k : W3Kit)

/-- Sign test: the symbol register holds `neg`. -/
def isNegR (v : KReg k) : Bool := decide ((kS k).get v = some Sym.neg)

/-- Negative branch: `|y| ↦ (|y| − 1) / 2^d + 1`, sign `neg`. -/
def drNeg : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (popR .Y)) (.seq (kSym k (dec .Y .t)) (.seq (shrV k .Y .D)
    (.seq (kSym k (inc .Y .t)) (kSym k (pushC .Y .neg)))))

/-- Nonnegative branch: `|y| ↦ |y| / 2^d`, sign `pos`. -/
def drPos : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (popR .Y)) (.seq (shrV k .Y .D) (kSym k (pushC .Y .pos)))

/-- The floor shift of `Y` by `D`, by the sign of `Y`. -/
def drBranch : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (peekR .Y)) (.ite (isNegR k) (drNeg k) (drPos k))

/-- **Signed rounding shift** `z := divRoundPow2 z d` (`d ≥ 1` on `D`). -/
def divRoundS (z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (pushC .E .mark)) (.seq (kSym k (copyBlock .D .E .t)) (.seq (kSym k (dec .E .t))
  (.seq (kSym k (pushC .F .mark)) (.seq (kSym k (pushC .F (.bit true))) (.seq (shlV k .F .E)
  (.seq (kSym k (pushC .F .pos))
  (.seq (kSym k (pushC .Y .mark)) (.seq (addI k z .F .Y)
  (.seq (kSym k (dropInt .F)) (.seq (kSym k (popR .F)) (.seq (kSym k (dropBits .E))
  (.seq (kSym k (popR .E)) (.seq (kSym k (dropInt z))
  (.seq (drBranch k)
  (.seq (kSym k (pushC .G .mark)) (.seq (kSym k (mvG .Y .G)) (kSym k (mvG .G z))))))))))))))))))

theorem rs_drBranch {C : ℕ} (hok : W3Ok k C) (y : ℤ) (dv : ℕ) (X : AStk → List Sym)
    (Yb dr : List Sym) (hYb : TermOK Yb) (hdr : TermOK dr) (hX : X .Y = intSyms y ++ Yb)
    (hD : X .D = natSyms dv ++ dr) :
    Runs (drBranch k) X (Function.update X .Y (intSyms (y / ((2 ^ dv : ℕ) : ℤ)) ++ Yb))
      (fun _ => True) (C * (dv + bitLen dv + 1) + 12 * bitLen y.natAbs + 22) := by
  have hpk := runs_liftRegs (kS k) (rs_peek AStk.Y X)
  by_cases hy : y < 0
  · -- negative: `neg`, `(|y| − 1) / 2^d + 1`
    have hsg : sgnSym y = Sym.neg := by simp [sgnSym, hy]
    have hc : Runs (kSym k (peekR .Y)) X X (fun v => isNegR k v = true) 1 :=
      runs_mono hpk (fun v (hv : (kS k).get v = (X .Y).head?) => by
        simp [isNegR, hv, hX, intSyms, hsg]) le_rfl
    have hn : y.natAbs = (y.natAbs - 1) + 1 := by
      have := Int.natAbs_pos.mpr (show y ≠ 0 by omega)
      omega
    have e1 := runs_lift (kS k) (rs_pop AStk.Y Sym.neg (natSyms y.natAbs ++ Yb) X
      (by simp [hX, intSyms, hsg]))
    set X1 := Function.update X .Y (natSyms y.natAbs ++ Yb) with hX1
    have e2 := runs_lift (kS k) (rs_dec (k := AStk.Y) (t := AStk.t) (by decide) (y.natAbs - 1) Yb
      X1 hYb (by rw [hX1, Function.update_self, ← hn]))
    set X2 := Function.update X1 .Y (natSyms (y.natAbs - 1) ++ Yb) with hX2
    have e3 := rs_shrV k hok.shr (x := AStk.Y) (c := AStk.D)
      (embL2_inj k.hR (by decide) trivial trivial) (y.natAbs - 1) dv Yb dr X2 hYb hdr
      (by rw [hX2, Function.update_self]) (by simp [hX2, hX1, hD])
    set X3 := Function.update X2 .Y (natSyms ((y.natAbs - 1) / 2 ^ dv) ++ Yb) with hX3
    have e4 := runs_lift (kS k) (rs_inc (k := AStk.Y) (t := AStk.t) (by decide)
      ((y.natAbs - 1) / 2 ^ dv) Yb X3 hYb (by rw [hX3, Function.update_self]))
    set X4 := Function.update X3 .Y (natSyms ((y.natAbs - 1) / 2 ^ dv + 1) ++ Yb) with hX4
    have e5 := runs_lift (kS k) (rs_push AStk.Y Sym.neg X4)
    have hz : zerosLead (encodeNat (y.natAbs - 1 + 1)) ≤ bitLen y.natAbs := by
      rw [← hn]
      exact zerosLead_le_length _
    have hb1 : bitLen ((y.natAbs - 1) / 2 ^ dv) ≤ bitLen y.natAbs :=
      bitLen_mono (le_trans (Nat.div_le_self _ _) (by omega))
    have hm : C * (min dv (bitLen (y.natAbs - 1)) + bitLen dv + 1) ≤ C * (dv + bitLen dv + 1) :=
      Nat.mul_le_mul_left _ (by have := min_le_left dv (bitLen (y.natAbs - 1)); omega)
    refine runs_post (runs_ite_true hc (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4
      e5))))) ?_ ?_
    · have e : intSyms (-(((y.natAbs - 1) / 2 ^ dv + 1 : ℕ) : ℤ)) =
          Sym.neg :: natSyms ((y.natAbs - 1) / 2 ^ dv + 1) := by
        simp only [intSyms, sgnSym, Int.natAbs_neg, Int.natAbs_natCast]
        rw [if_pos (neg_neg_of_pos (by positivity))]
      rw [ediv_two_pow_of_neg y hy, e]
      simp only [hX4, hX3, hX2, hX1, Function.update_idem, Function.update_self, List.cons_append]
    · omega
  · -- nonnegative: `pos`, `|y| / 2^d`
    have hy' : 0 ≤ y := by omega
    have hsg : sgnSym y = Sym.pos := by simp [sgnSym, hy]
    have hc : Runs (kSym k (peekR .Y)) X X (fun v => isNegR k v = false) 1 :=
      runs_mono hpk (fun v (hv : (kS k).get v = (X .Y).head?) => by
        simp [isNegR, hv, hX, intSyms, hsg]) le_rfl
    have e1 := runs_lift (kS k) (rs_pop AStk.Y Sym.pos (natSyms y.natAbs ++ Yb) X
      (by simp [hX, intSyms, hsg]))
    set X1 := Function.update X .Y (natSyms y.natAbs ++ Yb) with hX1
    have e2 := rs_shrV k hok.shr (x := AStk.Y) (c := AStk.D)
      (embL2_inj k.hR (by decide) trivial trivial) y.natAbs dv Yb dr X1 hYb hdr
      (by rw [hX1, Function.update_self]) (by simp [hX1, hD])
    set X2 := Function.update X1 .Y (natSyms (y.natAbs / 2 ^ dv) ++ Yb) with hX2
    have e3 := runs_lift (kS k) (rs_push AStk.Y Sym.pos X2)
    have hm : C * (min dv (bitLen y.natAbs) + bitLen dv + 1) ≤ C * (dv + bitLen dv + 1) :=
      Nat.mul_le_mul_left _ (by have := min_le_left dv (bitLen y.natAbs); omega)
    refine runs_post (runs_ite_false hc (runs_seq e1 (runs_seq e2 e3))) ?_ ?_
    · rw [ediv_two_pow_of_nonneg y hy', intSyms_natCast]
      simp only [hX2, hX1, Function.update_idem, Function.update_self, List.cons_append]
    · omega

theorem rs_divRoundS {C : ℕ} (hok : W3Ok k C) {z : AStk} (hz : z = .AI ∨ z = .AR) (zv : ℤ)
    (dv : ℕ) (hdv : 1 ≤ dv) (zr dr : List Sym) (hzr : TermOK zr) (hdr : TermOK dr)
    (S : AStk → List Sym) (hzS : S z = intSyms zv ++ zr) (hdS : S .D = natSyms dv ++ dr) :
    Runs (divRoundS k z) S (Function.update S z (intSyms (divRoundPow2 zv dv) ++ zr))
      (fun _ => True)
      (C * (bitLen zv.natAbs + 5 * dv + 3) + 25 * bitLen zv.natAbs + 45 * dv + 100) := by
  have hzE : z ≠ .E := by rcases hz with rfl | rfl <;> decide
  have hzF : z ≠ .F := by rcases hz with rfl | rfl <;> decide
  have hzY : z ≠ .Y := by rcases hz with rfl | rfl <;> decide
  have hzG : z ≠ .G := by rcases hz with rfl | rfl <;> decide
  have hzD : z ≠ .D := by rcases hz with rfl | rfl <;> decide
  have hzN : NotS z := by rcases hz with rfl | rfl <;> trivial
  have hd1 : dv = (dv - 1) + 1 := by omega
  -- E := d − 1
  have e1 := runs_lift (kS k) (rs_push AStk.E Sym.mark S)
  set S1 := Function.update S .E (Sym.mark :: S .E) with hS1
  have e2 := runs_lift (kS k) (rs_copy (src := AStk.D) (dst := AStk.E) (tmp := AStk.t)
    (by decide) (by decide) (by decide) dv dr S1 hdr (by simp [hS1, hdS]))
  set S2 := Function.update S1 .E (natSyms dv ++ S1 .E) with hS2
  have e3 := runs_lift (kS k) (rs_dec (k := AStk.E) (t := AStk.t) (by decide) (dv - 1)
    (Sym.mark :: S .E) S2 (TermOK.cons rfl _) (by simp [hS2, hS1, ← hd1]))
  set S3 := Function.update S2 .E (natSyms (dv - 1) ++ Sym.mark :: S .E) with hS3
  -- F := 2^(d−1)
  have e4 := runs_lift (kS k) (rs_push AStk.F Sym.mark S3)
  set S4 := Function.update S3 .F (Sym.mark :: S3 .F) with hS4
  have e5 := runs_lift (kS k) (rs_push AStk.F (Sym.bit true) S4)
  set S5 := Function.update S4 .F (Sym.bit true :: S4 .F) with hS5
  have e6 := rs_shlV k hok.shl (x := AStk.F) (c := AStk.E)
    (embL2_inj k.hL (by decide) trivial trivial) 1 (dv - 1) (Sym.mark :: S .F)
    (Sym.mark :: S .E) S5 (TermOK.cons rfl _) (TermOK.cons rfl _)
    (by simp [hS5, hS4, hS3, hS2, hS1, natSyms_one]) (by simp [hS5, hS4, hS3])
  set S6 := Function.update S5 .F (natSyms (1 * 2 ^ (dv - 1)) ++ Sym.mark :: S .F) with hS6
  have e7 := runs_lift (kS k) (rs_push AStk.F Sym.pos S6)
  set S7 := Function.update S6 .F (Sym.pos :: S6 .F) with hS7
  -- Y := z + 2^(d−1)
  have e8 := runs_lift (kS k) (rs_push AStk.Y Sym.mark S7)
  set S8 := Function.update S7 .Y (Sym.mark :: S7 .Y) with hS8
  have e9 := rs_addI k hok.add (x := z) (y := AStk.F) (z := AStk.Y)
    (embL3_inj k.hA hzF hzY (by decide) hzN trivial trivial) zv ((2 ^ (dv - 1) : ℕ) : ℤ) zr
    (Sym.mark :: S .F) S8 hzr (TermOK.cons rfl _)
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hzY, hzF, hzE, hzS])
    (by rw [intSyms_natCast]; simp [hS8, hS7, hS6])
  set y := zv + ((2 ^ (dv - 1) : ℕ) : ℤ) with hy
  set S9 := Function.update S8 .Y (intSyms y ++ S8 .Y) with hS9
  -- drop `F`, `E`, `z`
  have e10 := runs_lift (kS k) (rs_dropInt AStk.F ((2 ^ (dv - 1) : ℕ) : ℤ) (Sym.mark :: S .F) S9
    (TermOK.cons rfl _) (by rw [intSyms_natCast]; simp [hS9, hS8, hS7, hS6]))
  set S10 := Function.update S9 .F (Sym.mark :: S .F) with hS10
  have e11 := runs_lift (kS k) (rs_pop AStk.F Sym.mark (S .F) S10 (by simp [hS10]))
  set S11 := Function.update S10 .F (S .F) with hS11
  have e12 := runs_lift (kS k) (rs_dropNat AStk.E (dv - 1) (Sym.mark :: S .E) S11
    (TermOK.cons rfl _) (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3]))
  set S12 := Function.update S11 .E (Sym.mark :: S .E) with hS12
  have e13 := runs_lift (kS k) (rs_pop AStk.E Sym.mark (S .E) S12 (by simp [hS12]))
  set S13 := Function.update S12 .E (S .E) with hS13
  have e14 := runs_lift (kS k) (rs_dropInt z zv zr S13 hzr
    (by simp [hS13, hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
      hzE, hzF, hzY, hzS]))
  set S14 := Function.update S13 z zr with hS14
  -- floor shift
  have e15 := rs_drBranch k hok y dv S14 (Sym.mark :: S .Y) dr (TermOK.cons rfl _) hdr
    (by simp [hS14, hS13, hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
      Ne.symm hzY])
    (by simp [hS14, hS13, hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
      Ne.symm hzD, hdS])
  have hres : y / ((2 ^ dv : ℕ) : ℤ) = divRoundPow2 zv dv := (divRoundPow2_pos zv dv hdv).symm
  rw [hres] at e15
  set S15 := Function.update S14 .Y (intSyms (divRoundPow2 zv dv) ++ Sym.mark :: S .Y) with hS15
  -- move the result back onto `z`
  have e16 := runs_lift (kS k) (rs_push AStk.G Sym.mark S15)
  set S16 := Function.update S15 .G (Sym.mark :: S15 .G) with hS16
  have e17 := runs_lift (kS k) (rs_mvG (src := AStk.Y) (dst := AStk.G) (by decide)
    (intSyms (divRoundPow2 zv dv)) (S .Y) S16 (mem_intSyms_ne_mark _) (by simp [hS16, hS15]))
  set S17 := Function.update (Function.update S16 .Y (S .Y)) .G
    ((intSyms (divRoundPow2 zv dv)).reverse ++ S16 .G) with hS17
  have e18 := runs_lift (kS k) (rs_mvG (src := AStk.G) (dst := z) (Ne.symm hzG)
    (intSyms (divRoundPow2 zv dv)).reverse (S .G) S17
    (fun x hx => mem_intSyms_ne_mark _ x (List.mem_reverse.mp hx))
    (by simp [hS17, hS16, hS15, hS14, hS13, hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3,
      hS2, hS1, Ne.symm hzG]))
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 (runs_seq e6
    (runs_seq e7 (runs_seq e8 (runs_seq e9 (runs_seq e10 (runs_seq e11 (runs_seq e12
      (runs_seq e13 (runs_seq e14 (runs_seq e15 (runs_seq e16 (runs_seq e17
        e18))))))))))))))))) ?_ ?_
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 hd1 hres
    funext x
    simp only [hS17, hS16, hS15, hS14, hS13, hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3,
      hS2, hS1, Function.update_apply, List.reverse_reverse]
    clear hS17 hS16 hS15 hS14 hS13 hS12 hS11 hS10 hS9 hS8 hS7 hS6 hS5 hS4 hS3 hS2 hS1 hy
    split_ifs <;> simp_all
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
    have hbd := bitLen_le_self dv
    have hbd1 := bitLen_le_self (dv - 1)
    have hp2 : bitLen (2 ^ (dv - 1)) = dv := by rw [bitLen_two_pow]; omega
    have hnat : bitLen (((2 ^ (dv - 1) : ℕ) : ℤ)).natAbs = dv := by
      rw [Int.natAbs_natCast]
      exact hp2
    have hya : bitLen y.natAbs ≤ bitLen zv.natAbs + dv + 1 := by
      have h1 := Int.natAbs_add_le zv ((2 ^ (dv - 1) : ℕ) : ℤ)
      rw [Int.natAbs_natCast] at h1
      have h2 : bitLen y.natAbs ≤ bitLen (zv.natAbs + 2 ^ (dv - 1)) := bitLen_mono h1
      have h3 := bitLen_add_le zv.natAbs (2 ^ (dv - 1))
      omega
    have hoa : bitLen (divRoundPow2 zv dv).natAbs ≤ bitLen y.natAbs := by
      refine bitLen_mono ?_
      rw [← hres]
      by_cases hneg : y < 0
      · rw [ediv_two_pow_of_neg y hneg, Int.natAbs_neg, Int.natAbs_natCast]
        have h1 := Nat.div_le_self (y.natAbs - 1) (2 ^ dv)
        have h2 := Int.natAbs_pos.mpr (show y ≠ 0 by omega)
        omega
      · rw [ediv_two_pow_of_nonneg y (by omega), Int.natAbs_natCast]
        exact Nat.div_le_self _ _
    have hC1 : C * (dv - 1 + bitLen (dv - 1) + 1) + C * (bitLen zv.natAbs + dv + 1) +
        C * (dv + bitLen dv + 1) ≤ C * (bitLen zv.natAbs + 5 * dv + 3) := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    have hzl : zerosLead (encodeNat (dv - 1 + 1)) ≤ dv := by
      rw [← hd1]
      exact le_trans (zerosLead_le_length _) hbd
    have hlo : (intSyms (divRoundPow2 zv dv)).length ≤ bitLen zv.natAbs + dv + 2 := by
      rw [length_intSyms]
      omega
    rw [hnat]
    simp only [List.length_reverse]
    by_contra hc; omega

theorem closed_divRoundS (z : AStk) (hA : k.PA.Closed) (hL : k.PL.Closed) (hR : k.PR.Closed) :
    (divRoundS k z).Closed := by
  have hA' : k.PA.FreeBelow 0 := hA
  have hL' : k.PL.FreeBelow 0 := hL
  have hR' : k.PR.FreeBelow 0 := hR
  simp [Prog.Closed, Prog.FreeBelow, divRoundS, drBranch, drNeg, drPos, kSym, addI, shlV, shrV,
    freeBelow_liftRegs, freeBelow_mapStk, hA', hL', hR', pushC, copyBlock, moveBlock, moveBits,
    moveBitsBody, moveBitsDup, dupBody, restoreR, pushR, popR, peekR, Lib.skip, dec, decFix,
    scanLoop, scanBody, inc, incFix, dropInt, dropBits, dropBody, mvG, mvGBody]

end Round

#assert_std_axioms rs_peek natSyms_one bitLen_add_le length_intSyms rs_drBranch rs_divRoundS
  closed_divRoundS

end WP.W9b
