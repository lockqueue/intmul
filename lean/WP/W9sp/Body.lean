import WP.W9sp.State

/-!
# WP.W9sp.Body — one loop iteration: one packed entry

`halfP K x` (`x = OA` or `OB`): `splitAt` moves the low `b` bits of `x` to `sT` (canonical), `shl2`
multiplies them by 4, `moveBlk` pops them onto `sO` LSB first. `bodyP K` pushes
`pos · bits(4a) · sep2 · pos · bits(4b) · sep` onto `sO` in this order, i.e. `⟦(4a, 4b)⟧`
reversed (`rev_entry`). One iteration costs at most `cbody C b = O(C·(b+1))`.
-/

namespace WP.W9sp

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability

variable (K : Kit)

/-- Half an entry from operand stack `x`: `x ↦ x / 2^b`, then `4·(x mod 2^b)` onto `sO`. -/
def halfP (x : H) : Prog H (fun _ => Sym) K.Reg :=
  (K.pSplit x sB sT).seq ((K.pShl2 sT).seq (moveBlk K.lS sT sO))

/-- One loop iteration: entry `⟦(4a, 4b)⟧` onto `sO`, in natural symbol order. -/
def bodyP : Prog H (fun _ => Sym) K.Reg :=
  (pushS sO Sym.pos).seq ((halfP K hOA).seq ((pushS sO Sym.sep2).seq ((pushS sO Sym.pos).seq
    ((halfP K hOB).seq (pushS sO Sym.sep)))))

theorem halfP_closed (x : H) : (halfP K x).Closed :=
  ⟨K.pSplit_closed _ _ _, K.pShl2_closed _, moveBlk_closed _ _ _⟩

theorem bodyP_closed : (bodyP K).Closed :=
  ⟨trivial, halfP_closed K _, trivial, trivial, halfP_closed K _, trivial⟩

/-- Cost of one half entry. -/
def chalf (C b u : ℕ) : ℕ :=
  C * (min b (bitLen u) + bitLen b + 1) + (C * (2 + 1) + (3 * bitLen (u % 2 ^ b * 2 ^ 2) + 4))

theorem HT.half {C : ℕ} (hK : K.Spec C) (x : H) (hnd : [x, sB, sT].Nodup) (hxO : x ≠ sO)
    (B : H → List Sym) (u b : ℕ) (rx rb : List Sym) (hrx : TermOK rx) (hrb : TermOK rb)
    (hrt : TermOK (B sT)) (hBx : B x = natSyms u ++ rx) (hBb : B sB = natSyms b ++ rb) :
    HT [] B (halfP K x)
      (Function.update (Function.update B x (natSyms (u / 2 ^ b) ++ rx)) sO
        ((natSyms (u % 2 ^ b * 2 ^ 2)).reverse ++ B sO)) (chalf C b u) := by
  have hxT : x ≠ sT := by
    intro h
    rw [h] at hnd
    simp at hnd
  have h1 := HT.splitAt hK.split Kit.dflt K.lSplit x sB sT hnd (by decide) B u b rx rb hrx hrb hBx
    hBb []
  have h2 := HT.shlConst hK.shl2 Kit.dflt K.lShl2 sT (by decide)
    (Function.update (Function.update B x (natSyms (u / 2 ^ b) ++ rx)) sT
      (natSyms (u % 2 ^ b) ++ B sT)) (u % 2 ^ b) (B sT) hrt (Function.update_self _ _ _) []
  have h3 := HT.moveBlk K.lS (show sT ≠ sO by decide)
    (Function.update (Function.update (Function.update B x (natSyms (u / 2 ^ b) ++ rx)) sT
      (natSyms (u % 2 ^ b) ++ B sT)) sT (natSyms (u % 2 ^ b * 2 ^ 2) ++ B sT))
    (encodeNat (u % 2 ^ b * 2 ^ 2)) (B sT) hrt (Function.update_self _ _ _)
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ le_rfl
  rw [rev_natSyms]
  funext k
  by_cases e1 : k = sO
  · subst e1
    simp [Ne.symm hxO]
  · by_cases e2 : k = sT
    · subst e2
      simp [Function.update_apply, Ne.symm hxT]
    · simp [Function.update_apply, e1, e2]

/-! ## Record-level rules -/

theorem HT.pushO (σ : H → List Sym) (w : W) (x : Sym) :
    HT [] (w.toB σ) (pushS (σ := K.Reg) sO x) ({ w with xo := x :: w.xo }.toB σ) 1 :=
  (HT.pushS sO x (w.toB σ) []).of_eq (by rw [toB_sO, upd_sO]) le_rfl

theorem HT.halfA {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (w : W) (u b : ℕ)
    (rx rb : List Sym) (hrx : TermOK rx) (hrb : TermOK rb) (hrt : TermOK w.xt)
    (hoa : w.oa = natSyms u ++ rx) (hxb : w.xb = natSyms b ++ rb) :
    HT [] (w.toB σ) (halfP K hOA)
      ({ w with
          oa := natSyms (u / 2 ^ b) ++ rx,
          xo := (natSyms (u % 2 ^ b * 2 ^ 2)).reverse ++ w.xo }.toB σ) (chalf C b u) :=
  (HT.half K hK hOA (by decide) (by decide) (w.toB σ) u b rx rb hrx hrb (by simpa using hrt)
    (by simpa using hoa) (by simpa using hxb)).of_eq (by rw [toB_sO, upd_OA, upd_sO]) le_rfl

theorem HT.halfB {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (w : W) (u b : ℕ)
    (rx rb : List Sym) (hrx : TermOK rx) (hrb : TermOK rb) (hrt : TermOK w.xt)
    (hob : w.ob = natSyms u ++ rx) (hxb : w.xb = natSyms b ++ rb) :
    HT [] (w.toB σ) (halfP K hOB)
      ({ w with
          ob := natSyms (u / 2 ^ b) ++ rx,
          xo := (natSyms (u % 2 ^ b * 2 ^ 2)).reverse ++ w.xo }.toB σ) (chalf C b u) :=
  (HT.half K hK hOB (by decide) (by decide) (w.toB σ) u b rx rb hrx hrb (by simpa using hrt)
    (by simpa using hob) (by simpa using hxb)).of_eq (by rw [toB_sO, upd_OB, upd_sO]) le_rfl

/-- Cost bound of one iteration. -/
def cbody (C b : ℕ) : ℕ := 2 * (C * (2 * b + 1) + C * (2 + 1) + (3 * (b + 2) + 4)) + 4

theorem chalf_le (C b u : ℕ) : chalf C b u ≤ C * (2 * b + 1) + C * (2 + 1) + (3 * (b + 2) + 4) := by
  have h1 : C * (min b (bitLen u) + bitLen b + 1) ≤ C * (2 * b + 1) :=
    Nat.mul_le_mul_left C (by have := bitLen_le_self b; have := Nat.min_le_left b (bitLen u); omega)
  have h2 : bitLen (u % 2 ^ b * 2 ^ 2) ≤ b + 2 :=
    le_trans (bitLen_mul_two_pow_le _ 2)
      (by have := bitLen_le_of_lt (Nat.mod_lt u (Nat.two_pow_pos b)); omega)
  unfold chalf
  omega

/-- **One iteration.** -/
theorem HT.body {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (w : W) (b uA uB : ℕ)
    (rA rB rb : List Sym) (hrA : TermOK rA) (hrB : TermOK rB) (hrb : TermOK rb)
    (hrt : TermOK w.xt) (hoa : w.oa = natSyms uA ++ rA) (hob : w.ob = natSyms uB ++ rB)
    (hxb : w.xb = natSyms b ++ rb) :
    HT [] (w.toB σ) (bodyP K)
      ({ w with
          oa := natSyms (uA / 2 ^ b) ++ rA,
          ob := natSyms (uB / 2 ^ b) ++ rB,
          xo := Sym.sep :: ((natSyms (uB % 2 ^ b * 2 ^ 2)).reverse ++ Sym.pos :: Sym.sep2 ::
            ((natSyms (uA % 2 ^ b * 2 ^ 2)).reverse ++ Sym.pos :: w.xo)) }.toB σ)
      (cbody C b) := by
  refine (HT.seq (HT.pushO K σ w Sym.pos)
    (HT.seq (HT.halfA K hK σ _ uA b rA rb hrA hrb hrt hoa hxb)
    (HT.seq (HT.pushO K σ _ Sym.sep2)
    (HT.seq (HT.pushO K σ _ Sym.pos)
    (HT.seq (HT.halfB K hK σ _ uB b rB rb hrB hrb hrt hob hxb)
      (HT.pushO K σ _ Sym.sep)))))).mono ?_
  have hA := chalf_le C b uA
  have hB := chalf_le C b uB
  unfold cbody
  omega

#assert_std_axioms halfP_closed bodyP_closed HT.half HT.pushO HT.halfA HT.halfB chalf_le HT.body

end WP.W9sp
