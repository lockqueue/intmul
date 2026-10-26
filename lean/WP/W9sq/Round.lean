import WP.W9sq.Arith
import WP.W9sq.Ops

/-!
# WP.W9sq.Round — rounding a signed number by its sign

`roundP … src dst kQ kH kH1` (generic host): pop the sign of `w` from `src`; on `neg` add `H - 1`
(from `kH1`), on `pos` add `H` (from `kH`), into `dst` (`addNat`); shift `dst` right by the counter
`q` on `kQ` (`shrVar`); attach the branch's compile-time sign (`attachSign`); drop `|w|` from
`src` (`dropNat`). Result: `dst += intSyms (rnd bneg bpos H q w)` (`HT.roundP`), which is
`divRoundPow2 w q` for `(bneg, bpos) = (true, false)` and `-divRoundPow2 w q` for
`(false, true)` when `H = 2^(q-1)` (`rnd_re`, `rnd_im`).
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

variable {a b : ℕ} {σ : Type}

/-- Round the signed number on `src` into `dst` (see the module doc). -/
def roundP (lS : Lens σ (Option Sym)) (Ian : Inst 3 4 Unit) (lan : Lens σ Ian.R)
    (Isr : Inst 2 4 Unit) (lsr : Lens σ Isr.R) (Ineg Ipos : Inst 1 4 Unit) (lneg : Lens σ Ineg.R)
    (lpos : Lens σ Ipos.R) (Idr : Inst 1 4 Unit) (ldr : Lens σ Idr.R)
    (dflt src dst kQ kH kH1 : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  ((popR' lS src).seq (.ite (fun v => decide (lS.get v = some Sym.neg))
    ((callI Ian [src, kH1, dst] dflt lan).seq
      ((callI Isr [dst, kQ] dflt lsr).seq (callI Ineg [dst] dflt lneg)))
    ((callI Ian [src, kH, dst] dflt lan).seq
      ((callI Isr [dst, kQ] dflt lsr).seq (callI Ipos [dst] dflt lpos))))).seq
  (callI Idr [src] dflt ldr)

theorem roundP_closed (lS : Lens σ (Option Sym)) (Ian : Inst 3 4 Unit) (lan : Lens σ Ian.R)
    (Isr : Inst 2 4 Unit) (lsr : Lens σ Isr.R) (Ineg Ipos : Inst 1 4 Unit) (lneg : Lens σ Ineg.R)
    (lpos : Lens σ Ipos.R) (Idr : Inst 1 4 Unit) (ldr : Lens σ Idr.R)
    (dflt src dst kQ kH kH1 : Loc a b) :
    (roundP lS Ian lan Isr lsr Ineg Ipos lneg lpos Idr ldr dflt src dst kQ kH kH1).Closed :=
  ⟨⟨trivial, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩, callI_closed _ _ _ _⟩

theorem sgn_neg_iff (w : ℤ) : decide (some (sgnSym w) = some Sym.neg) = true ↔ w < 0 := by
  unfold sgnSym
  by_cases h : w < 0 <;> simp [h]

theorem HT.roundP (lS : Lens σ (Option Sym)) {Ian : Inst 3 4 Unit} {Isr : Inst 2 4 Unit}
    {Ineg Ipos Idr : Inst 1 4 Unit} {bneg bpos : Bool} {C : ℕ}
    (hAn : SpecAddNat Ian C) (hSr : SpecShrVar Isr C) (hNg : SpecAttach bneg Ineg C)
    (hPs : SpecAttach bpos Ipos C) (hDr : SpecDrop Idr C)
    (lan : Lens σ Ian.R) (lsr : Lens σ Isr.R) (lneg : Lens σ Ineg.R) (lpos : Lens σ Ipos.R)
    (ldr : Lens σ Idr.R) (dflt : Loc a b) {src dst kQ kH kH1 : Loc a b}
    (hsd : src ≠ dst) (hsQ : src ≠ kQ) (hsH : src ≠ kH) (hsH1 : src ≠ kH1)
    (hdQ : dst ≠ kQ) (hdH : dst ≠ kH) (hdH1 : dst ≠ kH1) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (w : ℤ) (rs : List Sym) (hrs : TermOK rs)
    (hsrc : B src = intSyms w ++ rs) (hdst : TermOK (B dst))
    (q H : ℕ) (rQ rH rH1 : List Sym) (hrQ : TermOK rQ) (hrH : TermOK rH) (hrH1 : TermOK rH1)
    (hQ : B kQ = natSyms q ++ rQ) (hH : B kH = natSyms H ++ rH)
    (hH1 : B kH1 = natSyms (H - 1) ++ rH1) :
    HT [] B (roundP lS Ian lan Isr lsr Ineg Ipos lneg lpos Idr ldr dflt src dst kQ kH kH1)
      (Function.update (Function.update B src rs) dst (intSyms (rnd bneg bpos H q w) ++ B dst))
      (C * (bitLen w.natAbs + bitLen H + 1) + C * (q + bitLen q + 1) +
        C * (bitLen w.natAbs + 1) + C + 2) := by
  have hB0s : Function.update B src (natSyms w.natAbs ++ rs) src = natSyms w.natAbs ++ rs := by
    simp
  have hB0d : Function.update B src (natSyms w.natAbs ++ rs) dst = B dst := by
    simp [Function.update_of_ne (Ne.symm hsd)]
  have hB0Q : Function.update B src (natSyms w.natAbs ++ rs) kQ = natSyms q ++ rQ := by
    simp [Function.update_of_ne (Ne.symm hsQ), hQ]
  have hB0H : Function.update B src (natSyms w.natAbs ++ rs) kH = natSyms H ++ rH := by
    simp [Function.update_of_ne (Ne.symm hsH), hH]
  have hB0H1 : Function.update B src (natSyms w.natAbs ++ rs) kH1 = natSyms (H - 1) ++ rH1 := by
    simp [Function.update_of_ne (Ne.symm hsH1), hH1]
  have hHp := bitLen_pred_le H
  refine (HT.seq (HT.popBranch lS src B
    (Function.update (Function.update B src (natSyms w.natAbs ++ rs)) dst
      (intSyms (rnd bneg bpos H q w) ++ B dst))
    (sgnSym w) (natSyms w.natAbs ++ rs) (by rw [hsrc]; rfl)
    (fun o => decide (o = some Sym.neg)) _ _
    (T₁ := C * (bitLen w.natAbs + bitLen H + 1) + C * (q + bitLen q + 1) + C)
    (T₂ := C * (bitLen w.natAbs + bitLen H + 1) + C * (q + bitLen q + 1) + C) [] ?_ ?_)
    (HT.dropNat hDr dflt ldr src (by omega) _ w.natAbs rs hrs ?_ [])).of_eq ?_ ?_
  · intro hneg
    have hw : w < 0 := (sgn_neg_iff w).mp hneg
    refine (HT.seq (HT.addNat hAn dflt lan src kH1 dst (by simp [hsH1, hsd, Ne.symm hdH1])
      (by omega) _ w.natAbs (H - 1) rs rH1 hrs hrH1 hB0s hB0H1 []) <|
      HT.seq (HT.shrVar hSr dflt lsr dst kQ (by simp [hdQ]) (by omega) _ (w.natAbs + (H - 1)) q
        (B dst) rQ hdst hrQ ?_ ?_ []) <|
      HT.attach hNg dflt lneg dst (by omega) _ ((w.natAbs + (H - 1)) / 2 ^ q) (B dst) hdst ?_
        []).of_eq ?_ ?_
    · simp [hB0d]
    · simp [Function.update_of_ne (Ne.symm hdQ), hB0Q]
    · simp
    · rw [Function.update_idem, Function.update_idem]
      congr 2
      unfold rnd
      rw [if_pos hw]
    · have h1 : C * (bitLen w.natAbs + bitLen (H - 1) + 1) ≤ C * (bitLen w.natAbs + bitLen H + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : C * (min q (bitLen (w.natAbs + (H - 1))) + bitLen q + 1) ≤ C * (q + bitLen q + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · intro hpos
    have hw : ¬ w < 0 := fun h => by
      have h1 : decide (some (sgnSym w) = some Sym.neg) = true := (sgn_neg_iff w).mpr h
      have h2 : decide (some (sgnSym w) = some Sym.neg) = false := hpos
      rw [h1] at h2
      exact absurd h2 (by decide)
    refine (HT.seq (HT.addNat hAn dflt lan src kH dst (by simp [hsH, hsd, Ne.symm hdH])
      (by omega) _ w.natAbs H rs rH hrs hrH hB0s hB0H []) <|
      HT.seq (HT.shrVar hSr dflt lsr dst kQ (by simp [hdQ]) (by omega) _ (w.natAbs + H) q
        (B dst) rQ hdst hrQ ?_ ?_ []) <|
      HT.attach hPs dflt lpos dst (by omega) _ ((w.natAbs + H) / 2 ^ q) (B dst) hdst ?_
        []).of_eq ?_ ?_
    · simp [hB0d]
    · simp [Function.update_of_ne (Ne.symm hdQ), hB0Q]
    · simp
    · rw [Function.update_idem, Function.update_idem]
      congr 2
      unfold rnd
      rw [if_neg hw]
    · have h2 : C * (min q (bitLen (w.natAbs + H)) + bitLen q + 1) ≤ C * (q + bitLen q + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · simp [Function.update_of_ne hsd]
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · omega

#assert_std_axioms roundP_closed sgn_neg_iff HT.roundP

end WP.W9sq
