/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractRecCDefs

/-!
# Lemma A.9 extraction, part 6b: one record, the run lemma (`Machine/AppC/C7ExtractRecC.lean`)

`runs_recBody`: the body of the main loop of the extraction kernel for the record with index `n`
(counter `n + 1` on `cM`), with the definitions of `C7ExtractRecCDefs.lean`. An exceptional record
gets a hole `tag 8` in the skeleton stream and its keyed record on the bank (key = the `A`-bit
destination `c7Dest … n`, computed by the triple sub-kernel `TriSpec` and Horner's rule); a kept
record is moved to the skeleton stream; every work stack is restored. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Everything here is proved (no `sorry`); the triple sub-kernel enters as the hypothesis
`TriSpec xk tri C K ρ f`.
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.Corr SubNLogN.Machine.AppC.C7RadixAux SubNLogN.Math.Networks
  SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.C7RepairAux.Math

section Rec

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

set_option maxHeartbeats 20000000 in
/-- **One record** (index `n`, counter `n + 1` on `cM`). From the buffer `T` (the reversed record
`pl` on top), an exceptional record (`badB`) puts `tag 8` on `H` and its keyed record on `Bk`; a
kept record goes to `H`; every work stack is restored. -/
theorem runs_recBody (σ : Equiv.Perm (Fin 3)) (tri : Prog (XK E') (fun _ => Sym) xk.R)
    (Ct K ρ f N1 N2 N3 A nb n : ℕ) (pl : List Bool) (X ct : List Sym) (S : XK E' → List Sym)
    (htri : TriSpec xk tri Ct K ρ f)
    (hK6 : 6 ≤ K) (hρK : ρ < K) (hf1 : 1 ≤ f) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3)
    (hLnb : f * K + 1 ≤ nb) (hN1b : N1 < 2 ^ nb) (hN2b : N2 < 2 ^ nb) (hN3b : N3 < 2 ^ nb)
    (hn : n + 1 < 2 ^ nb) (hd : c7Dest K ρ f N1 N2 N3 σ n < 2 ^ A)
    (hA : 2 ^ A + 2 ^ A ≤ 2 ^ nb)
    (cK : NumAt S sK K) (cρ : NumAt S sRho ρ) (cf : NumAt S sF f) (cN1 : NumAt S sN1 N1)
    (cN2 : NumAt S sN2 N2) (cN3 : NumAt S sN3 N3) (cL : NumAt S (wk .cL) (f * K))
    (c2L : NumAt S (wk .c2L) (2 ^ (f * K))) (c2K : NumAt S (wk .c2K) (2 ^ K))
    (c2K1 : NumAt S (wk .c2K1) (2 ^ (K - 1))) (c2r : NumAt S (wk .c2r) (2 ^ ρ))
    (c2r1 : NumAt S (wk .c2r1) (2 ^ (ρ + 1))) (cF1 : NumAt S (wk .cF1) (f - 1))
    (c10 : NumAt S (wk .c10) 10) (c11 : NumAt S (wk .c11) 11) (k1 : NumAt S (wk .c1) 1)
    (c2A : NumAt S (wk .c2A) (2 ^ A))
    (hct : TermOK ct) (hcM : S (wk .cM) = natSyms (n + 1) ++ ct)
    (hT : S (wk .T) = Sym.sep :: ((pl.map Sym.bit).reverse ++ X)) (hX : ∃ Y, X = Sym.sep :: Y) :
    Runs (recBody xk σ tri) S
      (Function.update (Function.update (Function.update S (wk .T) X) sH
        ((if badB K ρ f N1 N2 N3 σ n then [Sym.tag 8] else SubNLogN.Machine.recSyms pl) ++ S sH))
        sB ((if badB K ρ f N1 N2 N3 σ n then
          keyedSyms (bitsLE A (c7Dest K ρ f N1 N2 N3 σ n), pl) else []) ++ S sB))
      (fun _ => True) (recCost xk nb f (f * K) Ct pl.length A) := by
  obtain ⟨Y, rfl⟩ := hX
  obtain ⟨rK, hrK, hK⟩ := cK
  obtain ⟨rρ, hrρ, hρ⟩ := cρ
  obtain ⟨rf, hrf, hf⟩ := cf
  obtain ⟨rN1, hrN1, hN1'⟩ := cN1
  obtain ⟨rN2, hrN2, hN2'⟩ := cN2
  obtain ⟨rN3, hrN3, hN3'⟩ := cN3
  obtain ⟨rL, hrL, hL⟩ := cL
  obtain ⟨r2L, hr2L, h2L⟩ := c2L
  obtain ⟨r2K, hr2K, h2K⟩ := c2K
  obtain ⟨r2K1, hr2K1, h2K1⟩ := c2K1
  obtain ⟨r2r, hr2r, h2r⟩ := c2r
  obtain ⟨r2r1, hr2r1, h2r1⟩ := c2r1
  obtain ⟨rF1, hrF1, hF1⟩ := cF1
  obtain ⟨r10, hr10, h10⟩ := c10
  obtain ⟨r11, hr11, h11⟩ := c11
  obtain ⟨r1, hr1, h1⟩ := k1
  obtain ⟨r2A, hr2A, h2A⟩ := c2A
  have hQ0 : 0 < 2 ^ (f * K) := Nat.two_pow_pos _
  have hQnb : 2 ^ (f * K) < 2 ^ nb := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have bQ : bitLen (2 ^ (f * K)) ≤ nb := TMFw.W3s.bitLen_le_of_lt hQnb
  have bN1 : bitLen N1 ≤ nb := TMFw.W3s.bitLen_le_of_lt hN1b
  have bN2 : bitLen N2 ≤ nb := TMFw.W3s.bitLen_le_of_lt hN2b
  have bN3 : bitLen N3 ≤ nb := TMFw.W3s.bitLen_le_of_lt hN3b
  have bn1 : bitLen (n + 1) ≤ nb := TMFw.W3s.bitLen_le_of_lt hn
  have bn : bitLen n ≤ nb := TMFw.W3s.bitLen_le_of_lt (by omega)
  have hKL : K ≤ f * K := Nat.le_mul_of_pos_left K hf1
  have b1 : bitLen 1 ≤ nb := by
    rw [show bitLen 1 = 1 from rfl]
    omega
  have b2r1 : bitLen (2 ^ (ρ + 1)) ≤ nb :=
    TMFw.W3s.bitLen_le_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have bF1 : bitLen (f - 1) ≤ nb := TMFw.W3s.bitLen_le_of_lt
    (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by
      have : f ≤ f * K := Nat.le_mul_of_pos_right f (by omega)
      omega)))
  have hflag : (false || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1) || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (f - 1)) = badB K ρ f N1 N2 N3 σ n := by
    rw [badB_eq]
    simp [c7Tri]
  have hbox := T_inBox K ρ f (by omega) hρK hf1 (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n)
    ⟨c7Slot_lt _ _ _ _ _ n, c7Slot_lt _ _ _ _ _ n, c7Slot_lt _ _ _ _ _ n⟩
  have hdest : c7Rank (f * K) N1 N2 N3 (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (n / N3 / 2 ^ (f * K) % N2) (n % N3)
      (fun j => nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ j)) = c7Dest K ρ f N1 N2 N3 σ n := by
    rw [dest_eq K ρ f N1 N2 N3 σ n (by omega) (by omega) (by omega)]
    rfl
  have hdestH : (((((((n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 0)) * N1 + n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 1)) * N2 + n / N3 / 2 ^ (f * K) % N2) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 2)) * N3 + n % N3) = c7Dest K ρ f N1 N2 N3 σ n := hdest
  have hfin : (((((((n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 0)) * N1 + n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 1)) * N2 + n / N3 / 2 ^ (f * K) % N2) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 2)) * N3 + n % N3) + 2 ^ A < 2 ^ nb := by
    have e : c7Rank (f * K) N1 N2 N3 (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (n / N3 / 2 ^ (f * K) % N2) (n % N3)
      (fun j => nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ j)) = (((((((n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 0)) * N1 + n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 1)) * N2 + n / N3 / 2 ^ (f * K) % N2) * 2 ^ (f * K) + nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) (σ 2)) * N3 + n % N3) := rfl
    rw [← e, hdest]
    omega
  by_cases hb : badB K ρ f N1 N2 N3 σ n = true
  · have hyz : anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1) = true ∨ anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (f - 1) = true := by
      have h := hb
      rw [badB_eq] at h
      simpa [c7Tri] using h
    have X := WP.W9comp.runs_seq (WP.W9comp.runs_seq (runs_pushW xk (wk .tP) .mark S)
        (WP.W9comp.runs_seq (runs_copyW xk (src := wk .cM) (dst := wk .tP) (tmp := wk .u1) (by simp) (by simp) (by simp) (n + 1) ct _ hct (by simp [Function.update_apply, hcM]))
        (WP.W9comp.runs_seq (runs_subFrom xk (k := wk .tP) (b := wk .c1) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) (n + 1) 1 nb (Sym.mark :: S (wk .tP)) r1 _ (termOK_mark _) hr1 (by omega) (by simp [Function.update_apply]) (by simp [Function.update_apply, h1]) bn1 b1)
        (WP.W9comp.runs_seq (runs_decode xk n N1 N2 N3 (2 ^ (f * K)) nb _ (Sym.mark :: S (wk .tP)) rN1 rN2 rN3 r2L (termOK_mark _) hrN1 hrN2 hrN3 hr2L (by simp [Function.update_apply]) (by simp [Function.update_apply, hN1']) (by simp [Function.update_apply, hN2']) (by simp [Function.update_apply, hN3']) (by simp [Function.update_apply, h2L]) (by omega) (by omega) (by omega) hQ0 bn bN1 bN2 bN3 bQ)
        (WP.W9comp.runs_seq (runs_names xk σ (fun j => c7Slot (f * K) N1 N2 N3 j n) nb _ (fun j => Sym.mark :: S (wk (slotW j))) (fun _ => termOK_mark _) (by intro j; fin_cases j <;> simp [slotW, Function.update_apply, slot0_eq, slot1_eq, slot2_eq]) (fun j => TMFw.W3s.bitLen_le_of_lt (lt_trans (c7Slot_lt _ _ _ _ j n) hQnb)))
        (WP.W9comp.runs_seq (runs_pushW xk (wk .fG) (.bit false) _)
        (WP.W9comp.runs_seq (runs_guardV xk (v := wk .nY) (by simp) (by simp) nb K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) false _ (Sym.mark :: S (wk .nY)) (S (wk .fG)) r2r1 rF1 r2K1 r10 r11 r2K (termOK_mark _) hr2r1 hrF1 hr2K1 hr10 hr11 hr2K (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply, h2r1]) (by simp [Function.update_apply, hF1]) (by simp [Function.update_apply, h2K1]) (by simp [Function.update_apply, h10]) (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h2K]) (lt_trans (c7Slot_lt _ _ _ _ _ n) hQnb) hK6 (by omega) b2r1 bF1)
        (runs_guardV xk (v := wk .nZ) (by simp) (by simp) nb K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (false || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1)) _ (Sym.mark :: S (wk .nZ)) (S (wk .fG)) r2r1 rF1 r2K1 r10 r11 r2K (termOK_mark _) hr2r1 hrF1 hr2K1 hr10 hr11 hr2K (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply, h2r1]) (by simp [Function.update_apply, hF1]) (by simp [Function.update_apply, h2K1]) (by simp [Function.update_apply, h10]) (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h2K]) (lt_trans (c7Slot_lt _ _ _ _ _ n) hQnb) hK6 (by omega) b2r1 bF1))))))))
      (WP.W9comp.runs_seq (RunsIn.iff_runs.mp (RunsIn.ite_true (Pf := goodBr xk) (c := fun v => decide (xk.lw.get v = some (Sym.bit true))) (RunsIn.mono (runsIn_peekW xk (wk .fG) _) (fun v hv => by rw [hv]; simpa [Function.update_apply] using hyz) le_rfl) (RunsIn.iff_runs.mpr (WP.W9comp.runs_seq (runs_pushW xk sH (.tag 8) _)
          (WP.W9comp.runs_seq (htri (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n) (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (Sym.mark :: S (wk .nX)) (Sym.mark :: S (wk .nY)) (Sym.mark :: S (wk .nZ)) _ (c7Slot_lt _ _ _ _ _ n) (c7Slot_lt _ _ _ _ _ n) (c7Slot_lt _ _ _ _ _ n) (termOK_mark _) (termOK_mark _) (termOK_mark _) (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply]) ⟨rK, hrK, by simp [Function.update_apply, hK]⟩ ⟨rρ, hrρ, by simp [Function.update_apply, hρ]⟩ ⟨rf, hrf, by simp [Function.update_apply, hf]⟩ ⟨rL, hrL, by simp [Function.update_apply, hL]⟩ ⟨r2L, hr2L, by simp [Function.update_apply, h2L]⟩ ⟨r2K, hr2K, by simp [Function.update_apply, h2K]⟩ ⟨r2r, hr2r, by simp [Function.update_apply, h2r]⟩ ⟨rF1, hrF1, by simp [Function.update_apply, hF1]⟩)
          (WP.W9comp.runs_seq (runs_horner xk σ (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (n / N3 / 2 ^ (f * K) % N2) (n % N3) N1 N2 N3 (2 ^ (f * K)) (2 ^ A) nb (fun i => nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))) i) _ (Sym.mark :: S (wk .vA0)) (Sym.mark :: S (wk .vA1)) (Sym.mark :: S (wk .vA2)) (Sym.mark :: S (wk .vA3)) rN1 rN2 rN3 r2L r2A (fun j => Sym.mark :: S (wk (nameW j))) (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _) hrN1 hrN2 hrN3 hr2L hr2A (fun _ => termOK_mark _) (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply, hN1']) (by simp [Function.update_apply, hN2']) (by simp [Function.update_apply, hN3']) (by simp [Function.update_apply, h2L]) (by simp [Function.update_apply, h2A]) (by intro j; fin_cases j <;> simp [nameW, nameGet, Function.update_apply]) hN1 hN2 hN3 (Nat.one_le_two_pow) hfin bN1 bN2 bN3 bQ)
          (WP.W9comp.runs_seq (runs_keyEmit xk A (c7Dest K ρ f N1 N2 N3 σ n) hd pl Y (S (wk .hD)) _ (by simp [Function.update_apply, hT]) (by rw [← hdestH]; simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .nX) ((packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))).1) .mark (S (wk .nX)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .nY) ((packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))).2.1) .mark (S (wk .nY)) _ rfl (by simp [Function.update_apply]))
          (runs_dropFW xk (wk .nZ) ((packedT0 K ρ f (packedS0inv (f * K) K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n, c7Slot (f * K) N1 N2 N3 (σ.symm 1) n, c7Slot (f * K) N1 N2 N3 (σ.symm 2) n))).2.2) .mark (S (wk .nZ)) _ rfl (by simp [Function.update_apply])))))))))))
        (WP.W9comp.runs_seq (runs_popW_cons xk (wk .fG) _ (Sym.bit (false || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1) || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (f - 1))) (S (wk .fG)) (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC1) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 % 2 ^ (f * K)) .mark (S (wk .vC1)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC2) (n / N3 / 2 ^ (f * K) / N2 % 2 ^ (f * K)) .mark (S (wk .vC2)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC3) (n / N3 % 2 ^ (f * K)) .mark (S (wk .vC3)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA0) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) .mark (S (wk .vA0)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA1) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) .mark (S (wk .vA1)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA2) (n / N3 / 2 ^ (f * K) % N2) .mark (S (wk .vA2)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA3) (n % N3) .mark (S (wk .vA3)) _ rfl (by simp [Function.update_apply]))
          (runs_dropFW xk (wk .tP) n .mark (S (wk .tP)) _ rfl (by simp [Function.update_apply])))))))))))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
    · funext k
      rcases k with (k | k) | (x | e)
      · simp [Function.update_apply]
      · fin_cases k <;> simp [Function.update_apply, hb]
      · cases x <;> simp [Function.update_apply]
      · simp [Function.update_apply]
    · unfold recCost
      have dl : ∀ v, v ≤ n → 2 * bitLen v + 2 ≤ opCost xk nb := fun v hv => drop_le xk nb v (by omega)
      have dQ : ∀ v, v < 2 ^ (f * K) → 2 * bitLen v + 2 ≤ opCost xk nb :=
        fun v hv => drop_le xk nb v (lt_trans hv hQnb)
      have cp := small_le xk nb (bitLen (n + 1)) 0 bn1 (by omega)
      have e1 := dQ _ (Nat.mod_lt (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1) hQ0)
      have e2 := dQ _ (Nat.mod_lt (n / N3 / 2 ^ (f * K) / N2) hQ0)
      have e3 := dQ _ (Nat.mod_lt (n / N3) hQ0)
      have e4 := dl (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) (le_trans
        (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _)
        (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))))))
      have e5 := dl (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (le_trans (Nat.mod_le _ _)
        (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (le_trans
        (Nat.div_le_self _ _) (Nat.div_le_self _ _)))))
      have e6 := dl (n / N3 / 2 ^ (f * K) % N2) (le_trans (Nat.mod_le _ _)
        (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
      have e7 := dl (n % N3) (Nat.mod_le _ _)
      have e8 := dl n le_rfl
      have e9 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 0) n)
      have e10 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 1) n)
      have e11 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 2) n)
      have e12 := dQ _ hbox.1
      have e13 := dQ _ hbox.2.1
      have e14 := dQ _ hbox.2.2
      omega
  · have hb' : badB K ρ f N1 N2 N3 σ n = false := by simpa using hb
    have hyz : anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1) = false ∧ anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (f - 1) = false := by
      have h := hb'
      rw [badB_eq] at h
      simpa [c7Tri] using h
    have X := WP.W9comp.runs_seq (WP.W9comp.runs_seq (runs_pushW xk (wk .tP) .mark S)
        (WP.W9comp.runs_seq (runs_copyW xk (src := wk .cM) (dst := wk .tP) (tmp := wk .u1) (by simp) (by simp) (by simp) (n + 1) ct _ hct (by simp [Function.update_apply, hcM]))
        (WP.W9comp.runs_seq (runs_subFrom xk (k := wk .tP) (b := wk .c1) (t := wk .iT) (t1 := wk .u1) (t2 := wk .u2) (t3 := wk .u3) (by simp) (n + 1) 1 nb (Sym.mark :: S (wk .tP)) r1 _ (termOK_mark _) hr1 (by omega) (by simp [Function.update_apply]) (by simp [Function.update_apply, h1]) bn1 b1)
        (WP.W9comp.runs_seq (runs_decode xk n N1 N2 N3 (2 ^ (f * K)) nb _ (Sym.mark :: S (wk .tP)) rN1 rN2 rN3 r2L (termOK_mark _) hrN1 hrN2 hrN3 hr2L (by simp [Function.update_apply]) (by simp [Function.update_apply, hN1']) (by simp [Function.update_apply, hN2']) (by simp [Function.update_apply, hN3']) (by simp [Function.update_apply, h2L]) (by omega) (by omega) (by omega) hQ0 bn bN1 bN2 bN3 bQ)
        (WP.W9comp.runs_seq (runs_names xk σ (fun j => c7Slot (f * K) N1 N2 N3 j n) nb _ (fun j => Sym.mark :: S (wk (slotW j))) (fun _ => termOK_mark _) (by intro j; fin_cases j <;> simp [slotW, Function.update_apply, slot0_eq, slot1_eq, slot2_eq]) (fun j => TMFw.W3s.bitLen_le_of_lt (lt_trans (c7Slot_lt _ _ _ _ j n) hQnb)))
        (WP.W9comp.runs_seq (runs_pushW xk (wk .fG) (.bit false) _)
        (WP.W9comp.runs_seq (runs_guardV xk (v := wk .nY) (by simp) (by simp) nb K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) false _ (Sym.mark :: S (wk .nY)) (S (wk .fG)) r2r1 rF1 r2K1 r10 r11 r2K (termOK_mark _) hr2r1 hrF1 hr2K1 hr10 hr11 hr2K (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply, h2r1]) (by simp [Function.update_apply, hF1]) (by simp [Function.update_apply, h2K1]) (by simp [Function.update_apply, h10]) (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h2K]) (lt_trans (c7Slot_lt _ _ _ _ _ n) hQnb) hK6 (by omega) b2r1 bF1)
        (runs_guardV xk (v := wk .nZ) (by simp) (by simp) nb K ρ f (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (false || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1)) _ (Sym.mark :: S (wk .nZ)) (S (wk .fG)) r2r1 rF1 r2K1 r10 r11 r2K (termOK_mark _) hr2r1 hrF1 hr2K1 hr10 hr11 hr2K (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply, h2r1]) (by simp [Function.update_apply, hF1]) (by simp [Function.update_apply, h2K1]) (by simp [Function.update_apply, h10]) (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h2K]) (lt_trans (c7Slot_lt _ _ _ _ _ n) hQnb) hK6 (by omega) b2r1 bF1))))))))
      (WP.W9comp.runs_seq (RunsIn.iff_runs.mp (RunsIn.ite_false (Pt := badBr xk σ tri) (c := fun v => decide (xk.lw.get v = some (Sym.bit true))) (RunsIn.mono (runsIn_peekW xk (wk .fG) _) (fun v hv => by rw [hv]; simpa [Function.update_apply] using hyz) le_rfl) (RunsIn.iff_runs.mpr (WP.W9comp.runs_seq (runs_goodMove xk pl Y _ (by simp [Function.update_apply, hT]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .nX) (c7Slot (f * K) N1 N2 N3 (σ.symm 0) n) .mark (S (wk .nX)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .nY) (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) .mark (S (wk .nY)) _ rfl (by simp [Function.update_apply]))
          (runs_dropFW xk (wk .nZ) (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) .mark (S (wk .nZ)) _ rfl (by simp [Function.update_apply]))))))))
        (WP.W9comp.runs_seq (runs_popW_cons xk (wk .fG) _ (Sym.bit (false || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 1) n) (f - 1) || anyBad K ρ (c7Slot (f * K) N1 N2 N3 (σ.symm 2) n) (f - 1))) (S (wk .fG)) (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC1) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 % 2 ^ (f * K)) .mark (S (wk .vC1)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC2) (n / N3 / 2 ^ (f * K) / N2 % 2 ^ (f * K)) .mark (S (wk .vC2)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vC3) (n / N3 % 2 ^ (f * K)) .mark (S (wk .vC3)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA0) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) .mark (S (wk .vA0)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA1) (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) .mark (S (wk .vA1)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA2) (n / N3 / 2 ^ (f * K) % N2) .mark (S (wk .vA2)) _ rfl (by simp [Function.update_apply]))
          (WP.W9comp.runs_seq (runs_dropFW xk (wk .vA3) (n % N3) .mark (S (wk .vA3)) _ rfl (by simp [Function.update_apply]))
          (runs_dropFW xk (wk .tP) n .mark (S (wk .tP)) _ rfl (by simp [Function.update_apply])))))))))))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
    · funext k
      rcases k with (k | k) | (x | e)
      · simp [Function.update_apply]
      · fin_cases k <;> simp [Function.update_apply, hb']
      · cases x <;> simp [Function.update_apply]
      · simp [Function.update_apply]
    · unfold recCost
      have dl : ∀ v, v ≤ n → 2 * bitLen v + 2 ≤ opCost xk nb := fun v hv => drop_le xk nb v (by omega)
      have dQ : ∀ v, v < 2 ^ (f * K) → 2 * bitLen v + 2 ≤ opCost xk nb :=
        fun v hv => drop_le xk nb v (lt_trans hv hQnb)
      have cp := small_le xk nb (bitLen (n + 1)) 0 bn1 (by omega)
      have e1 := dQ _ (Nat.mod_lt (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1) hQ0)
      have e2 := dQ _ (Nat.mod_lt (n / N3 / 2 ^ (f * K) / N2) hQ0)
      have e3 := dQ _ (Nat.mod_lt (n / N3) hQ0)
      have e4 := dl (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K)) (le_trans
        (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _)
        (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))))))
      have e5 := dl (n / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (le_trans (Nat.mod_le _ _)
        (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) (le_trans
        (Nat.div_le_self _ _) (Nat.div_le_self _ _)))))
      have e6 := dl (n / N3 / 2 ^ (f * K) % N2) (le_trans (Nat.mod_le _ _)
        (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)))
      have e7 := dl (n % N3) (Nat.mod_le _ _)
      have e8 := dl n le_rfl
      have e9 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 0) n)
      have e10 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 1) n)
      have e11 := dQ _ (c7Slot_lt (f * K) N1 N2 N3 (σ.symm 2) n)
      have e12 := dQ _ hbox.1
      have e13 := dQ _ hbox.2.1
      have e14 := dQ _ hbox.2.2
      omega

end Rec

end SubNLogN.Machine.AppC.C7ExtractAux
