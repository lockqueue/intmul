import WP.W9fNF.Widths
import WP.W9fNF.Cost

/-!
# WP.W9fNF.Main — the Nyquist finish, assembled

`finish_runs`: for any subroutine kit satisfying `Kit.OK`, `finishProg κ` meets the
`W9f_nyqFinish` specification with constant `24·Cs + 32·Ca + 8·Cn + 32·Cf + 1000`.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

variable {κ : Kit} {Cs Ca Cn Cf : ℕ}

theorem liftM_peek (a : FS) (S : FS → List Sym) (v : κ.Reg) :
    Eval [] (liftM κ (peekR a)) ⟨v, S⟩ ⟨((S a).head?, v.2), S⟩ 1 :=
  liftM_eval (fun r => Eval.peek [] a (fun _ o => o) r S) v

theorem lt_two_pow_self' : ∀ n : ℕ, n < 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have := lt_two_pow_self' n
    rw [pow_succ]
    omega

theorem outList_length : ∀ (D : ℤ × ℤ) (L : List (ℤ × ℤ)), (outList D L).length = L.length
  | _, [] => rfl
  | D, _ :: L => by simp [outList, outList_length _ L]

theorem notEntry_mark (l : List Sym) :
    ∀ s, (Sym.mark :: l).head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg := by
  intro s h
  simp only [List.head?_cons, Option.some.injEq] at h
  subst h
  exact ⟨by decide, by decide⟩

/-- The stacks after all six phases are the contract's final stacks. -/
theorem final_state (S S1 S2 S3 S4 : FS → List Sym) (k' : ℕ) (rZ : List Sym) (Acc D Df : ℤ × ℤ)
    (L outs : List (ℤ × ℤ))
    (h1 : S1 = Function.update (Function.update (Function.update (Function.update (setupSt S k')
      sZ rZ) sT (blkE L ++ Sym.mark :: S sT)) sA1 (intSyms Acc.1 ++ Sym.mark :: S sA1)) sA2
      (intSyms Acc.2 ++ Sym.mark :: S sA2))
    (h2 : S2 = Function.update (Function.update S1 sA1 (intSyms D.1 ++ Sym.mark :: S sA1)) sA2
      (intSyms D.2 ++ Sym.mark :: S sA2))
    (h3 : S3 = Function.update (Function.update (Function.update (Function.update S2 sT
      (Sym.mark :: S sT)) sZ (blkE outs.reverse ++ rZ)) sA1 (intSyms Df.1 ++ Sym.mark :: S sA1))
      sA2 (intSyms Df.2 ++ Sym.mark :: S sA2))
    (h4 : S4 = Function.update (Function.update S3 sZ rZ) sO (blkE outs ++ S sO)) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update S4 sT (S sT)) sA1 (S sA1)) sA2 (S sA2)) sX (S sX)) sKI (S sKI)) sONE
      (S sONE) = Function.update (Function.update S sZ rZ) sO (blkE outs ++ S sO) := by
  subst h1 h2 h3 h4
  funext k
  simp only [setupSt, Function.update_apply]
  split_ifs <;> simp_all

theorem finish_runs (hκ : κ.OK Cs Ca Cn Cf) (H k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ))
    (rZ r2 r3 : List Sym) (S : FS → List Sym) (hsize : Z.size = 2 ^ k) (hk : 1 ≤ k)
    (hW : ArrW (H + 1) Z) (halt : EntryW H alt)
    (hrZ : ∀ s, rZ.head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg) (hr2 : TermOK r2)
    (hZ : S sZ = blkE Z.toList.reverse ++ rZ) (hK : S sK = natSyms k ++ r2)
    (hAL : S sAL = entrySyms alt ++ r3) :
    Runs (finishProg κ) S (Function.update (Function.update S sZ rZ) sO
        (blkE (WP.W9f.nyqOut k alt Z).toList ++ S sO)) (fun _ => True)
      ((24 * Cs + 32 * Ca + 8 * Cn + 32 * Cf + 1000) * (Z.size * (H + k + 1) + (H + 1) ^ 2)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine Runs.of_eval fun v => ?_
  have hlen : Z.toList.length = 2 ^ (k' + 1) := by rw [Array.length_toList, hsize]
  have hent : ∀ z ∈ Z.toList, bitLen z.1.natAbs ≤ H + 1 ∧ bitLen z.2.natAbs ≤ H + 1 :=
    fun z hz => hW z hz
  have hacc := accOK_top H (k' + 1) Z.toList.reverse (by rw [List.length_reverse, hlen])
    (fun z hz => hent z (List.mem_reverse.mp hz))
  obtain ⟨Acc, hAcc⟩ : ∃ A, A = altAcc (0, 0) Z.toList.reverse := ⟨_, rfl⟩
  have hAccW : bitLen Acc.1.natAbs ≤ H + (k' + 1) + 1 ∧ bitLen Acc.2.natAbs ≤ H + (k' + 1) + 1 := by
    have := hacc Z.toList.reverse.length le_rfl
    rwa [List.take_length, ← hAcc] at this
  obtain ⟨dw11, dw12, dw13, dw14, dw15, dw16⟩ := diff_widths H (k' + 1) k' alt.1 Acc.1 halt.1 hAccW.1
  obtain ⟨dw21, dw22, dw23, dw24, dw25, dw26⟩ := diff_widths H (k' + 1) k' alt.2 Acc.2 halt.2 hAccW.2
  obtain ⟨D, hD⟩ : ∃ D : ℤ × ℤ, D = (((alt.1 - Acc.1) >>> k' + 1) >>> 1,
      ((alt.2 - Acc.2) >>> k' + 1) >>> 1) := ⟨_, rfl⟩
  have hDw1 : bitLen D.1.natAbs ≤ H + (k' + 1) + 3 := by rw [hD]; exact dw16
  have hDw2 : bitLen D.2.natAbs ≤ H + (k' + 1) + 3 := by rw [hD]; exact dw26
  have hk'W : bitLen k' ≤ H + (k' + 1) + 3 := (bitLen_le_self k').trans (by omega)
  -- Phase 0: setup
  have e0 := liftM_eval (κ := κ) (fun r => setup_eval k' r2 S hr2 hK r) v
  -- Phase 1: pass 1
  have hS0Z : setupSt S k' sZ = blkE Z.toList.reverse ++ rZ := by simpa [setupSt] using hZ
  have e1a := liftM_peek (κ := κ) sZ (setupSt S k') (some Sym.mark, v.2)
  obtain ⟨w1, t1, e1b, ht1⟩ := loop1_eval hκ (H + (k' + 1) + 1) rZ (Sym.mark :: S sA1)
    (Sym.mark :: S sA2) (Sym.mark :: S sX) hrZ (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (TermOK.cons (by rfl) _) Z.toList.reverse (0, 0) (setupSt S k')
    ((setupSt S k' sZ).head?, (some Sym.mark, v.2).2)
    (fun z hz => by have := hent z (List.mem_reverse.mp hz); omega) hacc hS0Z
    (by simp [setupSt, intSyms_zero]) (by simp [setupSt, intSyms_zero]) (by simp [setupSt])
    (by rw [hS0Z])
  rw [← hAcc, List.reverse_reverse, show setupSt S k' sT = Sym.mark :: S sT by simp [setupSt]]
    at e1b
  obtain ⟨S1, hS1⟩ : ∃ X, X = Function.update (Function.update (Function.update (Function.update
      (setupSt S k') sZ rZ) sT (blkE Z.toList ++ Sym.mark :: S sT)) sA1
      (intSyms Acc.1 ++ Sym.mark :: S sA1)) sA2 (intSyms Acc.2 ++ Sym.mark :: S sA2) := ⟨_, rfl⟩
  rw [← hS1] at e1b
  -- Phase 2: the rounded difference
  obtain ⟨w2, t2, e2, ht2⟩ := diff_eval hκ (H + (k' + 1) + 3) k' alt Acc r3 (Sym.mark :: S sA1)
    (Sym.mark :: S sA2) (Sym.mark :: S sX) (Sym.mark :: S sKI) (Sym.mark :: S sONE) S1
    (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (by rw [hS1]; simpa [setupSt] using hAL) (by rw [hS1]; simp) (by rw [hS1]; simp)
    (by rw [hS1]; simp [setupSt]) (by rw [hS1]; simp [setupSt]) (by rw [hS1]; simp [setupSt])
    dw11 dw12 dw13 dw14 dw15 dw21 dw22 dw23 dw24 dw25 hk'W w1
  obtain ⟨S2, hS2⟩ : ∃ X, X = Function.update (Function.update S1 sA1
      (intSyms D.1 ++ Sym.mark :: S sA1)) sA2 (intSyms D.2 ++ Sym.mark :: S sA2) := ⟨_, rfl⟩
  have hS2' : Function.update (Function.update S1 sA1
      (intSyms (((alt.1 - Acc.1) >>> k' + 1) >>> 1) ++ Sym.mark :: S sA1)) sA2
      (intSyms (((alt.2 - Acc.2) >>> k' + 1) >>> 1) ++ Sym.mark :: S sA2) = S2 := by
    rw [hS2, hD]
  rw [hS2'] at e2
  -- Phase 3: pass 2
  have hS2T : S2 sT = blkE Z.toList ++ Sym.mark :: S sT := by rw [hS2, hS1]; simp
  have e3a := liftM_peek (κ := κ) sT S2 w2
  obtain ⟨w3, t3, e3b, ht3⟩ := loop2_eval hκ (H + (k' + 1) + 3) (Sym.mark :: S sT)
    (Sym.mark :: S sA1) (Sym.mark :: S sA2) (notEntry_mark _) (TermOK.cons (by rfl) _)
    (TermOK.cons (by rfl) _) Z.toList D S2 ((S2 sT).head?, w2.2)
    (fun z hz => by have := hent z hz; omega) hDw1 hDw2 hS2T (by rw [hS2]; simp)
    (by rw [hS2]; simp) (by rw [hS2T])
  rw [show S2 sZ = rZ by rw [hS2, hS1]; simp] at e3b
  obtain ⟨S3, hS3⟩ : ∃ X, X = Function.update (Function.update (Function.update (Function.update
      S2 sT (Sym.mark :: S sT)) sZ (blkE (outList D Z.toList).reverse ++ rZ)) sA1
      (intSyms (dFin Z.toList D).1 ++ Sym.mark :: S sA1)) sA2
      (intSyms (dFin Z.toList D).2 ++ Sym.mark :: S sA2) := ⟨_, rfl⟩
  rw [← hS3] at e3b
  -- Phase 4: pass 3
  obtain ⟨w4, t4, e4, ht4⟩ := pass3_eval (κ := κ) (outList D Z.toList).reverse rZ hrZ S3
    (by rw [hS3]; simp) w3
  rw [List.reverse_reverse, show S3 sO = S sO by
    rw [hS3, hS2, hS1]; simp [setupSt]] at e4
  obtain ⟨S4, hS4⟩ : ∃ X, X = Function.update (Function.update S3 sZ rZ) sO
      (blkE (outList D Z.toList) ++ S sO) := ⟨_, rfl⟩
  rw [← hS4] at e4
  -- Phase 5: cleanup
  have e5 := liftM_eval (κ := κ) (fun r => cleanup_eval S4 (dFin Z.toList D).1
    (dFin Z.toList D).2 k' (S sT) (S sA1) (S sA2) (S sX) (S sKI) (S sONE)
    (by rw [hS4, hS3]; simp) (by rw [hS4, hS3]; simp) (by rw [hS4, hS3]; simp)
    (by rw [hS4, hS3, hS2, hS1]; simp [setupSt]) (by rw [hS4, hS3, hS2, hS1]; simp [setupSt])
    (by rw [hS4, hS3, hS2, hS1]; simp [setupSt]) r) w4
  -- the final stacks
  have hOut : (WP.W9f.nyqOut (k' + 1) alt Z).toList = outList D Z.toList := by
    rw [nyqOut_toList, ← hAcc, hD]
    have r1 := rnd_eq (alt.1 - Acc.1) (k' + 1) (by omega)
    have r2' := rnd_eq (alt.2 - Acc.2) (k' + 1) (by omega)
    simp only [Nat.add_sub_cancel] at r1 r2'
    rw [r1, r2']
  have hfin : Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update S4 sT (S sT)) sA1 (S sA1)) sA2 (S sA2)) sX (S sX)) sKI
      (S sKI)) sONE (S sONE) = Function.update (Function.update S sZ rZ) sO
        (blkE (WP.W9f.nyqOut (k' + 1) alt Z).toList ++ S sO) := by
    rw [hOut]
    exact final_state S S1 S2 S3 S4 k' rZ Acc D (dFin Z.toList D) Z.toList (outList D Z.toList)
      hS1 hS2 hS3 hS4
  refine ⟨_, _, (Eval.seq e0 (Eval.seq (Eval.seq e1a e1b) (Eval.seq e2 (Eval.seq
    (Eval.seq e3a e3b) (Eval.seq e4 e5))))).of_eq (by rw [hfin]) rfl, trivial, ?_⟩
  -- the cost
  have hdF := dFin_natAbs Z.toList D
  have hlenOut : (blkE (outList D Z.toList).reverse).length ≤
      Z.toList.length * (2 * (H + (k' + 1) + 4) + 4) := by
    have hb := blkE_length_le (H + (k' + 1) + 4) (outList D Z.toList).reverse (fun o ho => by
      have hz : ∀ z ∈ Z.toList, z.1.natAbs ≤ 2 ^ (H + 1) ∧ z.2.natAbs ≤ 2 ^ (H + 1) :=
        fun z hz => ⟨(lt_pow_of_bitLen (hent z hz).1).le, (lt_pow_of_bitLen (hent z hz).2).le⟩
      have hd1 := (lt_pow_of_bitLen hDw1).le
      have hd2 := (lt_pow_of_bitLen hDw2).le
      have := outList_natAbs _ _ Z.toList D hz hd1 hd2 o (List.mem_reverse.mp ho)
      have e1 : 2 ^ (H + 1) < 2 ^ (H + (k' + 1) + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have e2 : 2 ^ (H + (k' + 1) + 4) = 2 * 2 ^ (H + (k' + 1) + 3) := by rw [pow_succ]; ring
      constructor
      · exact bitLen_le_of_lt_two_pow (by omega)
      · exact bitLen_le_of_lt_two_pow (by omega))
    rwa [List.length_reverse, outList_length] at hb
  have hkt : k' + 1 ≤ Z.toList.length := by
    rw [hlen]
    exact (lt_two_pow_self' (k' + 1)).le
  have h0 : 11 + (7 * bitLen (k' + 1) + 7) + (6 * zerosLead (encodeNat (k' + 1)) + 8) ≤
      13 * (k' + 1) + 26 := by
    have a1 := bitLen_le_self (k' + 1)
    have a2 := zerosLead_le_length (encodeNat (k' + 1))
    simp only [bitLen] at a1 ⊢
    omega
  have h5 : 3 * bitLen (dFin Z.toList D).1.natAbs + 3 * bitLen (dFin Z.toList D).2.natAbs +
      3 * bitLen k' + 21 ≤ 9 * (H + (k' + 1) + 3) + 22 := by
    rw [hdF.1, hdF.2]
    omega
  rw [List.length_reverse] at ht1
  have hc := finish_cost Cs Ca Cn Cf H (k' + 1) Z.toList.length _ _ _ _ _ _ (by omega) hkt h0
    ht1 ht2 ht3 (ht4.trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right hlenOut 1))) h5
  rw [show Z.size = Z.toList.length from (Array.length_toList).symm]
  refine le_trans (le_of_eq ?_) hc
  ring

#assert_std_axioms liftM_peek lt_two_pow_self' outList_length notEntry_mark final_state finish_runs

end WP.W9fNF
