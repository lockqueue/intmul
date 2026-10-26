import WP.W4f.Phases

/-!
# WP.W4f.Phases2 — setup and cleanup of the lift

* `setup_eval`: marks on `kS, kY, kT, kV`, then a copy of `k` on `kT`; exact cost `7·|k| + 12`.
* `cleanup_eval`: pop the marks of `kS, kT, kV`; drop the high zeros of the MSB-first output `h`
  on `kY` and move it onto `kD`, which receives `encodeNat (bitsVal h)`; `kY` is restored.
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts Computability

variable {K : Type} [DecidableEq K]

theorem setup_eval {kK kS kT kV kY : K} (hKS : kK ≠ kS) (hKT : kK ≠ kT) (hKV : kK ≠ kV)
    (hKY : kK ≠ kY) (hST : kS ≠ kT) (hSV : kS ≠ kV) (hSY : kS ≠ kY) (hTV : kT ≠ kV)
    (hTY : kT ≠ kY) (hVY : kV ≠ kY) (k : ℕ) (r0 : List Sym) (hr0 : TermOK r0) (v : Reg)
    (S : K → List Sym) (hK : S kK = natSyms k ++ r0) :
    ∃ t, t ≤ 7 * bitLen k + 12 ∧ Eval [] (setup kK kS kT kV kY) ⟨v, S⟩
      ⟨((natSyms k ++ Sym.mark :: S kT).head?, v.2),
        Function.update (Function.update (Function.update (Function.update S kS
          (Sym.mark :: S kS)) kY (Sym.mark :: S kY)) kT (natSyms k ++ Sym.mark :: S kT)) kV
          (Sym.mark :: S kV)⟩ t := by
  obtain ⟨Q1, hQ1⟩ : ∃ Q1, Q1 = Function.update S kS (Sym.mark :: S kS) := ⟨_, rfl⟩
  have e1 := (pc_eval kS Sym.mark v S).of_eq (st_eq rfl hQ1.symm) rfl
  obtain ⟨Q2, hQ2⟩ : ∃ Q2, Q2 = Function.update Q1 kY (Sym.mark :: Q1 kY) := ⟨_, rfl⟩
  have e2 := (pc_eval kY Sym.mark v Q1).of_eq (st_eq rfl hQ2.symm) rfl
  obtain ⟨Q3, hQ3⟩ : ∃ Q3, Q3 = Function.update Q2 kT (Sym.mark :: Q2 kT) := ⟨_, rfl⟩
  have e3 := (pc_eval kT Sym.mark v Q2).of_eq (st_eq rfl hQ3.symm) rfl
  obtain ⟨Q4, hQ4⟩ : ∃ Q4, Q4 = Function.update Q3 kV (Sym.mark :: Q3 kV) := ⟨_, rfl⟩
  have e4 := (pc_eval kV Sym.mark v Q3).of_eq (st_eq rfl hQ4.symm) rfl
  have h4K : Q4 kK = (encodeNat k).map Sym.bit ++ r0 := by
    simp only [hQ4, hQ3, hQ2, hQ1, Function.update_of_ne hKV, Function.update_of_ne hKT,
      Function.update_of_ne hKY, Function.update_of_ne hKS]
    exact hK
  have m5 := copyBlock_eval hKT hKV hTV [] v.1 (encodeNat k) r0 Q4 hr0 h4K
  obtain ⟨Q5, hQ5⟩ : ∃ Q5, Q5 = Function.update Q4 kT ((encodeNat k).map Sym.bit ++ Q4 kT) :=
    ⟨_, rfl⟩
  have e5 := (lift_eval m5 v rfl).of_eq (st_eq rfl hQ5.symm) rfl
  have h4T : Q4 kT = Sym.mark :: S kT := by
    simp only [hQ4, hQ3, hQ2, hQ1, Function.update_self, Function.update_of_ne hTV,
      Function.update_of_ne hTY, Function.update_of_ne hST.symm]
  have h5T : Q5 kT = natSyms k ++ Sym.mark :: S kT := by
    rw [hQ5, Function.update_self, h4T]
    rfl
  have e6 := pk_eval kT (some Sym.mark, v.2) Q5 _ h5T
  have hfin : Q5 = Function.update (Function.update (Function.update (Function.update S kS
      (Sym.mark :: S kS)) kY (Sym.mark :: S kY)) kT (natSyms k ++ Sym.mark :: S kT)) kV
      (Sym.mark :: S kV) := by
    funext i
    by_cases h1 : i = kT
    · rw [h1, h5T]
      simp only [Function.update_self, Function.update_of_ne hTV]
    by_cases h2 : i = kV
    · rw [h2]
      simp only [hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_self, Function.update_of_ne hTV.symm,
        Function.update_of_ne hVY, Function.update_of_ne hSV.symm]
    by_cases h3 : i = kY
    · rw [h3]
      simp only [hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_self, Function.update_of_ne hTY.symm,
        Function.update_of_ne hVY.symm, Function.update_of_ne hSY.symm]
    by_cases h4 : i = kS
    · rw [h4]
      simp only [hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_self, Function.update_of_ne hST,
        Function.update_of_ne hSV, Function.update_of_ne hSY]
    · simp only [hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4]
  refine ⟨1 + (1 + (1 + (1 + ((7 * (encodeNat k).length + 7) + 1)))), ?_,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq
      (st_eq rfl hfin) rfl⟩
  have hb : bitLen k = (encodeNat k).length := rfl
  omega

theorem cleanup_eval {kD kS kT kV kY : K} (hDS : kD ≠ kS) (hDT : kD ≠ kT) (hDV : kD ≠ kV)
    (hDY : kD ≠ kY) (hST : kS ≠ kT) (hSV : kS ≠ kV) (hSY : kS ≠ kY) (hTV : kT ≠ kV)
    (hTY : kT ≠ kY) (hVY : kV ≠ kY) (h : List Bool) (S0 T0 V0 Y0 : List Sym) (v : Reg)
    (S : K → List Sym) (hS : S kS = Sym.mark :: S0) (hT : S kT = Sym.mark :: T0)
    (hV : S kV = Sym.mark :: V0) (hY : S kY = h.reverse.map Sym.bit ++ Sym.mark :: Y0) :
    ∃ v' t, t ≤ 6 * h.length + 9 ∧ Eval [] (cleanup kD kS kT kV kY) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update (Function.update S
        kS S0) kT T0) kV V0) kY Y0) kD ((encodeNat (bitsVal h)).map Sym.bit ++ S kD)⟩ t := by
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S kS S0 := ⟨_, rfl⟩
  have e1 := (pd_eval kS v S _ _ hS).of_eq (st_eq rfl hS1.symm) rfl
  have h1T : S1 kT = Sym.mark :: T0 := by
    rw [hS1, Function.update_of_ne hST.symm, hT]
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 kT T0 := ⟨_, rfl⟩
  have e2 := (pd_eval kT v S1 _ _ h1T).of_eq (st_eq rfl hS2.symm) rfl
  have h2V : S2 kV = Sym.mark :: V0 := by
    rw [hS2, Function.update_of_ne hTV.symm, hS1, Function.update_of_ne hSV.symm, hV]
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 kV V0 := ⟨_, rfl⟩
  have e3 := (pd_eval kV v S2 _ _ h2V).of_eq (st_eq rfl hS3.symm) rfl
  have h3Y : S3 kY = h.reverse.map Sym.bit ++ Sym.mark :: Y0 := by
    rw [hS3, Function.update_of_ne hVY.symm, hS2, Function.update_of_ne hTY.symm, hS1,
      Function.update_of_ne hSY.symm, hY]
  have e4 := pk_eval kY v S3 _ h3Y
  obtain ⟨v5, t5, ht5, e5⟩ := dropLoop_eval Y0 h.reverse v.2 S3 h3Y
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = Function.update S3 kY
      ((h.reverse.dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0) := ⟨_, rfl⟩
  have e5' := e5.of_eq (st_eq rfl hS5.symm) rfl
  have h5Y : S5 kY = (h.reverse.dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0 := by
    rw [hS5, Function.update_self]
  have m6 := moveBits_eval hDY.symm [] v5.1 (h.reverse.dropWhile (fun b => !b)) (Sym.mark :: Y0)
    S5 (TermOK.cons rfl _) h5Y
  have e6 := lift_eval m6 v5 rfl
  have hfin : Function.update (Function.update S5 kY (Sym.mark :: Y0).tail) kD
      ((h.reverse.dropWhile (fun b => !b)).reverse.map Sym.bit ++ S5 kD) =
      Function.update (Function.update (Function.update (Function.update (Function.update S
        kS S0) kT T0) kV V0) kY Y0) kD ((encodeNat (bitsVal h)).map Sym.bit ++ S kD) := by
    funext i
    by_cases h1 : i = kD
    · rw [h1]
      simp only [Function.update_self, hS5, hS3, hS2, hS1, Function.update_of_ne hDY,
        Function.update_of_ne hDV, Function.update_of_ne hDT, Function.update_of_ne hDS,
        reverse_dropWhile_eq_encodeNat, List.reverse_reverse]
    by_cases h2 : i = kY
    · rw [h2]
      simp only [Function.update_self, Function.update_of_ne hDY.symm, List.tail_cons]
    by_cases h3 : i = kV
    · rw [h3]
      simp only [Function.update_self, Function.update_of_ne hDV.symm,
        Function.update_of_ne hVY, hS5, hS3]
    by_cases h4 : i = kT
    · rw [h4]
      simp only [Function.update_self, Function.update_of_ne hDT.symm,
        Function.update_of_ne hTY, Function.update_of_ne hTV, hS5, hS3, hS2]
    by_cases h5 : i = kS
    · rw [h5]
      simp only [Function.update_self, Function.update_of_ne hDS.symm,
        Function.update_of_ne hSY, Function.update_of_ne hSV, Function.update_of_ne hST, hS5, hS3,
        hS2, hS1]
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, Function.update_of_ne h5, hS5, hS3, hS2, hS1]
  refine ⟨_, 1 + (1 + (1 + (1 + (t5 + (3 * (h.reverse.dropWhile (fun b => !b)).length + 2))))),
    ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5' e6))))).of_eq
      (st_eq rfl hfin) rfl⟩
  have l1 := length_dropWhile_le' (fun b => !b) h.reverse
  rw [List.length_reverse] at l1 ht5
  omega

#assert_std_axioms setup_eval cleanup_eval

end WP.W4f
