import WP.W4f.Prog

/-!
# WP.W4f.Phases — setup, unary expansion, output normalization, cleanup

* `setup_eval`: marks on `kS, kY, kT, kV`, then a copy of `k` on `kT` (cost `7·|k| + 12`).
* `initLoop_eval`: `j` decrements of the counter on `kT`, each pushing a `1` on `kS`
  (`s := 1^j`; cost `≤ j·(6J + 12) + 1` for `j ≤ J`, using `|enc j| ≤ j`).
* `dropLoop_eval`: drop the leading zeros of an MSB-first block.
* `cleanup_eval`: pop the marks, normalize `kY` and move it onto `kD`, which receives
  `encodeNat (bitsVal h)` (`Bits.reverse_dropWhile_eq_encodeNat`).
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem encodeNat_one : encodeNat 1 = [true] := by
  have h := encodeNat_add_add_one 0
  rw [encodeNat_zero] at h
  exact h

theorem natSyms_zero : natSyms 0 = [] := by
  rw [natSyms, encodeNat_zero, List.map_nil]

theorem symBit_natSyms_succ (j : ℕ) (rest : List Sym) (w : Bool × Bool) :
    symBit ((natSyms (j + 1) ++ rest).head?, w) = true := by
  obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat (j + 1) = b :: l := by
    cases h : encodeNat (j + 1) with
    | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (Nat.succ_ne_zero j)
    | cons b l => exact ⟨b, l, rfl⟩
  rw [natSyms, hbl]
  rfl

theorem length_dropWhile_le' (p : Bool → Bool) :
    ∀ l : List Bool, (l.dropWhile p).length ≤ l.length
  | [] => le_refl _
  | b :: l => by
    rw [List.dropWhile_cons]
    split
    · exact le_trans (length_dropWhile_le' p l) (Nat.le_succ _)
    · exact le_refl _

variable {K : Type} [DecidableEq K]

theorem initLoop_eval {kS kT kV : K} (hST : kS ≠ kT) (hSV : kS ≠ kV) (hTV : kT ≠ kV)
    (T0 : List Sym) (J : ℕ) :
    ∀ (j : ℕ) (a c : Bool) (S : K → List Sym), j ≤ J → S kT = natSyms j ++ Sym.mark :: T0 →
      ∃ v' t, t ≤ j * (6 * J + 12) + 1 ∧
        Eval [] (initLoop kS kT kV) ⟨((natSyms j ++ Sym.mark :: T0).head?, a, c), S⟩
          ⟨v', Function.update (Function.update S kT (Sym.mark :: T0)) kS
            ((List.replicate j true).map Sym.bit ++ S kS)⟩ t
  | 0, a, c, S, _, hT => by
    have hT' : S kT = Sym.mark :: T0 := by rw [hT, natSyms_zero, List.nil_append]
    have hfin : Function.update (Function.update S kT (Sym.mark :: T0)) kS
        ((List.replicate 0 true).map Sym.bit ++ S kS) = S := by
      simp only [List.replicate_zero, List.map_nil, List.nil_append]
      rw [← hT', Function.update_eq_self, Function.update_eq_self]
    refine ⟨_, 1, by omega, (Eval.loop_false ?_).of_eq (st_eq rfl hfin.symm) rfl⟩
    rw [natSyms_zero]
    rfl
  | j + 1, a, c, S, hj, hT => by
    have m1 := dec_eval hTV [] ((natSyms (j + 1) ++ Sym.mark :: T0).head?) j (Sym.mark :: T0) S
      (TermOK.cons rfl _) hT
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S kT (natSyms j ++ Sym.mark :: T0) :=
      ⟨_, rfl⟩
    have e1 := (lift_eval m1 ((natSyms (j + 1) ++ Sym.mark :: T0).head?, a, c) rfl).of_eq
      (st_eq rfl hS1.symm) rfl
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 kS (Sym.bit true :: S1 kS) := ⟨_, rfl⟩
    have e2 := (pc_eval kS (Sym.bit true) (some Sym.mark, a, c) S1).of_eq (st_eq rfl hS2.symm) rfl
    have h2T : S2 kT = natSyms j ++ Sym.mark :: T0 := by
      rw [hS2, Function.update_of_ne (Ne.symm hST), hS1, Function.update_self]
    have e3 := pk_eval kT (some Sym.mark, a, c) S2 _ h2T
    obtain ⟨v', t, ht, ih⟩ := initLoop_eval hST hSV hTV T0 J j a c S2 (by omega) h2T
    have hfin : Function.update (Function.update S2 kT (Sym.mark :: T0)) kS
        ((List.replicate j true).map Sym.bit ++ S2 kS) =
        Function.update (Function.update S kT (Sym.mark :: T0)) kS
          ((List.replicate (j + 1) true).map Sym.bit ++ S kS) := by
      funext i
      by_cases h1 : i = kS
      · rw [h1]
        simp only [Function.update_self, hS2, hS1, Function.update_of_ne hST,
          List.replicate_succ', List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append, List.nil_append]
      by_cases h2 : i = kT
      · rw [h2]
        simp only [Function.update_self, Function.update_of_ne (Ne.symm hST)]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, hS2, hS1]
    have hz : zerosLead (encodeNat (j + 1)) ≤ J := by
      have h1 := zerosLead_le_length (encodeNat (j + 1))
      have h2 := length_encodeNat_le (j + 1)
      omega
    refine ⟨v', 6 * zerosLead (encodeNat (j + 1)) + 8 + (1 + 1) + t + 1, ?_,
      (Eval.loop_true (symBit_natSyms_succ j _ _) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq
        (st_eq rfl hfin) rfl⟩
    have hjJ : (j + 1) * (6 * J + 12) = j * (6 * J + 12) + (6 * J + 12) := Nat.succ_mul _ _
    rw [hjJ]
    omega

theorem dropLoop_eval {kY : K} (Y0 : List Sym) :
    ∀ (ds : List Bool) (w : Bool × Bool) (S : K → List Sym),
      S kY = ds.map Sym.bit ++ Sym.mark :: Y0 →
      ∃ v' t, t ≤ 3 * ds.length + 1 ∧
        Eval [] (dropLoop kY) ⟨((ds.map Sym.bit ++ Sym.mark :: Y0).head?, w), S⟩
          ⟨v', Function.update S kY
            ((ds.dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0)⟩ t
  | [], w, S, hY => by
    have hY' : S kY = Sym.mark :: Y0 := hY
    have hfin : Function.update S kY
        ((([] : List Bool).dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0) = S := by
      simp only [List.dropWhile_nil, List.map_nil, List.nil_append]
      rw [← hY', Function.update_eq_self]
    exact ⟨_, 1, by omega, (Eval.loop_false (isBitR_head?_of_termOK false
      (TermOK.cons rfl Y0))).of_eq (st_eq rfl hfin.symm) rfl⟩
  | d :: ds, w, S, hY => by
    cases d with
    | true =>
      have hfin : Function.update S kY
          (((true :: ds).dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0) = S := by
        have hd : (true :: ds).dropWhile (fun b => !b) = true :: ds := by
          simp
        rw [hd, ← hY, Function.update_eq_self]
      exact ⟨_, 1, by omega, (Eval.loop_false (by rfl)).of_eq (st_eq rfl hfin.symm) rfl⟩
    | false =>
      have hY' : S kY = Sym.bit false :: (ds.map Sym.bit ++ Sym.mark :: Y0) := hY
      obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S kY (ds.map Sym.bit ++ Sym.mark :: Y0) :=
        ⟨_, rfl⟩
      have e1 := (pd_eval kY (((false :: ds).map Sym.bit ++ Sym.mark :: Y0).head?, w) S _ _
        hY').of_eq (st_eq rfl hS1.symm) rfl
      have h1Y : S1 kY = ds.map Sym.bit ++ Sym.mark :: Y0 := by
        rw [hS1, Function.update_self]
      have e2 := pk_eval kY (((false :: ds).map Sym.bit ++ Sym.mark :: Y0).head?, w) S1 _ h1Y
      obtain ⟨v', t, ht, ih⟩ := dropLoop_eval Y0 ds w S1 h1Y
      have hfin : Function.update S1 kY
          ((ds.dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0) =
          Function.update S kY
            (((false :: ds).dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: Y0) := by
        have hd : (false :: ds).dropWhile (fun b => !b) = ds.dropWhile (fun b => !b) := by
          simp
        rw [hd, hS1, Function.update_idem]
      exact ⟨v', 1 + 1 + t + 1, by simp only [List.length_cons]; omega,
        (Eval.loop_true (by rfl) (Eval.seq e1 e2) ih).of_eq (st_eq rfl hfin) rfl⟩

#assert_std_axioms encodeNat_one natSyms_zero symBit_natSyms_succ length_dropWhile_le'
  initLoop_eval dropLoop_eval

end WP.W4f
