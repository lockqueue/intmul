/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackFilt
import SubNLogN.Machine.Bridge.SpreadPackDataTop

/-!
# K5 spreading, filter packing: the contract (`Bridge/SpreadPackFiltTop.lean`)

**Scope (honest summary).** Proves `SpreadAux.packFilter_holds : PackFilterStmt`
(`Bridge/SpreadIface.lean`), with cost constant `C = 70`: the tap record `F` is read coefficient
by coefficient (`loopFilt_eval`), its symbols are pushed onto the restore copy `tr` in reading
order, and part `k` receives `natSyms (pack s (F.reverse.map (cpart w k)))` (first coefficient in
the most significant slot; `tst_emitSeq`); scratch stacks are restored. No hypothesis beyond the
statement's is used.
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

theorem carrSyms_single (w : ℕ) (F : List CInt) :
    carrSyms w [F] = (F.flatMap (coefBits w)).map Sym.bit ++ [Sym.sep] := by
  simp [carrSyms, arrSyms, blk, crecBits, recSyms]

variable {K : Type} [DecidableEq K]

theorem packFilter_main (ι : FiltRole → K) (hι : Function.Injective ι) (w s : ℕ) (F : List CInt)
    (rest Dlo Dpad : List Sym) (S : K → List Sym) (v : AReg) (hw : 1 ≤ w) (hws : w ≤ s)
    (hfits : ∀ x ∈ F, FitsTwos w x.1 ∧ FitsTwos w x.2)
    (hDlo : Dlo.head? ≠ some .mark) (hDpad : Dpad.head? ≠ some .mark)
    (hsrc : S (ι .src) = carrSyms w [F] ++ rest)
    (hlo : S (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo)
    (hpad : S (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad)
    (htmp : ∀ j, S (ι (.tmp j)) = []) :
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (packFiltProg K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ 70 * (F.length * (s + 1) + 1) ∧
      S' (ι .src) = rest ∧
      S' (ι .tr) = (carrSyms w [F]).reverse ++ S (ι .tr) ∧
      (∀ k, S' (ι (.out k)) = natSyms (pack s (F.reverse.map (cpart w k))) ++ S (ι (.out k))) ∧
      ∀ k, k ≠ ι .src → k ≠ ι .tr → (∀ j, k ≠ ι (.out j)) → S' k = S k := by
  have hsrc' : S (ι .src) = (F.flatMap (coefBits w)).map Sym.bit ++ Sym.sep :: rest := by
    rw [hsrc, carrSyms_single, List.append_assoc]
    rfl
  have e1 := eval_peekO (ι .src) v S
  have hst : st4F ι S (fun _ => []) (fun k => S (ι (.out k))) = S := by
    refine ext_F (ι := ι) (fun k hk => ?_) (fun r => ?_)
    · simp [st4F, setPM, eReF, eImF, Function.update_apply, hk]
    · rcases r with _ | k | _ | _ | _ | j
      · simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · fin_cases k <;> simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, tst,
          trimPush]
      · simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · fin_cases j <;> simp [st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, flagStk,
          htmp]
  obtain ⟨v2, e2⟩ := loopFilt_eval ι hι hw hws rest Dlo Dpad hDlo hDpad (fun k => S (ι (.out k)))
    F (fun _ => []) S { v with o := (S (ι .src)).head? } hfits hsrc' (htmp 0) hlo hpad
    (by rw [htmp 1]; simp) (by rw [htmp 2]; simp) rfl
  rw [hst] at e2
  set S2 := st4F ι (Function.update (Function.update S (ι .src) (Sym.sep :: rest)) (ι .tr)
    ((F.flatMap (coefBits w)).reverse.map Sym.bit ++ S (ι .tr))) (fun k => [] ++ emitSeq w s k F)
    (fun k => S (ι (.out k))) with hS2
  have hS2s : S2 (ι .src) = Sym.sep :: rest := by
    simp [hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
  have e3 := eval_move1 (hι.ne (by decide) : ι .src ≠ ι .tr) v2 S2 Sym.sep rest hS2s
  set S3 := Function.update (Function.update S2 (ι .src) rest) (ι .tr) (Sym.sep :: S2 (ι .tr))
    with hS3
  have c0 := eval_clrFlag (F := ι (.tmp 4)) ((emitSeq w s 0 F).any id)
    { v2 with o := some Sym.sep } S3
    (by simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff])
  refine ⟨_, _, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq c0
    (Eval.seq (eval_clrFlag (F := ι (.tmp 5)) ((emitSeq w s 1 F).any id) _
      (Function.update S3 (ι (.tmp 4)) [])
      (by simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]))
    (Eval.seq (eval_clrFlag (F := ι (.tmp 6)) ((emitSeq w s 2 F).any id) _
      (Function.update (Function.update S3 (ι (.tmp 4)) []) (ι (.tmp 5)) [])
      (by simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]))
      (eval_clrFlag (F := ι (.tmp 7)) ((emitSeq w s 3 F).any id) _
      (Function.update (Function.update (Function.update S3 (ι (.tmp 4)) []) (ι (.tmp 5)) [])
        (ι (.tmp 6)) [])
      (by simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]))))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · have hcc : coefCost w s + 1 ≤ 70 * (s + 1) := by
      unfold coefCost
      omega
    have hm : F.length * (coefCost w s + 1) ≤ F.length * (70 * (s + 1)) :=
      Nat.mul_le_mul_left _ hcc
    have r1 : F.length * (70 * (s + 1)) = 70 * (F.length * (s + 1)) := by ring
    omega
  · simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
  · simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff, carrSyms_single,
      List.reverse_append, List.map_reverse]
  · intro k
    fin_cases k <;> simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff,
      tst_emitSeq hw hws]
  · intro k h1 h2 h3
    by_cases hk : ∃ r, k = ι r
    · obtain ⟨r, rfl⟩ := hk
      rcases r with _ | j | _ | _ | _ | j
      · exact absurd rfl h1
      · exact absurd rfl (h3 j)
      · exact absurd rfl h2
      · simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hι.eq_iff]
      · fin_cases j <;> simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply,
          hι.eq_iff, htmp]
    · have hk' : ∀ r, k ≠ ι r := fun r hr => hk ⟨r, hr⟩
      simp [hS3, hS2, st4F, setPM, eReF, eImF, Function.update_apply, hk']

end SubNLogN.Machine.Bridge.SpreadPackAux

namespace SubNLogN.Machine.Bridge.SpreadAux

/-- **Filter packing holds** (`PackFilterStmt`, `Bridge/SpreadIface.lean`), cost constant `70`. -/
theorem packFilter_holds : PackFilterStmt :=
  ⟨SpreadPackAux.packFiltProg, 70, fun K _ ι => SpreadPackAux.closed_packFiltProg K ι,
    fun _ _ ι hι w s F rest Dlo Dpad S v hw hws hfits hDlo hDpad hsrc hlo hpad htmp =>
      SpreadPackAux.packFilter_main ι hι w s F rest Dlo Dpad S v hw hws hfits hDlo hDpad hsrc hlo
        hpad htmp⟩

end SubNLogN.Machine.Bridge.SpreadAux
