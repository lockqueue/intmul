/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackCollect

/-!
# K5 spreading, data packing: the contract (`Bridge/SpreadPackDataTop.lean`)

**Scope (honest summary).** Proves `SpreadAux.packData_holds : PackDataStmt`
(`Bridge/SpreadIface.lean`), with cost constant `C = 60`: the source's `m ≤ W` one-coefficient
records are collected onto a buffer (`collect_eval`), emitted part by part, most significant bit
first and trimmed (`loopEmit_eval`), so that part `k` receives
`natSyms (pack s (B.map (cpart w k)))` (`tst_emitSeq`, from `trimPush_pack`); `m` marks go onto
`M`; rulers, walk temporaries, the buffer and the flag stacks are restored. No hypothesis beyond
the statement's is used.
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

theorem tst_emitSeq {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (k : Fin 4) (L : List CInt)
    (D : List Sym) : tst (emitSeq w s k L) D = natSyms (pack s (L.reverse.map (cpart w k))) ++ D := by
  rw [tst, emitSeq, trimPush_pack hw hws k L]
  rfl

variable {K : Type} [DecidableEq K]

theorem packData_main (ι : PackRole → K) (hι : Function.Injective ι) (W w s : ℕ) (B : List CInt)
    (rest DW Dlo Dpad : List Sym) (S : K → List Sym) (v : AReg) (hw : 1 ≤ w) (hws : w ≤ s)
    (hBW : B.length ≤ W) (hrest : B.length < W → TermOK rest)
    (hfits : ∀ x ∈ B, FitsTwos w x.1 ∧ FitsTwos w x.2)
    (hDW : DW.head? ≠ some .mark) (hDlo : Dlo.head? ≠ some .mark) (hDpad : Dpad.head? ≠ some .mark)
    (hsrc : S (ι .src) = carrSyms w (B.map fun x => [x]) ++ rest)
    (hRW : S (ι .RW) = List.replicate W .mark ++ DW)
    (hlo : S (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo)
    (hpad : S (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad)
    (htmp : ∀ j, S (ι (.tmp j)) = []) :
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (packDataProg K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ 60 * (W * (s + 1) + 1) ∧
      S' (ι .src) = rest ∧
      (∀ k, S' (ι (.out k)) = natSyms (pack s (B.map (cpart w k))) ++ S (ι (.out k))) ∧
      S' (ι .M) = List.replicate B.length .mark ++ S (ι .M) ∧
      ∀ k, k ≠ ι .src → (∀ j, k ≠ ι (.out j)) → k ≠ ι .M → S' k = S k := by
  rw [carrSyms_singletons] at hsrc
  obtain ⟨v1, e1⟩ := collect_eval ι hι hw W B hBW rest DW hrest hDW S hsrc hRW
    (by rw [htmp 3]; simp) v
  set S1 := Function.update (Function.update (Function.update S (ι .src) rest) (ι (.tmp 0))
    (B.reverse.flatMap (revRec w) ++ S (ι (.tmp 0)))) (ι .M)
    (List.replicate B.length .mark ++ S (ι .M)) with hS1
  have hS1A : S1 (ι (.tmp 0)) = B.reverse.flatMap (revRec w) := by
    simp [hS1, Function.update_apply, hι.eq_iff, htmp]
  have e2 := eval_peekQ (ι (.tmp 0)) v1 S1
  rw [hS1A] at e2
  have hst : st4 ι S1 (fun _ => []) (fun k => S (ι (.out k))) = S1 := by
    refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
    · simp [st4, setPM, eReD, eImD, Function.update_apply, hk]
    · rcases r with _ | k | _ | _ | _ | _ | j
      · simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · fin_cases k <;> simp [st4, setPM, eReD, eImD, hS1, Function.update_apply, hι.eq_iff, tst,
          trimPush]
      · simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · simp [st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · fin_cases j <;> simp [st4, setPM, eReD, eImD, hS1, Function.update_apply, hι.eq_iff,
          flagStk, htmp]
  obtain ⟨v3, e3⟩ := loopEmit_eval ι hι hw hws Dlo Dpad hDlo hDpad (fun k => S (ι (.out k)))
    B.reverse (fun _ => []) S1 { v1 with q := (B.reverse.flatMap (revRec w)).head? }
    (fun x hx => hfits x (List.mem_reverse.mp hx)) hS1A
    (by simp [hS1, Function.update_apply, hι.eq_iff, hlo])
    (by simp [hS1, Function.update_apply, hι.eq_iff, hpad])
    (by simp [hS1, Function.update_apply, hι.eq_iff, htmp])
    (by simp [hS1, Function.update_apply, hι.eq_iff, htmp]) rfl
  rw [hst] at e3
  set S3 := st4 ι (Function.update S1 (ι (.tmp 0)) [])
    (fun k => [] ++ emitSeq w s k B.reverse) (fun k => S (ι (.out k))) with hS3
  have c0 := eval_clrFlag (F := ι (.tmp 4)) ((emitSeq w s 0 B.reverse).any id) v3 S3
    (by simp [hS3, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff])
  refine ⟨_, _, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq c0
    (Eval.seq (eval_clrFlag (F := ι (.tmp 5)) ((emitSeq w s 1 B.reverse).any id) _
      (Function.update S3 (ι (.tmp 4)) [])
      (by simp [hS3, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]))
    (Eval.seq (eval_clrFlag (F := ι (.tmp 6)) ((emitSeq w s 2 B.reverse).any id) _
      (Function.update (Function.update S3 (ι (.tmp 4)) []) (ι (.tmp 5)) [])
      (by simp [hS3, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]))
      (eval_clrFlag (F := ι (.tmp 7)) ((emitSeq w s 3 B.reverse).any id) _
      (Function.update (Function.update (Function.update S3 (ι (.tmp 4)) []) (ι (.tmp 5)) [])
        (ι (.tmp 6)) [])
      (by simp [hS3, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]))))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · have hsum : (Finset.range W).sum (fun j => (if j < B.length then 8 * w + 7 else 4) + 4) ≤
        (Finset.range W).sum (fun _ => 8 * w + 11) :=
      Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
    have hec : 2 * (18 * (s - w) + 19 * (w - 1) + 19) + 3 ≤ 38 * s + 41 := by omega
    have hmc : B.reverse.length * (2 * (18 * (s - w) + 19 * (w - 1) + 19) + 3) ≤
        W * (38 * s + 41) := by
      rw [List.length_reverse]
      exact Nat.mul_le_mul hBW hec
    have hW1 : W * (8 * w + 11) ≤ W * (8 * s + 11) := Nat.mul_le_mul_left _ (by omega)
    have r1 : W * (8 * s + 11) = 8 * (W * s) + 11 * W := by ring
    have r2 : W * (38 * s + 41) = 38 * (W * s) + 41 * W := by ring
    have r3 : 60 * (W * (s + 1) + 1) = 60 * (W * s) + 60 * W + 60 := by ring
    omega
  · simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
  · intro k
    fin_cases k <;> simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff,
      tst_emitSeq hw hws]
  · simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
  · intro k h1 h2 h3
    by_cases hk : ∃ r, k = ι r
    · obtain ⟨r, rfl⟩ := hk
      rcases r with _ | j | _ | _ | _ | _ | j
      · exact absurd rfl h1
      · exact absurd rfl (h2 j)
      · exact absurd rfl h3
      · simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hι.eq_iff]
      · fin_cases j <;> simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply,
          hι.eq_iff, htmp]
    · have hk' : ∀ r, k ≠ ι r := fun r hr => hk ⟨r, hr⟩
      simp [hS3, hS1, st4, setPM, eReD, eImD, Function.update_apply, hk']

end SubNLogN.Machine.Bridge.SpreadPackAux

namespace SubNLogN.Machine.Bridge.SpreadAux

/-- **Data packing holds** (`PackDataStmt`, `Bridge/SpreadIface.lean`), cost constant `60`. -/
theorem packData_holds : PackDataStmt :=
  ⟨SpreadPackAux.packDataProg, 60, fun K _ ι => SpreadPackAux.closed_packDataProg K ι,
    fun _ _ ι hι W w s B rest DW Dlo Dpad S v hw hws hBW hrest hfits hDW hDlo hDpad hsrc hRW hlo
      hpad htmp => SpreadPackAux.packData_main ι hι W w s B rest DW Dlo Dpad S v hw hws hBW hrest
        hfits hDW hDlo hDpad hsrc hRW hlo hpad htmp⟩

end SubNLogN.Machine.Bridge.SpreadAux
