import WP.W9fOps.Shape

/-!
# WP.W9fOps.MulPow2 — `z += a·2^|b|` (signed)

`mulPow2Prog`: pop both signs; copy `|a|` onto `z` (`W3_copyNat`, proved instance `w3_copyNat`);
shift `z` left by the counter `|b|` on `y` (`W3_shlVar`, hypothesis; the number's terminator is
the old content of `z`, hence `TermOK (S z)`); push the sign of `a` on `z` (`a·2^k` has the sign
of `a`, and zero stays `pos`); push both signs back.
Cost `Ccp·(|a| + 1) + Csh·(|b|ᵥ + |b| + 1) + 5`, i.e. `W9fShiftOp`.
-/

namespace WP.W9fOps

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers: two sign slots, then the copier's and the shifter's registers. -/
abbrev RegM (Rcp Rsh : Type) : Type := Option Sym × Option Sym × Rcp × Rsh

/-- Lens onto the copier's registers. -/
def lensMcp (Rcp Rsh : Type) : Lens (RegM Rcp Rsh) Rcp where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the shifter's registers. -/
def lensMsh (Rcp Rsh : Type) : Lens (RegM Rcp Rsh) Rsh where
  get v := v.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `z += a·2^|b|`. -/
def mulPow2Prog {mcp msh : ℕ} {Rcp Rsh : Type} (hcp : mcp ≤ 4) (hsh : msh ≤ 4)
    (Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp) (Psh : Prog (Loc 2 msh) (fun _ => Sym) Rsh) :
    Prog (Loc 3 4) (fun _ => Sym) (RegM Rcp Rsh) :=
  .seq (.pop (.inl 0) fun v o => (o, v.2))
  (.seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
  (.seq (call (emb f02 hcp) (lensMcp Rcp Rsh) Pcp)
  (.seq (call (emb f21 hsh) (lensMsh Rcp Rsh) Psh)
  (.seq (.push (.inl 2) fun v => v.1.getD .pos)
  (.seq (.push (.inl 1) fun v => v.2.1.getD .pos)
  (.push (.inl 0) fun v => v.1.getD .pos))))))

theorem mulPow2Prog_closed {mcp msh : ℕ} {Rcp Rsh : Type} (hcp : mcp ≤ 4) (hsh : msh ≤ 4)
    {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp} {Psh : Prog (Loc 2 msh) (fun _ => Sym) Rsh}
    (hPcp : Pcp.Closed) (hPsh : Psh.Closed) : (mulPow2Prog hcp hsh Pcp Psh).Closed :=
  ⟨trivial, trivial, call_closed _ _ hPcp, call_closed _ _ hPsh, trivial, trivial, trivial⟩

theorem two_pow_pos_int : ∀ k : ℕ, (0 : ℤ) < 2 ^ k
  | 0 => by rw [pow_zero]; decide
  | k + 1 => by
    have := two_pow_pos_int k
    rw [pow_succ]
    omega

theorem sgnSym_mul_pow2 (a : ℤ) (k : ℕ) : sgnSym (a * 2 ^ k) = sgnSym a := by
  have hP : (0 : ℤ) < 2 ^ k := two_pow_pos_int k
  refine sgnSym_congr ⟨fun h => ?_, fun h => Int.mul_neg_of_neg_of_pos h hP⟩
  by_contra ha
  exact absurd h (not_lt.2 (Int.mul_nonneg (not_lt.1 ha) hP.le))

theorem natAbs_mul_pow2 (a : ℤ) (k : ℕ) : (a * 2 ^ k).natAbs = a.natAbs * 2 ^ k := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  rfl

theorem mulPow2_runs {mcp msh : ℕ} {Rcp Rsh : Type} (hcp : mcp ≤ 4) (hsh : msh ≤ 4)
    {Ccp Csh : ℕ} {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp}
    {Psh : Prog (Loc 2 msh) (fun _ => Sym) Rsh} (hCp : CopySpec Ccp Pcp) (hSh : ShlSpec Csh Psh)
    (a b : ℤ) (ra rb : List Sym) (S : Loc 3 4 → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hz : TermOK (S (.inl 2))) (hx : S (.inl 0) = intSyms a ++ ra)
    (hy : S (.inl 1) = intSyms b ++ rb) :
    Runs (mulPow2Prog hcp hsh Pcp Psh) S
      (Function.update S (.inl 2) (intSyms (a * 2 ^ b.natAbs) ++ S (.inl 2))) (fun _ => True)
      (Ccp * (bitLen a.natAbs + 1) + Csh * (b.natAbs + bitLen b.natAbs + 1) + 5) := by
  refine Runs.of_eval fun v => ?_
  -- pop the signs
  have e1 := eval_pop_int [] (.inl 0) (fun (v : RegM Rcp Rsh) o => (o, v.2)) v S a ra hx
  have hS1y : Function.update S (.inl 0) (natSyms a.natAbs ++ ra) (.inl 1) = intSyms b ++ rb := by
    simp [hy]
  have e2 := eval_pop_int [] (.inl 1) (fun (v : RegM Rcp Rsh) o => (v.1, o, v.2.2))
    (some (sgnSym a), v.2) (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) b rb hS1y
  set S2 := Function.update (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) (.inl 1)
    (natSyms b.natAbs ++ rb) with hS2
  have hS2x : S2 (.inl 0) = natSyms a.natAbs ++ ra := by simp [hS2]
  have hS2y : S2 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS2]
  have hS2z : S2 (.inl 2) = S (.inl 2) := by simp [hS2]
  -- copy |a| onto z
  obtain ⟨r3, t3, e3, -, ht3⟩ := call_eval_upd (emb_injective f02_injective hcp)
    (hCp a.natAbs ra (fun l => S2 (emb f02 hcp l)) hra hS2x) (lensMcp Rcp Rsh)
    (some (sgnSym a), some (sgnSym b), v.2.2)
  set S3 := Function.update S2 (emb f02 hcp (.inl 1))
    (natSyms a.natAbs ++ (fun l => S2 (emb f02 hcp l)) (.inl 1)) with hS3
  have hS3z : S3 (.inl 2) = natSyms a.natAbs ++ S (.inl 2) := by simp [hS3, hS2z]
  have hS3y : S3 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS3, hS2y]
  -- shift z left by |b|
  obtain ⟨r4, t4, e4, -, ht4⟩ := call_eval_upd (emb_injective f21_injective hsh)
    (hSh a.natAbs b.natAbs (S (.inl 2)) rb (fun l => S3 (emb f21 hsh l)) hz hrb hS3z hS3y)
    (lensMsh Rcp Rsh) (some (sgnSym a), some (sgnSym b), r3, v.2.2.2)
  set S4 := Function.update S3 (emb f21 hsh (.inl 0))
    (natSyms (a.natAbs * 2 ^ b.natAbs) ++ S (.inl 2)) with hS4
  -- push the result sign, then the operand signs
  have e5 := eval_push_eq [] (.inl 2) (fun (v : RegM Rcp Rsh) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r3, r4) S4 (sgnSym a)
    (natSyms (a.natAbs * 2 ^ b.natAbs) ++ S (.inl 2)) rfl (by simp [hS4])
  set S5 := Function.update S4 (.inl 2)
    (sgnSym a :: (natSyms (a.natAbs * 2 ^ b.natAbs) ++ S (.inl 2))) with hS5
  have e6 := eval_push_eq [] (.inl 1) (fun (v : RegM Rcp Rsh) => v.2.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r3, r4) S5 (sgnSym b) (natSyms b.natAbs ++ rb) rfl
    (by simp [hS5, hS4, hS3y])
  have e7 := eval_push_eq [] (.inl 0) (fun (v : RegM Rcp Rsh) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r3, r4)
    (Function.update S5 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ rb))) (sgnSym a)
    (natSyms a.natAbs ++ ra) rfl (by simp [hS5, hS4, hS3, hS2x])
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))) ?_, trivial, by omega⟩
  funext k
  rcases k with ⟨_ | _ | _ | i, hi⟩ | j
  · simp [hS5, hS4, hS3, hS2, hx, intSyms_append]
  · simp [hS5, hS4, hS3, hS2, hy, intSyms_append]
  · simp [hS5, hS4, hS3, hS2, intSyms_append, sgnSym_mul_pow2, natAbs_mul_pow2]
  · omega
  · simp [hS5, hS4, hS3, hS2]

/-- **`a·2^|b|`**, from `W3_shlVar` (and the proved `w3_copyNat`). -/
theorem mulPow2_holds (hshl : W3_shlVar) : W9fShiftOp (fun a b => a * 2 ^ b.natAbs) := by
  obtain ⟨Ccp, hcp⟩ := w3_copyNat
  obtain ⟨mcp, Rcp, _ocp, Pcp, hmcp, hRcp, ⟨rcp⟩, hPcp, hspCp⟩ := hcp ()
  obtain ⟨Csh, hsh⟩ := hshl
  obtain ⟨msh, Rsh, _osh, Psh, hmsh, hRsh, ⟨rsh⟩, hPsh, hspSh⟩ := hsh ()
  refine ⟨Ccp + Csh + 5, 4, RegM Rcp Rsh, mulPow2Prog hmcp hmsh Pcp Psh, by decide, inferInstance,
    ⟨(none, none, rcp, rsh)⟩, mulPow2Prog_closed hmcp hmsh hPcp hPsh, ?_⟩
  intro a b ra rb S hra hrb hz hx hy
  refine Triple.cost_mono (mulPow2_runs hmcp hmsh hspCp hspSh a b ra rb S hra hrb hz hx hy) ?_
  have h1 := Nat.mul_le_mul (le_refl Ccp)
    (show bitLen a.natAbs + 1 ≤ bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1 by omega)
  have h2 := Nat.mul_le_mul (le_refl Csh)
    (show b.natAbs + bitLen b.natAbs + 1 ≤ bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1 by omega)
  rw [Nat.add_mul, Nat.add_mul]
  omega

#assert_std_axioms mulPow2Prog_closed two_pow_pos_int sgnSym_mul_pow2 natAbs_mul_pow2 mulPow2_runs mulPow2_holds

end WP.W9fOps
