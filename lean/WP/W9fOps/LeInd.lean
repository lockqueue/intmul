import WP.W9fOps.Shape

/-!
# WP.W9fOps.LeInd — `z += [a ≤ b]` (signed), from the proved unsigned comparator

`leIndProg`: pop both signs, compare the magnitudes with the `W3_cmpNat` program (proved
instance `w3_cmpNat`), decide `a ≤ b` from the signs and the unsigned order (`cmpIntObs`,
as in `wp/W3b`), push `[pos, 1]` or `[pos]` on `z`, push both signs back.
Cost `Cc·(|a| + |b| + 1) + 7`; no hypotheses.
-/

namespace WP.W9fOps

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers: two sign slots, then the comparator's registers. -/
abbrev RegL (Rc : Type) : Type := Option Sym × Option Sym × Rc

/-- Lens onto the comparator's registers. -/
def lensL (Rc : Type) : Lens (RegL Rc) Rc where
  get v := v.2.2
  set v w := (v.1, v.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `cmpZ a b` from the two signs and the unsigned comparison of the magnitudes. -/
def cmpIntObs {Rc : Type} (obsc : Rc → Ordering) (v : RegL Rc) : Ordering :=
  if isNegR v.1 then (if isNegR v.2.1 then (obsc v.2.2).swap else .lt)
  else (if isNegR v.2.1 then .gt else obsc v.2.2)

theorem cmpIntObs_spec {Rc : Type} (obsc : Rc → Ordering) (a b : ℤ) (r : Rc)
    (hr : obsc r = Lib.ordOf a.natAbs b.natAbs) :
    cmpIntObs obsc (some (sgnSym a), some (sgnSym b), r) = cmpZ a b := by
  simp only [cmpIntObs, isNegR_sgnSym, hr, decide_eq_true_eq]
  unfold cmpZ Lib.ordOf
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Push `[a ≤ b]` (as `intSyms`) on `z`. -/
def leIte {Rc : Type} (obsc : Rc → Ordering) : Prog (Loc 3 4) (fun _ => Sym) (RegL Rc) :=
  .ite (fun v => decide (cmpIntObs obsc v ≠ .gt))
    (.seq (.push (.inl 2) fun _ => .bit true) (.push (.inl 2) fun _ => .pos))
    (.push (.inl 2) fun _ => .pos)

/-- `z += [a ≤ b]`. -/
def leIndProg {mc : ℕ} {Rc : Type} (hmc : mc ≤ 4) (obsc : Rc → Ordering)
    (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) : Prog (Loc 3 4) (fun _ => Sym) (RegL Rc) :=
  .seq (.pop (.inl 0) fun v o => (o, v.2))
  (.seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
  (.seq (call (emb f23 hmc) (lensL Rc) Pc)
  (.seq (leIte obsc)
  (.seq (.push (.inl 1) fun v => v.2.1.getD .pos) (.push (.inl 0) fun v => v.1.getD .pos)))))

theorem natSyms_one : natSyms 1 = [.bit true] := by
  have h : encodeNat 1 = [true] := by
    have h0 := encodeNat_add_add_one 0
    rw [encodeNat_zero] at h0
    exact h0
  simp [natSyms, h]

theorem leIte_eval {Rc : Type} (obsc : Rc → Ordering) (a b : ℤ) (v : RegL Rc)
    (hv : cmpIntObs obsc v = cmpZ a b) (S : Loc 3 4 → List Sym) :
    ∃ t, t ≤ 3 ∧ Eval [] (leIte obsc) ⟨v, S⟩
      ⟨v, Function.update S (.inl 2) (intSyms (if a ≤ b then 1 else 0) ++ S (.inl 2))⟩ t := by
  by_cases hab : a ≤ b
  · have hc : decide (cmpIntObs obsc v ≠ .gt) = true := by
      rw [hv]
      exact decide_eq_true ((cmpZ_ne_gt_iff a b).2 hab)
    refine ⟨3, le_refl _, eval_stk (Eval.ite_true hc (Eval.seq (Eval.push [] _ _ v S)
      (Eval.push [] _ _ v _))) ?_⟩
    rw [if_pos hab, intSyms_append, sgnSym_of_nonneg (by omega), Function.update_idem]
    simp [natSyms_one]
  · have hc : decide (cmpIntObs obsc v ≠ .gt) = false := by
      rw [hv]
      exact decide_eq_false (fun h => hab ((cmpZ_ne_gt_iff a b).1 h))
    refine ⟨2, by omega, eval_stk (Eval.ite_false hc (Eval.push [] _ _ v S)) ?_⟩
    rw [if_neg hab, intSyms_append, sgnSym_of_nonneg (le_refl _)]
    simp [natSyms, encodeNat_zero]

/-- Body of `W3_cmpNat`. -/
def CmpSpec {m : ℕ} {R : Type} (C : ℕ) (obs : R → Ordering) (P : Prog (Loc 2 m) (fun _ => Sym) R) :
    Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S S (fun r => obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

theorem leInd_runs {mc : ℕ} {Rc : Type} (hmc : mc ≤ 4) {Cc : ℕ} {obsc : Rc → Ordering}
    {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} (hC : CmpSpec Cc obsc Pc)
    (a b : ℤ) (ra rb : List Sym) (S : Loc 3 4 → List Sym) (hra : TermOK ra) (hrb : TermOK rb)
    (hx : S (.inl 0) = intSyms a ++ ra) (hy : S (.inl 1) = intSyms b ++ rb) :
    Runs (leIndProg hmc obsc Pc) S
      (Function.update S (.inl 2) (intSyms (if a ≤ b then 1 else 0) ++ S (.inl 2)))
      (fun _ => True) (Cc * (bitLen a.natAbs + bitLen b.natAbs + 1) + 7) := by
  refine Runs.of_eval fun v => ?_
  have e1 := eval_pop_int [] (.inl 0) (fun (v : RegL Rc) o => (o, v.2)) v S a ra hx
  have hS1y : Function.update S (.inl 0) (natSyms a.natAbs ++ ra) (.inl 1) = intSyms b ++ rb := by
    simp [hy]
  have e2 := eval_pop_int [] (.inl 1) (fun (v : RegL Rc) o => (v.1, o, v.2.2))
    (some (sgnSym a), v.2) (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) b rb hS1y
  set S2 := Function.update (Function.update S (.inl 0) (natSyms a.natAbs ++ ra)) (.inl 1)
    (natSyms b.natAbs ++ rb) with hS2
  have hS2x : S2 (.inl 0) = natSyms a.natAbs ++ ra := by simp [hS2]
  have hS2y : S2 (.inl 1) = natSyms b.natAbs ++ rb := by simp [hS2]
  obtain ⟨r, t3, e3, hr, ht3⟩ := call_eval_same (emb_injective f23_injective hmc)
    (hC a.natAbs b.natAbs ra rb (fun l => S2 (emb f23 hmc l)) hra hrb hS2x hS2y) (lensL Rc)
    (some (sgnSym a), some (sgnSym b), v.2.2)
  obtain ⟨t4, ht4, e4⟩ := leIte_eval obsc a b (some (sgnSym a), some (sgnSym b), r)
    (cmpIntObs_spec obsc a b r hr) S2
  set S4 := Function.update S2 (.inl 2) (intSyms (if a ≤ b then 1 else 0) ++ S2 (.inl 2))
    with hS4
  have e5 := eval_push_eq [] (.inl 1) (fun (v : RegL Rc) => v.2.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r) S4 (sgnSym b) (natSyms b.natAbs ++ rb) rfl
    (by simp [hS4, hS2y])
  have e6 := eval_push_eq [] (.inl 0) (fun (v : RegL Rc) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r)
    (Function.update S4 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ rb))) (sgnSym a)
    (natSyms a.natAbs ++ ra) rfl (by simp [hS4, hS2x])
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq e5 e6))))) ?_, trivial, by omega⟩
  funext k
  rcases k with ⟨_ | _ | _ | i, hi⟩ | j
  · simp [hS4, hS2, hx, intSyms_append]
  · simp [hS4, hS2, hy, intSyms_append]
  · simp [hS4, hS2]
  · omega
  · simp [hS4, hS2]

theorem leIndProg_closed {mc : ℕ} {Rc : Type} (hmc : mc ≤ 4) (obsc : Rc → Ordering)
    {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} (hPc : Pc.Closed) :
    (leIndProg hmc obsc Pc).Closed :=
  ⟨trivial, trivial, call_closed _ _ hPc, ⟨⟨trivial, trivial⟩, trivial⟩, trivial, trivial⟩

/-- **`[a ≤ b]`**, no hypotheses: cost `(Cc + 7)·(|a| + |b| + 1)` with the `w3_cmpNat` constant. -/
theorem leInd_holds : W9fBinOp (fun a b => if a ≤ b then 1 else 0) := by
  obtain ⟨Cc, hc⟩ := w3_cmpNat
  obtain ⟨mc, Rc, obsc, Pc, hmc, hRc, ⟨r0⟩, hPc, hspec⟩ := hc ()
  refine ⟨Cc + 7, 4, RegL Rc, leIndProg hmc obsc Pc, by decide, inferInstance,
    ⟨(none, none, r0)⟩, leIndProg_closed hmc obsc hPc, ?_⟩
  intro a b ra rb S hra hrb _ hx hy
  refine Triple.cost_mono (leInd_runs hmc hspec a b ra rb S hra hrb hx hy) ?_
  rw [Nat.add_mul]
  omega

#assert_std_axioms cmpIntObs_spec natSyms_one leIte_eval leInd_runs leIndProg_closed leInd_holds

end WP.W9fOps
