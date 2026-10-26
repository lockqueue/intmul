import WP.W3b.Glue

/-!
# WP.W3b.CmpInt — signed comparison from the unsigned comparator

`cmpIntProg Pc` (stacks `x = .inl 0`, `y = .inl 1`, plus the comparator's scratch stacks):
pop both signs, run the unsigned comparator `Pc` on the magnitudes (`W3_cmpNat`, from the
proved instance `w3_cmpNat`), push both signs back. The result is computed by the observation:

| sign `a` | sign `b` | `cmpZ a b` |
|---|---|---|
| `pos` | `pos` | `ordOf |a| |b|` |
| `neg` | `neg` | `(ordOf |a| |b|).swap` |
| `neg` | `pos` | `lt` |
| `pos` | `neg` | `gt` |

(`neg` means strictly negative: zero is `[pos]`.) Cost `Cc·(|a|+|b|+1) + 4`.
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers of a two-operand signed program: two sign slots, then the subroutines' registers. -/
abbrev RegS (Rc : Type) : Type := Option Sym × Option Sym × Rc

/-- Lens onto the subroutine registers. -/
def lensSub (Rc : Type) : Lens (RegS Rc) Rc where
  get v := v.2.2
  set v w := (v.1, v.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `cmpZ a b` from the two signs and the unsigned comparison of the magnitudes. -/
def cmpIntObs {Rc : Type} (obsc : Rc → Ordering) (v : RegS Rc) : Ordering :=
  if isNegR v.1 then (if isNegR v.2.1 then (obsc v.2.2).swap else .lt)
  else (if isNegR v.2.1 then .gt else obsc v.2.2)

/-- Pop both signs, compare the magnitudes, push both signs back. -/
def cmpIntProg {mc : ℕ} {Rc : Type} (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) :
    Prog (Loc 2 mc) (fun _ => Sym) (RegS Rc) :=
  .seq (.pop (.inl 0) fun v o => (o, v.2))
    (.seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
      (.seq (call id (lensSub Rc) Pc)
        (.seq (.push (.inl 1) fun v => v.2.1.getD .pos) (.push (.inl 0) fun v => v.1.getD .pos))))

theorem cmpIntObs_spec {Rc : Type} (obsc : Rc → Ordering) (a b : ℤ) (r : Rc)
    (hr : obsc r = Lib.ordOf a.natAbs b.natAbs) :
    cmpIntObs obsc (some (sgnSym a), some (sgnSym b), r) = cmpZ a b := by
  simp only [cmpIntObs, isNegR_sgnSym, hr, decide_eq_true_eq]
  unfold cmpZ Lib.ordOf
  split_ifs <;> first | rfl | (exfalso; omega)

theorem W3_cmpInt_holds : W3_cmpInt := by
  obtain ⟨Cc, hc⟩ := w3_cmpNat
  obtain ⟨mc, Rc, obsc, Pc, hmc, hRc, ⟨r0⟩, hPc, hspec⟩ := hc ()
  refine ⟨Cc + 4, fun _ => ⟨mc, RegS Rc, cmpIntObs obsc, cmpIntProg Pc, hmc, inferInstance,
    ⟨(none, none, r0)⟩, ⟨trivial, trivial, call_closed id (lensSub Rc) hPc, trivial, trivial⟩,
    ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  refine Runs.of_eval fun v => ?_
  -- pop the two signs
  have e1 := eval_pop_int [] (.inl 0) (fun (v : RegS Rc) o => (o, v.2)) v S a rx hx
  have hS1y : Function.update S (.inl 0) (natSyms a.natAbs ++ rx) (.inl 1) = intSyms b ++ ry := by
    simp [hy]
  have e2 := eval_pop_int [] (.inl 1) (fun (v : RegS Rc) o => (v.1, o, v.2.2))
    (some (sgnSym a), v.2) (Function.update S (.inl 0) (natSyms a.natAbs ++ rx)) b ry hS1y
  -- the magnitudes are in place
  set S2 := Function.update (Function.update S (.inl 0) (natSyms a.natAbs ++ rx)) (.inl 1)
    (natSyms b.natAbs ++ ry) with hS2
  have hS2x : S2 (.inl 0) = natSyms a.natAbs ++ rx := by simp [hS2]
  have hS2y : S2 (.inl 1) = natSyms b.natAbs ++ ry := by simp [hS2]
  -- compare
  obtain ⟨r, t, e3, hr, ht⟩ := call_eval_same (ι := id) (B := S2) Function.injective_id
    (hspec a.natAbs b.natAbs rx ry (fun l => S2 (id l)) hrx hry hS2x hS2y) (lensSub Rc)
    (some (sgnSym a), some (sgnSym b), v.2.2)
  -- push the two signs back
  have e4 := eval_push_eq [] (.inl 1) (fun (v : RegS Rc) => v.2.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r) S2 (sgnSym b) (natSyms b.natAbs ++ ry) rfl hS2y
  have hS4x : Function.update S2 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ ry)) (.inl 0) =
      natSyms a.natAbs ++ rx := by
    simp [hS2x]
  have e5 := eval_push_eq [] (.inl 0) (fun (v : RegS Rc) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), r)
    (Function.update S2 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ ry))) (sgnSym a)
    (natSyms a.natAbs ++ rx) rfl hS4x
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))) ?_,
    cmpIntObs_spec obsc a b r hr, ?_⟩
  · funext k
    rw [hS2]
    rcases k with i | j
    · rcases i with ⟨_ | _ | i, hi⟩
      · simp [hx, intSyms_append]
      · simp [hy, intSyms_append]
      · omega
    · simp
  · rw [Nat.add_mul]
    omega

#assert_std_axioms cmpIntObs_spec W3_cmpInt_holds

end TMFw.W3b
