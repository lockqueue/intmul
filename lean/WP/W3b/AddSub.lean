import WP.W3b.AddSubMath

/-!
# WP.W3b.AddSub — signed add / subtract programs and the contract theorems

See `WP.W3b.AddSubMath` for the algorithm and the case arithmetic. Here: the program (over
`Loc 3 4`, registers `RegA = Option Sym × Option Sym × Ra × Rs × Rc`), its evaluation, and
`W3_addInt_holds (ha : W3_addNat) (hs : W3_subNat)`, `W3_subInt_holds (ha) (hs)`.

Embeddings of the subroutines (all scratch stacks shared, `emb`): adder and subtractor on
`x, y, z` (`id`), subtractor with swapped operands on `y, x, z` (`sw01`), comparator on `x, y`
(`f23`).
-/

namespace TMFw.W3b

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Registers of signed add/sub: two sign slots, then the adder's, subtractor's and comparator's
registers. -/
abbrev RegA (Ra Rs Rc : Type) : Type := Option Sym × Option Sym × Ra × Rs × Rc

/-- Lens onto the adder's registers. -/
def lensAdd (Ra Rs Rc : Type) : Lens (RegA Ra Rs Rc) Ra where
  get v := v.2.2.1
  set v w := (v.1, v.2.1, w, v.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the subtractor's registers. -/
def lensSubtr (Ra Rs Rc : Type) : Lens (RegA Ra Rs Rc) Rs where
  get v := v.2.2.2.1
  set v w := (v.1, v.2.1, v.2.2.1, w, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the comparator's registers. -/
def lensCmp (Ra Rs Rc : Type) : Lens (RegA Ra Rs Rc) Rc where
  get v := v.2.2.2.2
  set v w := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Swap the first two named stacks (computes `y - x`). -/
def sw01 (i : Fin 3) : Fin 3 := if i = 0 then 1 else if i = 1 then 0 else i

theorem sw01_injective : Function.Injective sw01 := by
  unfold Function.Injective
  decide

/-- The comparator's two named stacks into `x, y`. -/
def f23 (i : Fin 2) : Fin 3 := ⟨i.val, by have := i.isLt; omega⟩

theorem f23_injective : Function.Injective f23 := by
  intro i j h
  have h' : (f23 i).val = (f23 j).val := congrArg Fin.val h
  exact Fin.ext h'

section Prog

variable {ma ms mc : ℕ} {Ra Rs Rc : Type}

/-- The signed core on the popped magnitudes. -/
def addSubCore (hma : ma ≤ 4) (hms : ms ≤ 4) (hmc : mc ≤ 4) (obsc : Rc → Ordering)
    (Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra) (Ps : Prog (Loc 3 ms) (fun _ => Sym) Rs)
    (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (flip : Bool) :
    Prog (Loc 3 4) (fun _ => Sym) (RegA Ra Rs Rc) :=
  .ite (fun v => decide (isNegR v.1 = xor (isNegR v.2.1) flip))
    (.seq (call (emb id hma) (lensAdd Ra Rs Rc) Pa) (.push (.inl 2) fun v => v.1.getD .pos))
    (.seq (call (emb f23 hmc) (lensCmp Ra Rs Rc) Pc)
      (.ite (fun v => decide (obsc v.2.2.2.2 = .lt))
        (.seq (call (emb sw01 hms) (lensSubtr Ra Rs Rc) Ps)
          (.push (.inl 2) fun v => if xor (isNegR v.2.1) flip then .neg else .pos))
        (.seq (call (emb id hms) (lensSubtr Ra Rs Rc) Ps)
          (.push (.inl 2) fun v => if obsc v.2.2.2.2 = .gt then v.1.getD .pos else .pos))))

/-- Signed `z += a + b` (`flip = false`) or `z += a - b` (`flip = true`). -/
def addSubProg (hma : ma ≤ 4) (hms : ms ≤ 4) (hmc : mc ≤ 4) (obsc : Rc → Ordering)
    (Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra) (Ps : Prog (Loc 3 ms) (fun _ => Sym) Rs)
    (Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc) (flip : Bool) :
    Prog (Loc 3 4) (fun _ => Sym) (RegA Ra Rs Rc) :=
  .seq (.pop (.inl 0) fun v o => (o, v.2))
  (.seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
  (.seq (addSubCore hma hms hmc obsc Pa Ps Pc flip)
  (.seq (.push (.inl 1) fun v => v.2.1.getD .pos) (.push (.inl 0) fun v => v.1.getD .pos))))

theorem addSubProg_closed (hma : ma ≤ 4) (hms : ms ≤ 4) (hmc : mc ≤ 4) (obsc : Rc → Ordering)
    {Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra} {Ps : Prog (Loc 3 ms) (fun _ => Sym) Rs}
    {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc} (hPa : Pa.Closed) (hPs : Ps.Closed)
    (hPc : Pc.Closed) (flip : Bool) : (addSubProg hma hms hmc obsc Pa Ps Pc flip).Closed :=
  ⟨trivial, trivial, ⟨⟨call_closed _ _ hPa, trivial⟩, call_closed _ _ hPc,
    ⟨call_closed _ _ hPs, trivial⟩, call_closed _ _ hPs, trivial⟩, trivial, trivial⟩

theorem addSubCore_eval (hma : ma ≤ 4) (hms : ms ≤ 4) (hmc : mc ≤ 4) {Ca Cs Cc : ℕ}
    {obsc : Rc → Ordering} {Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Ps : Prog (Loc 3 ms) (fun _ => Sym) Rs} {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc}
    (hA : AddSpec Ca Pa) (hS : SubSpec Cs Ps) (hC : CmpSpec Cc obsc Pc) (flip : Bool)
    (a b : ℤ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (S : Loc 3 4 → List Sym)
    (hx : S (.inl 0) = natSyms a.natAbs ++ rx) (hy : S (.inl 1) = natSyms b.natAbs ++ ry)
    (w : Ra × Rs × Rc) :
    ∃ w' t, Eval [] (addSubCore hma hms hmc obsc Pa Ps Pc flip)
      ⟨(some (sgnSym a), some (sgnSym b), w), S⟩
      ⟨(some (sgnSym a), some (sgnSym b), w'),
        Function.update S (.inl 2) (intSyms (a + effB flip b) ++ S (.inl 2))⟩ t ∧
      t ≤ (Ca + Cs + Cc) * (bitLen a.natAbs + bitLen b.natAbs + 1) + 3 := by
  have hcA := effB_natAbs flip b
  have hnc := effNeg_spec flip b
  by_cases hs : decide (a < 0) = effNeg flip b
  · -- equal signs: add the magnitudes, keep the sign of `a`
    have hc : decide (isNegR (some (sgnSym a)) = xor (isNegR (some (sgnSym b))) flip) = true := by
      rw [isNegR_sgnSym, isNegR_sgnSym]
      exact decide_eq_true hs
    obtain ⟨r, t1, e1, -, ht1⟩ := call_eval_upd (emb_injective Function.injective_id hma)
      (hA a.natAbs b.natAbs rx ry (fun l => S (emb id hma l)) hrx hry hx hy)
      (lensAdd Ra Rs Rc) (some (sgnSym a), some (sgnSym b), w)
    have e2 := eval_push_eq [] (.inl 2) (fun (v : RegA Ra Rs Rc) => v.1.getD .pos)
      (some (sgnSym a), some (sgnSym b), r, w.2)
      (Function.update S (emb id hma (.inl 2))
        (natSyms (a.natAbs + b.natAbs) ++ (fun l => S (emb id hma l)) (.inl 2)))
      (sgnSym a) (natSyms (a.natAbs + b.natAbs) ++ S (.inl 2)) rfl (by simp [emb])
    obtain ⟨hm, hsg⟩ := arith_same a (effB flip b) (effNeg flip b) hnc hs
    rw [hcA] at hm
    refine ⟨(r, w.2), _, eval_stk (Eval.ite_true hc (Eval.seq e1 e2)) ?_, ?_⟩
    · rw [show emb id hma (.inl 2) = (.inl 2 : Loc 3 4) from rfl, Function.update_idem,
        intSyms_eq_cons hsg hm, List.cons_append]
    · simp only [Nat.add_mul]
      omega
  · have hc : decide (isNegR (some (sgnSym a)) = xor (isNegR (some (sgnSym b))) flip) =
        false := by
      rw [isNegR_sgnSym, isNegR_sgnSym]
      exact decide_eq_false hs
    obtain ⟨rc, t1, e1, hrc, ht1⟩ := call_eval_same (emb_injective f23_injective hmc)
      (hC a.natAbs b.natAbs rx ry (fun l => S (emb f23 hmc l)) hrx hry hx hy)
      (lensCmp Ra Rs Rc) (some (sgnSym a), some (sgnSym b), w)
    by_cases hlt : obsc rc = .lt
    · -- `|a| < |b|`: `z += |b| - |a|`, sign of the effective `b`
      have hab : a.natAbs < b.natAbs := ordOf_eq_lt (hrc.symm.trans hlt)
      have hc2 : decide (obsc rc = .lt) = true := decide_eq_true hlt
      obtain ⟨r, t2, e2, -, ht2⟩ := call_eval_upd (emb_injective sw01_injective hms)
        (hS b.natAbs a.natAbs ry rx (fun l => S (emb sw01 hms l)) hry hrx hab.le hy hx)
        (lensSubtr Ra Rs Rc) (some (sgnSym a), some (sgnSym b), w.1, w.2.1, rc)
      have e3 := eval_push_eq [] (.inl 2)
        (fun (v : RegA Ra Rs Rc) => if xor (isNegR v.2.1) flip then .neg else .pos)
        (some (sgnSym a), some (sgnSym b), w.1, r, rc)
        (Function.update S (emb sw01 hms (.inl 2))
          (natSyms (b.natAbs - a.natAbs) ++ (fun l => S (emb sw01 hms l)) (.inl 2)))
        (if effNeg flip b then .neg else .pos) (natSyms (b.natAbs - a.natAbs) ++ S (.inl 2))
        (by simp only [isNegR_sgnSym, effNeg]; rfl) (by simp [emb, sw01])
      obtain ⟨hm, hsg⟩ := arith_lt a (effB flip b) (effNeg flip b) hnc hs (by rw [hcA]; exact hab)
      rw [hcA] at hm
      refine ⟨(w.1, r, rc), _, eval_stk (Eval.ite_false hc (Eval.seq e1
        (Eval.ite_true hc2 (Eval.seq e2 e3)))) ?_, ?_⟩
      · rw [show emb sw01 hms (.inl 2) = (.inl 2 : Loc 3 4) from rfl, Function.update_idem,
          intSyms_eq_cons hsg hm, List.cons_append]
      · simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at ht1 ht2 ⊢
        omega
    · -- `|b| ≤ |a|`: `z += |a| - |b|`, sign of `a` (or `pos` if equal)
      have hab : b.natAbs ≤ a.natAbs := ordOf_ne_lt (fun h => hlt (hrc.trans h))
      have hc2 : decide (obsc rc = .lt) = false := decide_eq_false hlt
      obtain ⟨r, t2, e2, -, ht2⟩ := call_eval_upd (emb_injective Function.injective_id hms)
        (hS a.natAbs b.natAbs rx ry (fun l => S (emb id hms l)) hrx hry hab hx hy)
        (lensSubtr Ra Rs Rc) (some (sgnSym a), some (sgnSym b), w.1, w.2.1, rc)
      obtain ⟨hm, hsg⟩ := arith_ge a (effB flip b) (effNeg flip b) hnc hs (by rw [hcA]; exact hab)
      rw [hcA] at hm hsg
      have e3 := eval_push_eq [] (.inl 2)
        (fun (v : RegA Ra Rs Rc) => if obsc v.2.2.2.2 = .gt then v.1.getD .pos else .pos)
        (some (sgnSym a), some (sgnSym b), w.1, r, rc)
        (Function.update S (emb id hms (.inl 2))
          (natSyms (a.natAbs - b.natAbs) ++ (fun l => S (emb id hms l)) (.inl 2)))
        (if Lib.ordOf a.natAbs b.natAbs = .gt then sgnSym a else .pos)
        (natSyms (a.natAbs - b.natAbs) ++ S (.inl 2)) (by simp only [hrc]; rfl) (by simp [emb])
      refine ⟨(w.1, r, rc), _, eval_stk (Eval.ite_false hc (Eval.seq e1
        (Eval.ite_false hc2 (Eval.seq e2 e3)))) ?_, ?_⟩
      · rw [show emb id hms (.inl 2) = (.inl 2 : Loc 3 4) from rfl, Function.update_idem,
          intSyms_eq_cons hsg hm, List.cons_append]
      · simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at ht1 ht2 ⊢
        omega

/-- **Signed add / subtract**, from the unsigned contracts' specifications. -/
theorem addSub_runs (hma : ma ≤ 4) (hms : ms ≤ 4) (hmc : mc ≤ 4) {Ca Cs Cc : ℕ}
    {obsc : Rc → Ordering} {Pa : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Ps : Prog (Loc 3 ms) (fun _ => Sym) Rs} {Pc : Prog (Loc 2 mc) (fun _ => Sym) Rc}
    (hA : AddSpec Ca Pa) (hS : SubSpec Cs Ps) (hC : CmpSpec Cc obsc Pc) (flip : Bool)
    (a b res : ℤ) (hres : res = a + effB flip b) (rx ry : List Sym) (S : Loc 3 4 → List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hx : S (.inl 0) = intSyms a ++ rx)
    (hy : S (.inl 1) = intSyms b ++ ry) :
    Runs (addSubProg hma hms hmc obsc Pa Ps Pc flip) S
      (Function.update S (.inl 2) (intSyms res ++ S (.inl 2))) (fun _ => True)
      ((Ca + Cs + Cc + 7) * (bitLen a.natAbs + bitLen b.natAbs + 1)) := by
  subst hres
  refine Runs.of_eval fun v => ?_
  -- pop the signs
  have e1 := eval_pop_int [] (.inl 0) (fun (v : RegA Ra Rs Rc) o => (o, v.2)) v S a rx hx
  have hS1y : Function.update S (.inl 0) (natSyms a.natAbs ++ rx) (.inl 1) = intSyms b ++ ry := by
    simp [hy]
  have e2 := eval_pop_int [] (.inl 1) (fun (v : RegA Ra Rs Rc) o => (v.1, o, v.2.2))
    (some (sgnSym a), v.2) (Function.update S (.inl 0) (natSyms a.natAbs ++ rx)) b ry hS1y
  set S2 := Function.update (Function.update S (.inl 0) (natSyms a.natAbs ++ rx)) (.inl 1)
    (natSyms b.natAbs ++ ry) with hS2
  have hS2x : S2 (.inl 0) = natSyms a.natAbs ++ rx := by simp [hS2]
  have hS2y : S2 (.inl 1) = natSyms b.natAbs ++ ry := by simp [hS2]
  -- the signed core
  obtain ⟨w', t, e3, ht⟩ := addSubCore_eval hma hms hmc hA hS hC flip a b rx ry hrx hry S2
    hS2x hS2y v.2.2
  set S3 := Function.update S2 (.inl 2) (intSyms (a + effB flip b) ++ S2 (.inl 2)) with hS3
  -- push the signs back
  have e4 := eval_push_eq [] (.inl 1) (fun (v : RegA Ra Rs Rc) => v.2.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), w') S3 (sgnSym b) (natSyms b.natAbs ++ ry) rfl
    (by simp [hS3, hS2y])
  have e5 := eval_push_eq [] (.inl 0) (fun (v : RegA Ra Rs Rc) => v.1.getD .pos)
    (some (sgnSym a), some (sgnSym b), w')
    (Function.update S3 (.inl 1) (sgnSym b :: (natSyms b.natAbs ++ ry))) (sgnSym a)
    (natSyms a.natAbs ++ rx) rfl (by simp [hS3, hS2x])
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))) ?_,
    trivial, ?_⟩
  · funext k
    rcases k with ⟨_ | _ | _ | i, hi⟩ | j
    · simp [hS3, hS2, hx, intSyms_append]
    · simp [hS3, hS2, hy, intSyms_append]
    · simp [hS3, hS2]
    · omega
    · simp [hS3, hS2]
  · simp only [Nat.add_mul] at ht ⊢
    omega

end Prog

/-- **Signed add**, given the unsigned add and subtract contracts (compare: `w3_cmpNat`). -/
theorem W3_addInt_holds (ha : W3_addNat) (hs : W3_subNat) : W3_addInt := by
  obtain ⟨Ca, hPa⟩ := ha
  obtain ⟨ma, Ra, _obsa, Pa, hma, hRa, ⟨ra0⟩, hPac, hspA⟩ := hPa ()
  obtain ⟨Cs, hPs⟩ := hs
  obtain ⟨ms, Rs, _obss, Ps, hms, hRs, ⟨rs0⟩, hPsc, hspS⟩ := hPs ()
  obtain ⟨Cc, hPc⟩ := w3_cmpNat
  obtain ⟨mc, Rc, obsc, Pc, hmc, hRc, ⟨rc0⟩, hPcc, hspC⟩ := hPc ()
  refine ⟨Ca + Cs + Cc + 7, fun _ => ⟨4, RegA Ra Rs Rc, fun _ => (),
    addSubProg hma hms hmc obsc Pa Ps Pc false, le_refl _, inferInstance,
    ⟨(none, none, ra0, rs0, rc0)⟩, addSubProg_closed hma hms hmc obsc hPac hPsc hPcc false, ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  exact addSub_runs hma hms hmc hspA hspS hspC false a b (a + b) (by simp [effB]) rx ry S hrx hry
    hx hy

/-- **Signed subtract**, given the unsigned add and subtract contracts (compare: `w3_cmpNat`). -/
theorem W3_subInt_holds (ha : W3_addNat) (hs : W3_subNat) : W3_subInt := by
  obtain ⟨Ca, hPa⟩ := ha
  obtain ⟨ma, Ra, _obsa, Pa, hma, hRa, ⟨ra0⟩, hPac, hspA⟩ := hPa ()
  obtain ⟨Cs, hPs⟩ := hs
  obtain ⟨ms, Rs, _obss, Ps, hms, hRs, ⟨rs0⟩, hPsc, hspS⟩ := hPs ()
  obtain ⟨Cc, hPc⟩ := w3_cmpNat
  obtain ⟨mc, Rc, obsc, Pc, hmc, hRc, ⟨rc0⟩, hPcc, hspC⟩ := hPc ()
  refine ⟨Ca + Cs + Cc + 7, fun _ => ⟨4, RegA Ra Rs Rc, fun _ => (),
    addSubProg hma hms hmc obsc Pa Ps Pc true, le_refl _, inferInstance,
    ⟨(none, none, ra0, rs0, rc0)⟩, addSubProg_closed hma hms hmc obsc hPac hPsc hPcc true, ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  exact addSub_runs hma hms hmc hspA hspS hspC true a b (a - b) (by simp [effB, sub_eq_add_neg])
    rx ry S hrx hry hx hy

#assert_std_axioms sw01_injective f23_injective addSubProg_closed addSubCore_eval addSub_runs
  W3_addInt_holds W3_subInt_holds

end TMFw.W3b
