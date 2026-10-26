import WP.W9a.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WP.W9a.Sweep — the generic SWEEP combinator (`W9_sweep`)

`sweepProg hm κ` runs the node kernel `κ` once per group of `g` consecutive nodes of the level
stream on `S`:

1. push the sweep's own `$` on S′ (`sO`); peek `S`;
2. if the stream is nonempty: copy `g` from `C2` to the private master copy `sG` (the kernel may
   change `C2`), then loop while the top of `S` is not `$`:
   * LOAD (`loadProg`): copy `g` to the working counter `sK`; move `g` nodes from `S` to the
     temporary `sT` (terminators dropped, one counter decrement per node); move `sT` back onto
     `W0`, which restores the orientation (`W0 = groupSyms grp`);
   * run the kernel (registers `R`, first component);
   * EMIT (`emitProg`): move `W0` onto S′ (reversed);
   * peek `S`;

   then drop the master copy;
3. FLIP: move S′ back onto `S` down to the sweep's `$`.

The sweep's private stacks are the scratch stacks `0..3`; the kernel restores every scratch stack, so
they survive it. The register is `R × Option Sym`.

**Cost.** Per group: the kernel, `O(|g|)` for the counter copy, the amortised decrements
(`incSeqCost 6 10 g ≤ 16 g`, and `g ≤` the group's symbols), and three moves of the group's and the
output's symbols. Total `∑ c i + 32·(|⟦xs⟧| + ∑|out i| + M·(|g|+1) + 1)`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section SweepDef

variable {m : ℕ}

/-- S′: the output accumulator of the running sweep (scratch 0). -/
def sO (hm : 4 ≤ m) : BLoc m := .inr ⟨0, by omega⟩
/-- The LOAD temporary (scratch 1). -/
def sT (hm : 4 ≤ m) : BLoc m := .inr ⟨1, by omega⟩
/-- The master copy of the group size `g` (scratch 2). -/
def sG (hm : 4 ≤ m) : BLoc m := .inr ⟨2, by omega⟩
/-- The working counter of a group (scratch 3). -/
def sK (hm : 4 ≤ m) : BLoc m := .inr ⟨3, by omega⟩

variable {R : Type}

/-- LOAD one group: counter `g` on `sK`; move `g` nodes `S → sT` (terminators dropped); move `sT`
back onto `W0`. -/
def loadProg (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (pushC (sK hm) .mark) (.seq (copyBlock (sG hm) (sK hm) (sT hm)) (.seq (pushC (sT hm) .mark)
    (.seq (countLoop (sK hm) (sT hm) (moveUntil (.inl .S) (sT hm) (isSym symNode)))
      (.seq (popR (sK hm)) (moveUntil (sT hm) (.inl .W0) (isSym .mark))))))

/-- EMIT the kernel output onto S′ (reversed). -/
def emitProg (hm : 4 ≤ m) : SProg (BLoc m) := moveUntil (.inl .W0) (sO hm) isNoneR

/-- Copy `g` from `C2` to the master copy `sG`, then look at the stream. -/
def setupProg (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (pushC (sG hm) .mark) (.seq (copyBlock (.inl .C2) (sG hm) (sT hm)) (peekR (.inl .S)))

/-- The loop test: the top of the stream is not `$`. -/
def notLevel (v : R × Option Sym) : Bool := !isSym symLevel v.2

/-- One group: LOAD, kernel, EMIT, peek. -/
def groupBody (hm : 4 ≤ m) (κ : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (liftQ (loadProg hm)) (.seq (liftK κ) (.seq (liftQ (emitProg hm)) (liftQ (peekR (.inl .S)))))

/-- **The sweep combinator.** -/
def sweepProg (hm : 4 ≤ m) (κ : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (liftQ (pushC (sO hm) symLevel))
    (.seq (liftQ (peekR (.inl .S)))
      (.seq (.ite notLevel
          (.seq (liftQ (setupProg hm))
            (.seq (.loop notLevel (groupBody hm κ)) (liftQ (dropUntil (sG hm) (isSym .mark)))))
          (liftQ skip))
        (liftQ (moveUntil (sO hm) (.inl .S) (isSym symLevel)))))

theorem closed_loadProg (hm : 4 ≤ m) : (loadProg hm).Closed :=
  closed_seq (closed_pushC _ _) (closed_seq (closed_copyBlock _ _ _) (closed_seq (closed_pushC _ _)
    (closed_seq (closed_countLoop _ _ (closed_moveUntil _ _ _))
      (closed_seq (closed_popR _) (closed_moveUntil _ _ _)))))

theorem closed_sweepProg (hm : 4 ≤ m) (κ : Prog (BLoc m) (fun _ => Sym) R) (hκ : κ.Closed) :
    (sweepProg hm κ).Closed :=
  closed_seq (closed_liftQ (closed_pushC _ _)) (closed_seq (closed_liftQ (closed_peekR _))
    (closed_seq (closed_ite (closed_seq (closed_liftQ (closed_seq (closed_pushC _ _)
        (closed_seq (closed_copyBlock _ _ _) (closed_peekR _))))
      (closed_seq (closed_loop (closed_seq (closed_liftQ (closed_loadProg hm))
        (closed_seq (closed_liftK hκ) (closed_seq (closed_liftQ (closed_moveUntil _ _ _))
          (closed_liftQ (closed_peekR _))))))
        (closed_liftQ (closed_dropUntil _ _)))) (closed_liftQ closed_skip))
      (closed_liftQ (closed_moveUntil _ _ _))))

end SweepDef

/-! ## LOAD -/

section Load

variable {m : ℕ}

/-- State of the LOAD loop: `done` already moved onto `sT`, `ys` still on `S`, counter `|ys|`. -/
def loadSt (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (after : List Sym)
    (done ys : List (Array (ℤ × ℤ))) : BLoc m → List Sym :=
  Function.update (Function.update (Function.update S0 (.inl .S) (ys.flatMap nodeSyms ++ after))
    (sT hm) ((groupSyms done).reverse ++ Sym.mark :: S0 (sT hm)))
    (sK hm) (natSyms ys.length ++ Sym.mark :: S0 (sK hm))

theorem sum_load_cost : ∀ grp : List (Array (ℤ × ℤ)),
    (grp.map (fun y => 3 * (blkE y.toList).length + 2)).sum =
      3 * (groupSyms grp).length + 2 * grp.length
  | [] => rfl
  | y :: grp => by
    rw [List.map_cons, List.sum_cons, sum_load_cost grp, groupSyms_cons, List.length_append,
      List.length_cons]
    ring

theorem natSyms_zero' : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

/-- **LOAD**, exact: the group `grp` moves from `S` to `W0` (terminators dropped), every scratch
stack is restored. -/
theorem loadProg_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (v : Option Sym)
    (grp : List (Array (ℤ × ℤ))) (after G0 : List Sym)
    (hS : S0 (.inl .S) = grp.flatMap nodeSyms ++ after)
    (hG : S0 (sG hm) = natSyms grp.length ++ Sym.mark :: G0) :
    ∃ v', Eval [] (loadProg hm) ⟨v, S0⟩
      ⟨v', Function.update (Function.update S0 (.inl .S) after) (.inl .W0)
        (groupSyms grp ++ S0 (.inl .W0))⟩
      (7 * bitLen grp.length + 14 + incSeqCost 6 10 grp.length + 6 * (groupSyms grp).length +
        2 * grp.length) := by
  have hGK : sG hm ≠ sK hm := by simp [sG, sK]
  have hGT : sG hm ≠ sT hm := by simp [sG, sT]
  have hKT : sK hm ≠ sT hm := by simp [sK, sT]
  have hST : (.inl .S : BLoc m) ≠ sT hm := by simp [sT]
  have hTW : sT hm ≠ (.inl .W0 : BLoc m) := by simp [sT]
  -- push the counter guard
  have e1 : Eval [] (pushC (sK hm) .mark) ⟨v, S0⟩
      ⟨v, Function.update S0 (sK hm) (.mark :: S0 (sK hm))⟩ 1 := Eval.push _ _ _ _ _
  -- copy `g` onto the counter
  have hS1G : Function.update S0 (sK hm) (.mark :: S0 (sK hm)) (sG hm) =
      (encodeNat grp.length).map Sym.bit ++ Sym.mark :: G0 := by
    rw [Function.update_of_ne hGK]
    exact hG
  have e2 := copyBlock_eval hGK hGT hKT [] v (encodeNat grp.length) (Sym.mark :: G0) _
    (TermOK.cons rfl _) hS1G
  -- push the temporary guard
  have e3 := Eval.push [] (sT hm) (fun _ => Sym.mark) (some Sym.mark)
    (Function.update (Function.update S0 (sK hm) (.mark :: S0 (sK hm))) (sK hm)
      ((encodeNat grp.length).map Sym.bit ++
        Function.update S0 (sK hm) (.mark :: S0 (sK hm)) (sK hm)))
  -- the loop
  let P : List (Array (ℤ × ℤ)) → (BLoc m → List Sym) → Prop := fun ys S =>
    ∃ done, done ++ ys = grp ∧ S = loadSt hm S0 after done ys
  have hP0 : P grp (Function.update (Function.update (Function.update S0 (sK hm)
      (.mark :: S0 (sK hm))) (sK hm) ((encodeNat grp.length).map Sym.bit ++
        Function.update S0 (sK hm) (.mark :: S0 (sK hm)) (sK hm))) (sT hm)
      ((fun _ => Sym.mark) (some Sym.mark) :: Function.update (Function.update S0 (sK hm)
        (.mark :: S0 (sK hm))) (sK hm) ((encodeNat grp.length).map Sym.bit ++
          Function.update S0 (sK hm) (.mark :: S0 (sK hm)) (sK hm)) (sT hm))) := by
    refine ⟨[], rfl, ?_⟩
    funext k
    simp only [loadSt, Function.update_apply, groupSyms_nil, List.reverse_nil, List.nil_append,
      natSyms]
    split_ifs <;> simp_all
  have hK : ∀ ys S, P ys S → S (sK hm) = natSyms ys.length ++ (Sym.mark :: S0 (sK hm)) := by
    rintro ys S ⟨done, -, rfl⟩
    simp [loadSt]
  have hbody : ∀ y ys S v, P (y :: ys) S → ∃ v' S', Eval [] (moveUntil (.inl .S) (sT hm)
      (isSym symNode)) ⟨v, Function.update S (sK hm) (natSyms ys.length ++ Sym.mark ::
        S0 (sK hm))⟩ ⟨v', S'⟩ (3 * (blkE y.toList).length + 2) ∧ P ys S' := by
    rintro y ys S v ⟨done, hdone, rfl⟩
    have hsrc : Function.update (loadSt hm S0 after done (y :: ys)) (sK hm)
        (natSyms ys.length ++ Sym.mark :: S0 (sK hm)) (.inl .S) =
        blkE y.toList ++ symNode :: (ys.flatMap nodeSyms ++ after) := by
      simp [loadSt, sK, sT, nodeSyms, List.flatMap_cons]
    refine ⟨_, _, moveUntil_eval hST (isSym symNode) v (blkE y.toList)
      (symNode :: (ys.flatMap nodeSyms ++ after)) _ (fun x hx => isSym_some_of_ne
        (fun e => tag_not_mem_blkE 0 _ (e ▸ hx))) (isSym_some_self _) hsrc,
      ⟨done ++ [y], by rw [List.append_assoc]; exact hdone, ?_⟩⟩
    funext k
    simp only [loadSt, Function.update_apply, groupSyms_append, groupSyms_cons, groupSyms_nil,
      List.append_nil, List.reverse_append, List.tail_cons]
    split_ifs <;> simp_all [sK, sT]
  obtain ⟨v4, S4, e4, done, hdone, hS4⟩ := countLoop_eval hKT _ P (Sym.mark :: S0 (sK hm))
    (TermOK.cons rfl _) (fun y => 3 * (blkE y.toList).length + 2) hK hbody grp _ (some .mark) hP0
  rw [List.append_nil] at hdone
  subst hdone
  subst hS4
  -- pop the counter guard
  have hS4K : loadSt hm S0 after done [] (sK hm) = Sym.mark :: S0 (sK hm) := by
    simp [loadSt, natSyms_zero']
  have e5 : Eval [] (popR (sK hm)) ⟨v4, loadSt hm S0 after done []⟩
      ⟨some .mark, Function.update (loadSt hm S0 after done []) (sK hm) (S0 (sK hm))⟩ 1 := by
    refine (Eval.pop [] (sK hm) (fun _ o => o) _ _).of_eq ?_ rfl
    rw [hS4K]
    rfl
  -- move the group back onto `W0`
  have hS5T : Function.update (loadSt hm S0 after done []) (sK hm) (S0 (sK hm)) (sT hm) =
      (groupSyms done).reverse ++ Sym.mark :: S0 (sT hm) := by
    rw [Function.update_of_ne (Ne.symm hKT)]
    simp [loadSt, sK, sT]
  have e6 := moveUntil_eval hTW (isSym .mark) (some .mark) (groupSyms done).reverse
    (Sym.mark :: S0 (sT hm)) _ (fun x hx => isSym_some_of_ne (fun e => mark_not_mem_blkE _
      (by rw [groupSyms] at hx; rw [← e]; exact List.mem_reverse.1 hx))) (isSym_some_self _) hS5T
  refine ⟨some .mark, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    e6))))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [loadSt, Function.update_apply, List.flatMap_nil, List.nil_append,
      List.reverse_reverse, List.tail_cons]
    split_ifs <;> simp_all [sK, sT]
  · rw [sum_load_cost, List.length_reverse, bitLen]
    ring

end Load

/-! ## One group -/

section Group

variable {m : ℕ} {R : Type}

/-- Per-group cost bound of the sweep. -/
def grpCost (c : ℕ → ℕ) (g : ℕ) (xs : List (Array (ℤ × ℤ))) (out : ℕ → List Sym) (i : ℕ) : ℕ :=
  c i + 7 * bitLen g + 17 + incSeqCost 6 10 g + 6 * (groupSyms (groupAt g xs i)).length +
    2 * g + 3 * (out i).length

/-- Loop invariant of the sweep after `i` groups. -/
def SwInv (hm : 4 ≤ m) (g : ℕ) (xs : List (Array (ℤ × ℤ))) (out : ℕ → List Sym)
    (J : ℕ → (LB → List Sym) → Prop) (σ : BLoc m → List Sym) (rest : List Sym) (i : ℕ)
    (s : St (BLoc m) (fun _ => Sym) (R × Option Sym)) : Prop :=
  s.stk (.inl .S) = (xs.drop (i * g)).flatMap nodeSyms ++ symLevel :: rest ∧
  s.stk (.inl .W0) = [] ∧
  s.stk (sO hm) = ((List.range i).flatMap out).reverse ++ symLevel :: σ (sO hm) ∧
  s.stk (sG hm) = natSyms g ++ Sym.mark :: σ (sG hm) ∧
  (∀ j : Fin m, (.inr j : BLoc m) ≠ sO hm → (.inr j : BLoc m) ≠ sG hm →
    s.stk (.inr j) = σ (.inr j)) ∧
  J i (outer s.stk) ∧
  s.var.2 = (s.stk (.inl .S)).head?

theorem groupBody_triple (hm : 4 ≤ m) (κ : Prog (BLoc m) (fun _ => Sym) R) (g M : ℕ)
    (xs : List (Array (ℤ × ℤ))) (out : ℕ → List Sym) (J : ℕ → (LB → List Sym) → Prop)
    (c : ℕ → ℕ) (hlen : xs.length = g * M)
    (hκ : ∀ i < M, ∀ σ : BLoc m → List Sym, J i (outer σ) →
      σ (.inl .W0) = groupSyms (groupAt g xs i) →
      Triple [] (fun s => s.stk = σ) κ
        (fun s => s.stk (.inl .W0) = out i ∧ s.stk (.inl .S) = σ (.inl .S) ∧
          (∀ j, s.stk (.inr j) = σ (.inr j)) ∧ J (i + 1) (outer s.stk)) (c i))
    (σ : BLoc m → List Sym) (rest : List Sym) (i : ℕ) (hi : i < M) :
    Triple [] (SwInv hm g xs out J σ rest i) (groupBody hm κ)
      (SwInv hm g xs out J σ rest (i + 1)) (grpCost c g xs out i) := by
  rintro ⟨⟨r, q⟩, S⟩ ⟨hS, hW, hO, hG, hsc, hJ, -⟩
  simp only at hS hW hO hG hsc hJ
  have hglen := length_groupAt g M i xs hlen hi
  have hS' : S (.inl .S) = (groupAt g xs i).flatMap nodeSyms ++
      ((xs.drop ((i + 1) * g)).flatMap nodeSyms ++ symLevel :: rest) := by
    rw [hS, drop_groupAt g i xs, List.flatMap_append, List.append_assoc]
  -- LOAD
  obtain ⟨v1, e1⟩ := loadProg_eval hm S q (groupAt g xs i) _ (σ (sG hm)) hS'
    (by rw [hglen]; exact hG)
  rw [hglen] at e1
  generalize hS1 : Function.update (Function.update S (.inl .S)
      ((xs.drop ((i + 1) * g)).flatMap nodeSyms ++ symLevel :: rest)) (.inl .W0)
      (groupSyms (groupAt g xs i) ++ S (.inl .W0)) = S1 at e1
  have hS1S : S1 (.inl .S) = (xs.drop ((i + 1) * g)).flatMap nodeSyms ++ symLevel :: rest := by
    rw [← hS1, Function.update_of_ne (by simp), Function.update_self]
  have hS1W : S1 (.inl .W0) = groupSyms (groupAt g xs i) := by
    rw [← hS1, Function.update_self, hW, List.append_nil]
  have hS1r : ∀ j, S1 (.inr j) = S (.inr j) := by
    intro j
    rw [← hS1, Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  have hJ1 : J i (outer S1) := by
    rw [← hS1, outer_update_W0, outer_update_S]
    exact hJ
  -- kernel
  obtain ⟨s2, t2, e2, ⟨hW2, hS2, hsc2, hJ2⟩, ht2⟩ := hκ i hi S1 hJ1 hS1W ⟨r, S1⟩ rfl
  -- EMIT
  have hWO : (.inl .W0 : BLoc m) ≠ sO hm := by simp [sO]
  have e3 := moveUntil_eval hWO isNoneR v1 (out i) [] s2.stk (fun _ _ => rfl) rfl
    (by rw [hW2, List.append_nil])
  generalize hS3 : Function.update (Function.update s2.stk (.inl .W0) [].tail) (sO hm)
      ((out i).reverse ++ s2.stk (sO hm)) = S3 at e3
  -- peek
  have e4 := Eval.peek (Γ := fun _ => Sym) [] (.inl .S : BLoc m) (fun _ o => o) [].head? S3
  refine ⟨_, _, Eval.seq (liftQ_eval e1 (r, q) rfl) (Eval.seq (liftK_eval e2 v1)
    (Eval.seq (liftQ_eval e3 (s2.var, v1) rfl) (liftQ_eval e4 (s2.var, [].head?) rfl))), ?_, ?_⟩
  · have hOS : sO hm ≠ (.inl .S : BLoc m) := by simp [sO]
    have hOW : sO hm ≠ (.inl .W0 : BLoc m) := by simp [sO]
    have hGO : sG hm ≠ sO hm := by simp [sG, sO]
    have hs2r : ∀ j, s2.stk (.inr j) = S (.inr j) := fun j => (hsc2 j).trans (hS1r j)
    have hS3S : S3 (.inl .S) = (xs.drop ((i + 1) * g)).flatMap nodeSyms ++ symLevel :: rest := by
      rw [← hS3, Function.update_of_ne (Ne.symm hOS), Function.update_of_ne (by simp), hS2, hS1S]
    refine ⟨hS3S, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show S3 (.inl .W0) = []
      rw [← hS3, Function.update_of_ne (Ne.symm hOW), Function.update_self]
      rfl
    · show S3 (sO hm) = _
      have h2O : s2.stk (sO hm) = S (sO hm) := hs2r _
      rw [← hS3, Function.update_self, h2O, hO, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.reverse_append, List.append_assoc]
    · show S3 (sG hm) = _
      have h2G : s2.stk (sG hm) = S (sG hm) := hs2r _
      rw [← hS3, Function.update_of_ne hGO, Function.update_of_ne (by simp [sG]), h2G, hG]
    · intro j hjO hjG
      show S3 (.inr j) = _
      rw [← hS3, Function.update_of_ne hjO, Function.update_of_ne (by simp), hs2r j,
        hsc j hjO hjG]
    · show J (i + 1) (outer S3)
      rw [← hS3, sO, outer_update_inr, outer_update_W0]
      exact hJ2
  · unfold grpCost
    omega

end Group

/-! ## The sweep -/

section Main

variable {m : ℕ} {R : Type}

/-- Setup, exact: `g` is copied from `C2` to the master copy `sG` (above a guard). -/
theorem setupProg_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (v : Option Sym) (g : ℕ)
    (r2 : List Sym) (hC2 : S0 (.inl .C2) = natSyms g ++ r2) (hr2 : TermOK r2) :
    Eval [] (setupProg hm) ⟨v, S0⟩
      ⟨(S0 (.inl .S)).head?, Function.update S0 (sG hm) (natSyms g ++ Sym.mark :: S0 (sG hm))⟩
      (7 * bitLen g + 9) := by
  have hCG : (.inl .C2 : BLoc m) ≠ sG hm := by simp [sG]
  have hCT : (.inl .C2 : BLoc m) ≠ sT hm := by simp [sT]
  have hGT : sG hm ≠ sT hm := by simp [sG, sT]
  have hSG : (.inl .S : BLoc m) ≠ sG hm := by simp [sG]
  have e1 : Eval [] (pushC (sG hm) .mark) ⟨v, S0⟩
      ⟨v, Function.update S0 (sG hm) (.mark :: S0 (sG hm))⟩ 1 := Eval.push _ _ _ _ _
  have e2 := copyBlock_eval hCG hCT hGT [] v (encodeNat g) r2
    (Function.update S0 (sG hm) (.mark :: S0 (sG hm))) hr2
    (by rw [Function.update_of_ne hCG]; exact hC2)
  rw [Function.update_self, Function.update_idem] at e2
  have e3 := Eval.peek (Γ := fun _ => Sym) [] (.inl .S : BLoc m) (fun _ o => o) (some Sym.mark)
    (Function.update S0 (sG hm) ((encodeNat g).map Sym.bit ++ Sym.mark :: S0 (sG hm)))
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_
  · rw [Function.update_of_ne hSG]
    rfl
  · simp only [bitLen]
    omega

/-- Cost of the nonempty sweep. -/
theorem sweep_cost (c : ℕ → ℕ) (g M : ℕ) (xs : List (Array (ℤ × ℤ))) (out : ℕ → List Sym)
    (hlen : xs.length = g * M) (hM : 0 < M) :
    9 * bitLen g + sumTo M (grpCost c g xs out) + M + 3 * ((List.range M).flatMap out).length +
      18 ≤
    sumTo M c + 32 * ((streamSyms xs).length + sumTo M (fun i => (out i).length) +
      M * (bitLen g + 1) + 1) := by
  have hsum : ∀ n, sumTo n (grpCost c g xs out) = sumTo n c +
      n * (7 * bitLen g + 17 + incSeqCost 6 10 g + 2 * g) +
      6 * sumTo n (fun i => (groupSyms (groupAt g xs i)).length) +
      3 * sumTo n (fun i => (out i).length) := by
    intro n
    induction n with
    | zero => simp [sumTo_zero]
    | succ n ih =>
      rw [sumTo_succ, ih, sumTo_succ, sumTo_succ, sumTo_succ]
      unfold grpCost
      ring
  have hout := sumTo_length_flatMap out M
  have hst := length_streamSyms xs
  have hinc := incSeqCost_le 6 10 g
  have hMinc : M * incSeqCost 6 10 g ≤ 16 * (M * g) := by
    calc M * incSeqCost 6 10 g ≤ M * ((6 + 10) * g) := Nat.mul_le_mul_left M hinc
      _ = 16 * (M * g) := by ring
  have hB : bitLen g ≤ M * bitLen g := Nat.le_mul_of_pos_left _ hM
  have hMg : M * g = xs.length := by rw [hlen, Nat.mul_comm]
  rw [hsum, sumTo_groupSyms g M xs hlen, ← hout, hst]
  nlinarith

theorem W9_sweep_holds : W9_sweep := by
  refine ⟨32, fun m R hm => ⟨Option Sym, sweepProg hm, inferInstance, ⟨none⟩,
    fun κ hκc => closed_sweepProg hm κ hκc, ?_⟩⟩
  intro κ g M xs out J c hg hlen hout hκ σ rest r2 hS hW0 hC2 hr2 hJ0
  rintro ⟨⟨r, q⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  have hOS : sO hm ≠ (.inl .S : BLoc m) := by simp [sO]
  unfold sweepProg
  -- push the sweep's `$` on S′, peek
  have e1 : Eval [] (pushC (sO hm) symLevel) ⟨q, σ⟩
      ⟨q, Function.update σ (sO hm) (symLevel :: σ (sO hm))⟩ 1 := Eval.push _ _ _ _ _
  generalize hS1 : Function.update σ (sO hm) (symLevel :: σ (sO hm)) = S1 at e1
  have hS1S : S1 (.inl .S) = σ (.inl .S) := by rw [← hS1, Function.update_of_ne (Ne.symm hOS)]
  have hS1O : S1 (sO hm) = symLevel :: σ (sO hm) := by rw [← hS1, Function.update_self]
  have hS1o : ∀ k, k ≠ sO hm → S1 k = σ k := fun k hk => by rw [← hS1, Function.update_of_ne hk]
  have e2 := Eval.peek (Γ := fun _ => Sym) [] (.inl .S : BLoc m) (fun _ o => o) q S1
  by_cases hM : M = 0
  · -- the empty level
    subst hM
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, Nat.mul_zero])
    subst hxs
    have hhead : (S1 (.inl .S)).head? = some symLevel := by
      rw [hS1S, hS]
      rfl
    have e3 : Eval [] (Prog.ite notLevel
        (.seq (liftQ (setupProg hm)) (.seq (.loop notLevel (groupBody hm κ))
          (liftQ (dropUntil (sG hm) (isSym .mark))))) (liftQ skip))
        ⟨(r, (S1 (.inl .S)).head?), S1⟩ ⟨(r, (S1 (.inl .S)).head?), S1⟩ 2 :=
      Eval.ite_false (by simp [notLevel, hhead, isSym]) (liftQ_eval (skip_eval [] _) _ rfl)
    have e4 := moveUntil_eval hOS (isSym symLevel) (S1 (.inl .S)).head? []
      (symLevel :: σ (sO hm)) S1 (fun _ h => by simp at h) (isSym_some_self _)
      hS1O
    have hfin : Function.update (Function.update S1 (sO hm) (σ (sO hm))) (.inl .S)
        (S1 (.inl .S)) = σ := by
      funext k
      by_cases hk1 : k = .inl .S
      · subst hk1
        rw [Function.update_self, hS1S]
      · rw [Function.update_of_ne hk1]
        by_cases hk2 : k = sO hm
        · subst hk2
          rw [Function.update_self]
        · rw [Function.update_of_ne hk2, hS1o k hk2]
    refine ⟨⟨(r, some symLevel), σ⟩, _, (Eval.seq (liftQ_eval e1 (r, q) rfl)
      (Eval.seq (liftQ_eval e2 (r, q) rfl) (Eval.seq e3 (liftQ_eval e4 _ rfl)))).of_eq
        (congrArg₂ St.mk rfl hfin) rfl, ⟨?_, hW0, fun _ => rfl, hJ0⟩, ?_⟩
    · show σ (.inl .S) = _
      rw [hS]
      rfl
    · simp [sumTo_zero, streamSyms]
  · -- a nonempty level
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hSG : (.inl .S : BLoc m) ≠ sG hm := by simp [sG]
    have hGO : sG hm ≠ sO hm := by simp [sG, sO]
    obtain ⟨x, xs', hxs⟩ : ∃ x xs', xs = x :: xs' := by
      cases xs with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen.symm (Nat.ne_of_gt (Nat.mul_pos hg hMpos))
      | cons x xs' => exact ⟨x, xs', rfl⟩
    have hhead : notLevel (r, (S1 (.inl .S)).head?) = true := by
      have h := head_ne_level x (xs'.flatMap nodeSyms ++ symLevel :: rest)
      rw [hS1S, hS, hxs]
      simp only [notLevel, isSym, streamSyms, List.flatMap_cons, List.append_assoc]
      simpa using h
    -- setup
    have es := setupProg_eval hm S1 (S1 (.inl .S)).head? g r2
      (by rw [hS1o _ (by simp [sO])]; exact hC2) hr2
    generalize hS2 : Function.update S1 (sG hm) (natSyms g ++ Sym.mark :: S1 (sG hm)) = S2 at es
    have hS2G : S2 (sG hm) = natSyms g ++ Sym.mark :: σ (sG hm) := by
      rw [← hS2, Function.update_self, hS1o _ hGO]
    have hS2g : ∀ k, k ≠ sG hm → S2 k = S1 k := fun k hk => by
      rw [← hS2, Function.update_of_ne hk]
    -- the group loop
    have hInv0 : SwInv (R := R) hm g xs out J σ rest 0 ⟨(r, (S1 (.inl .S)).head?), S2⟩ := by
      refine ⟨?_, ?_, ?_, hS2G, ?_, ?_, ?_⟩
      · show S2 (.inl .S) = _
        rw [hS2g _ hSG, hS1S, hS, Nat.zero_mul, List.drop_zero]
        simp [streamSyms]
      · show S2 (.inl .W0) = []
        rw [hS2g _ (by simp [sG]), hS1o _ (by simp [sO])]
        exact hW0
      · show S2 (sO hm) = _
        rw [hS2g _ (Ne.symm hGO), hS1O]
        rfl
      · intro j hjO hjG
        show S2 (.inr j) = _
        rw [hS2g _ hjG, hS1o _ hjO]
      · show J 0 (outer S2)
        rw [← hS2, ← hS1, sG, sO, outer_update_inr, outer_update_inr]
        exact hJ0
      · show (S1 (.inl .S)).head? = (S2 (.inl .S)).head?
        rw [hS2g _ hSG]
    have hcont : ∀ i < M, ∀ s, SwInv (R := R) hm g xs out J σ rest i s →
        notLevel s.var = true := by
      rintro i hi s ⟨hSi, -, -, -, -, -, hv⟩
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil (show groupAt g xs i ≠ [] by
        intro h
        have := length_groupAt g M i xs hlen hi
        rw [h, List.length_nil] at this
        omega)
      have h := head_ne_level y ((ys ++ xs.drop ((i + 1) * g)).flatMap nodeSyms ++ symLevel :: rest)
      simp only [notLevel]
      rw [hv, hSi, drop_groupAt g i xs, hy]
      simp only [isSym, List.cons_append, List.flatMap_cons, List.append_assoc]
      simpa [List.append_assoc] using h
    have hstop : ∀ s, SwInv (R := R) hm g xs out J σ rest M s → notLevel s.var = false := by
      rintro s ⟨hSi, -, -, -, -, -, hv⟩
      simp only [notLevel]
      rw [hv, hSi, drop_all g M xs hlen]
      simp [isSym]
    obtain ⟨sM, tM, eM, ⟨hSM, hWM, hOM, hGM, hscM, hJM, -⟩, htM⟩ :=
      Triple.loop_up (I := SwInv (R := R) hm g xs out J σ rest) (B := grpCost c g xs out) M
        (fun i hi => groupBody_triple hm κ g M xs out J c hlen hκ σ rest i hi) hcont hstop
        ⟨(r, (S1 (.inl .S)).head?), S2⟩ hInv0
    -- teardown
    have hdg : ∀ x ∈ natSyms g, isSym .mark (some x) = false := by
      intro x hx
      simp only [natSyms, List.mem_map] at hx
      obtain ⟨b, -, rfl⟩ := hx
      exact isSym_some_of_ne (fun h => by cases h)
    have et := dropUntil_eval (src := sG hm) (isSym .mark) sM.var.2 (natSyms g)
      (Sym.mark :: σ (sG hm)) sM.stk hdg (isSym_some_self _) hGM
    generalize hS5 : Function.update sM.stk (sG hm) (Sym.mark :: σ (sG hm)).tail = S5 at et
    have hS5G : S5 (sG hm) = σ (sG hm) := by rw [← hS5, Function.update_self]; rfl
    have hS5g : ∀ k, k ≠ sG hm → S5 k = sM.stk k := fun k hk => by
      rw [← hS5, Function.update_of_ne hk]
    -- flip
    have hdo : ∀ x ∈ ((List.range M).flatMap out).reverse, isSym symLevel (some x) = false := by
      intro x hx
      rw [List.mem_reverse, List.mem_flatMap] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact isSym_some_of_ne (fun h => hout i (List.mem_range.1 hi) (h ▸ hxi))
    have ef := moveUntil_eval hOS (isSym symLevel) (some .mark)
      ((List.range M).flatMap out).reverse (symLevel :: σ (sO hm)) S5 hdo (isSym_some_self _)
      (by rw [hS5g _ (Ne.symm hGO)]; exact hOM)
    refine ⟨_, _, Eval.seq (liftQ_eval e1 (r, q) rfl) (Eval.seq (liftQ_eval e2 (r, q) rfl)
      (Eval.seq (Eval.ite_true hhead (Eval.seq (liftQ_eval es _ rfl)
        (Eval.seq eM (liftQ_eval et sM.var rfl)))) (liftQ_eval ef _ rfl))), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show Function.update (Function.update S5 (sO hm) (σ (sO hm))) (.inl .S)
          (((List.range M).flatMap out).reverse.reverse ++ S5 (.inl .S)) (.inl .S) = _
        rw [Function.update_self, List.reverse_reverse, hS5g _ hSG, hSM, drop_all g M xs hlen]
        rfl
      · show Function.update (Function.update S5 (sO hm) (σ (sO hm))) (.inl .S)
          (((List.range M).flatMap out).reverse.reverse ++ S5 (.inl .S)) (.inl .W0) = []
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp [sO]),
          hS5g _ (by simp [sG]), hWM]
      · intro j
        show Function.update (Function.update S5 (sO hm) (σ (sO hm))) (.inl .S)
          (((List.range M).flatMap out).reverse.reverse ++ S5 (.inl .S)) (.inr j) = σ (.inr j)
        rw [Function.update_of_ne (by simp)]
        by_cases hjO : (.inr j : BLoc m) = sO hm
        · rw [hjO, Function.update_self]
        · rw [Function.update_of_ne hjO]
          by_cases hjG : (.inr j : BLoc m) = sG hm
          · rw [hjG, hS5G]
          · rw [hS5g _ hjG, hscM j hjO hjG]
      · show J M (outer (Function.update (Function.update S5 (sO hm) (σ (sO hm))) (.inl .S)
          (((List.range M).flatMap out).reverse.reverse ++ S5 (.inl .S))))
        rw [outer_update_S, sO, outer_update_inr, ← hS5, sG, outer_update_inr]
        exact hJM
    · have hcost := sweep_cost c g M xs out hlen hMpos
      rw [length_natSyms, List.length_reverse] at *
      linarith

end Main

#assert_std_axioms loadProg_eval groupBody_triple setupProg_eval sweep_cost W9_sweep_holds

end WP.W9a
