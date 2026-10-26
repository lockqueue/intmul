import WP.W3.Loop

/-!
# WP.W3.AddSub — unsigned add / subtract: `W3_addNat_holds`, `W3_subNat_holds`

`addSubProg f` over `Loc 3 3` (registers `AReg`):
1. guard `kTX`, `kTY`, `kT` with `mark`, push the initial carry `0` on `kT`, peek `kX`, `kY`;
2. `ripLoop f` (`max |A| |B|` steps): operand bits move to `kTX`, `kTY`; out bits and the final
   carry pile up on `kT` (MSB on top);
3. `emitNorm kT kZ`: skip high zeros, push the canonical result on `kZ`, consume the mark;
4. `moveBits kTX kX`, `moveBits kTY kY`: restore the operands, consume the marks.

Exact cost `≤ 18·(|a| + |b|) + 17`; contract constant `C = 20` for both.
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The one-symbol register of the library macros, inside `AReg`. -/
def lensR : Lens AReg (Option Sym) := Lens.fst (Option Sym) (Option Sym × Bool)

/-- `z += a ∘ b` for the ripple bit function `f` (`addBit`: sum, `subBit`: difference). -/
def addSubProg (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .seq (.push kTX fun _ => .mark)
  (.seq (.push kTY fun _ => .mark)
  (.seq (.push kT fun _ => .mark)
  (.seq (.push kT fun _ => .bit false)
  (.seq peekX
  (.seq peekY
  (.seq (ripLoop f)
  (.seq ((emitNorm kT kZ).liftRegs lensR)
  (.seq ((moveBits kTX kX).liftRegs lensR)
    ((moveBits kTY kY).liftRegs lensR)))))))))

theorem addSubProg_closed (f : Bool → Bool → Bool → Bool × Bool) : (addSubProg f).Closed :=
  closed_of_noRec rfl

theorem addSubProg_eval (f : Bool → Bool → Bool → Bool × Bool) (A B : List Bool)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (S : Loc 3 3 → List Sym)
    (hx : S kX = A.map Sym.bit ++ rx) (hy : S kY = B.map Sym.bit ++ ry) (v : AReg) :
    ∃ v' t, Eval [] (addSubProg f) ⟨v, S⟩
      ⟨v', Function.update S kZ
        ((encodeNat (bitsVal (rip f (max A.length B.length) false A B))).map Sym.bit ++ S kZ)⟩ t ∧
      t ≤ 18 * (A.length + B.length) + 17 := by
  have e1 := eval_push_eq [] kTX (fun (_ : AReg) => Sym.mark) v S .mark (S kTX) rfl rfl
  set S1 := Function.update S kTX (.mark :: S kTX) with hS1
  have e2 := eval_push_eq [] kTY (fun (_ : AReg) => Sym.mark) v S1 .mark (S kTY) rfl
    (by simp [hS1])
  set S2 := Function.update S1 kTY (.mark :: S kTY) with hS2
  have e3 := eval_push_eq [] kT (fun (_ : AReg) => Sym.mark) v S2 .mark (S kT) rfl
    (by simp [hS2, hS1])
  set S3 := Function.update S2 kT (.mark :: S kT) with hS3
  have e4 := eval_push_eq [] kT (fun (_ : AReg) => Sym.bit false) v S3 (.bit false)
    (.mark :: S kT) rfl (by simp [hS3])
  set S4 := Function.update S3 kT (.bit false :: .mark :: S kT) with hS4
  have hx4 : S4 kX = A.map Sym.bit ++ rx := by simp [hS4, hS3, hS2, hS1, hx]
  have hy4 : S4 kY = B.map Sym.bit ++ ry := by simp [hS4, hS3, hS2, hS1, hy]
  have e5 := eval_peek_eq [] kX (fun (v : AReg) o => (o, v.2)) v S4 (A.map Sym.bit ++ rx).head?
    (by rw [hx4])
  have e6 := eval_peek_eq [] kY (fun (v : AReg) o => (v.1, o, v.2.2))
    ((A.map Sym.bit ++ rx).head?, v.2) S4 (B.map Sym.bit ++ ry).head? (by rw [hy4])
  obtain ⟨w', t7, ht7, e7⟩ := ripLoop_eval f rx ry (.mark :: S kT) hrx hry
    (max A.length B.length) A B false [] S4 v.2.2 rfl hx4 hy4 (by simp [hS4])
  set n := max A.length B.length with hn
  set S7 := Function.update (Function.update (Function.update (Function.update
    (Function.update S4 kX rx) kY ry) kTX (A.reverse.map Sym.bit ++ S4 kTX))
    kTY (B.reverse.map Sym.bit ++ S4 kTY)) kT
    (((rip f n false A B).reverse ++ []).map Sym.bit ++ (.mark :: S kT)) with hS7
  have hT7 : S7 kT = (rip f n false A B).reverse.map Sym.bit ++ (.mark :: S kT) := by
    simp [hS7]
  have e8 := Eval.liftRegs lensR (emitNorm_eval (t := kT) (d := kZ) (by decide) [] rx.head?
    (rip f n false A B).reverse (.mark :: S kT) S7 (TermOK.cons rfl _) hT7)
    (rx.head?, ry.head?, w') rfl
  set S8 := Function.update (Function.update S7 kT (Sym.mark :: S kT).tail) kZ
    ((encodeNat (bitsVal (rip f n false A B).reverse.reverse)).map Sym.bit ++ S7 kZ) with hS8
  have hTX8 : S8 kTX = A.reverse.map Sym.bit ++ (.mark :: S kTX) := by
    simp [hS8, hS7, hS4, hS3, hS2, hS1]
  have e9 := Eval.liftRegs lensR (moveBits_eval (src := kTX) (dst := kX) (by decide) []
    (some .mark) A.reverse (.mark :: S kTX) S8 (TermOK.cons rfl _) hTX8)
    (some .mark, ry.head?, w') rfl
  set S9 := Function.update (Function.update S8 kTX (Sym.mark :: S kTX).tail) kX
    (A.reverse.reverse.map Sym.bit ++ S8 kX) with hS9
  have hTY9 : S9 kTY = B.reverse.map Sym.bit ++ (.mark :: S kTY) := by
    simp [hS9, hS8, hS7, hS4, hS3, hS2, hS1]
  have e10 := Eval.liftRegs lensR (moveBits_eval (src := kTY) (dst := kY) (by decide) []
    (some .mark) B.reverse (.mark :: S kTY) S9 (TermOK.cons rfl _) hTY9)
    (some .mark, ry.head?, w') rfl
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 e10))))))))) ?_, ?_⟩
  · apply stk_ext33 <;> simp [hS9, hS8, hS7, hS4, hS3, hS2, hS1, hx, hy]
  · have hlen := length_dropWhile_le' (fun b => !b) (rip f n false A B).reverse
    have hr := length_rip f n false A B
    have hmax : n ≤ A.length + B.length := by omega
    simp only [List.length_reverse] at hlen ⊢
    omega

/-- **add** `z += a + b`, cost `20·(|a| + |b| + 1)`. -/
theorem W3_addNat_holds : W3_addNat := by
  refine ⟨20, fun _ => ⟨3, AReg, fun _ => (), addSubProg addBit, by decide, inferInstance,
    ⟨(none, none, false)⟩, addSubProg_closed addBit, ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := addSubProg_eval addBit (encodeNat a) (encodeNat b) rx ry hrx hry S hx
    hy v
  have h0 : false.toNat = 0 := rfl
  have hval : bitsVal (rip addBit (max (encodeNat a).length (encodeNat b).length) false
      (encodeNat a) (encodeNat b)) = a + b := by
    rw [bitsVal_rip_add (max (encodeNat a).length (encodeNat b).length) false (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _), bitsVal_encodeNat, bitsVal_encodeNat,
      h0, Nat.add_zero]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

/-- **subtract** `z += a - b` for `b ≤ a`, cost `20·(|a| + |b| + 1)`. -/
theorem W3_subNat_holds : W3_subNat := by
  refine ⟨20, fun _ => ⟨3, AReg, fun _ => (), addSubProg subBit, by decide, inferInstance,
    ⟨(none, none, false)⟩, addSubProg_closed subBit, ?_⟩⟩
  intro a b rx ry S hrx hry hab hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := addSubProg_eval subBit (encodeNat a) (encodeNat b) rx ry hrx hry S hx
    hy v
  have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
    rw [bitsVal_encodeNat, bitsVal_encodeNat]
    exact hab
  have hval : bitsVal (rip subBit (max (encodeNat a).length (encodeNat b).length) false
      (encodeNat a) (encodeNat b)) = a - b := by
    rw [bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

#assert_std_axioms addSubProg_closed addSubProg_eval W3_addNat_holds W3_subNat_holds

end WP.W3
