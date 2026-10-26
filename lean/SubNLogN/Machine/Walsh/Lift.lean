/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.LiftLoop
import SubNLogN.Machine.Walsh.LiftPure

/-!
# `SubNLogN.Machine.Walsh.Lift`: the exact lift and lowering kernels (K3.1, K3.2)

Paper: Lemma 5.3 (`lem:walsh-lift`: append `8d`
fractional zero bits to every numerator and use width `w_* = w + 8d`) and Proposition 5.5 (`prop:cnot-batch`:
lowering from `P_*` to `P` discards only zero bits). The program design is at the top of
`Walsh/LiftBase.lean`.

**Scope (honest summary).** Proved (no `sorry`, no extra hypotheses):
* `liftMachine_holds : LiftMachineStmt` (`Contracts/Walsh.lean`, K3.1);
* `lowerMachine_holds : LowerMachineStmt` (`Contracts/Walsh.lean`, K3.2).
Both kernels use five private scratch stacks (`Scr`), the register type `Option Sym` and the
cost constant `C = 50`. The guard hypotheses `CArrFits w v` of the two contracts are not used: the
field identity `twosBits (w + δ) (a·2^δ) = replicate δ false ++ twosBits w a` holds for every
integer `a` (`twosBits_mul_two_pow`). The hypothesis `1 ≤ w` is used (a field of the narrower
format must be detectable by its first bit, and it pays for the per-field overhead).
-/

namespace SubNLogN.Machine.WalshLift

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-- Private scratch stacks of the lift / lower kernels: the template counters `tz` (`δ` units) and
`tc` (`w` units), the walk buffer `u`, the output buffer `o` (also the bit buffer of `w` while the
template is built) and the bit buffer `pk` of `δ`. -/
inductive Scr : Type
  | tz | tc | u | o | pk
  deriving DecidableEq

instance : Fintype Scr where
  elems := {.tz, .tc, .u, .o, .pk}
  complete := by intro x; cases x <;> simp

/-- Stacks of the lift / lower kernels: `.inl 0` the array, `.inl 1` the header. -/
abbrev LK : Type := KLoc (Fin 2) Scr

/-! ## Programs -/

/-- Build the template from the header `hdrSyms [w, δ]`: `tz = uSym^δ`, `tc = uSym^w`; the header
is restored. -/
def build : SProg LK :=
  .seq (moveBits (.inl 1) (.inr .o)) (.seq (moveBits (.inl 1) (.inr .pk))
  (.seq (pushC (.inl 1) .mark) (.seq (toUnary (.inr .pk) (.inr .tz) (.inl 1) (.inr .u))
  (.seq (pushC (.inl 1) .mark) (toUnary (.inr .o) (.inr .tc) (.inl 1) (.inr .u))))))

/-- The kernel skeleton, for a field program `fld`: build the template, run the record loop with
the output reversed on `o` (guard `mark`), rewind the output onto the array stack, clear the
template. -/
def mainProg (fld : SProg LK) : SProg LK :=
  .seq build (.seq (pushC (.inr .o) .mark) (.seq (recLoop (.inl 0) (.inr .o) fld)
    (.seq (WP.W9comp.rewindTo (.inr .o) (.inl 0) .mark)
    (.seq (clear (.inr .tz)) (clear (.inr .tc))))))

/-- The lift kernel. -/
def liftProg : SProg LK := mainProg (fieldL (.inl 0) (.inr .tz) (.inr .tc) (.inr .u) (.inr .o))

/-- The lowering kernel. -/
def lowerProg : SProg LK := mainProg (fieldD (.inl 0) (.inr .tz) (.inr .tc) (.inr .u) (.inr .o))

theorem closed_liftProg : liftProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, liftProg, mainProg, build, fieldL, walkZL, walkC, drain,
    drainBody, toUnary, u2Body, dbl, drain2, drain2Body, clear, recLoop, recBody, fieldLoop,
    moveBits, moveBitsBody, WP.W9comp.rewindTo, WP.W9comp.rewindBody, pushR, popR, peekR, pushC,
    skip]

theorem closed_lowerProg : lowerProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, lowerProg, mainProg, build, fieldD, walkZD, walkC, drain,
    drainBody, toUnary, u2Body, dbl, drain2, drain2Body, clear, recLoop, recBody, fieldLoop,
    moveBits, moveBitsBody, WP.W9comp.rewindTo, WP.W9comp.rewindBody, pushR, popR, peekR, pushC,
    skip]

/-! ## The template build -/

/-- **Template build**: from the header `hdrSyms [w, δ]` (restored) and clean scratch, `tz`
receives `uSym^δ` and `tc` receives `uSym^w`; all other stacks are unchanged. -/
theorem build_eval (w δ : ℕ) (hrest : List Sym) (S : LK → List Sym) (v : Option Sym)
    (hclean : KClean S) (hH : S (.inl 1) = hdrSyms [w, δ] ++ hrest) :
    ∃ t, Eval [] build ⟨v, S⟩
      ⟨none, Function.update (Function.update S (.inr .tz) (List.replicate δ uSym)) (.inr .tc)
        (List.replicate w uSym)⟩ t ∧ t ≤ 20 * (w + δ) + 10 := by
  have hH' : S (.inl 1) = (encodeNat w).map Sym.bit ++
      Sym.mark :: ((encodeNat δ).map Sym.bit ++ Sym.mark :: hrest) := by
    rw [hH]
    simp [hdrSyms, natSyms]
  have e1 := moveBits_eval (src := (.inl 1 : LK)) (dst := .inr .o) (by decide) [] v
    (encodeNat w) _ S (TermOK.cons rfl _) hH'
  simp only [List.tail_cons, List.head?_cons] at e1
  set S1 := Function.update (Function.update S (.inl 1)
    ((encodeNat δ).map Sym.bit ++ Sym.mark :: hrest)) (.inr .o)
    ((encodeNat w).reverse.map Sym.bit ++ S (.inr .o)) with hS1
  have e2 := moveBits_eval (src := (.inl 1 : LK)) (dst := .inr .pk) (by decide) [] (some .mark)
    (encodeNat δ) _ S1 (TermOK.cons rfl _)
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_self])
  simp only [List.tail_cons, List.head?_cons] at e2
  set S2 := Function.update (Function.update S1 (.inl 1) hrest) (.inr .pk)
    ((encodeNat δ).reverse.map Sym.bit ++ S1 (.inr .pk)) with hS2
  have e3 := eval_pushC (.inl 1 : LK) Sym.mark (some .mark) S2
  set S3 := Function.update S2 (.inl 1) (Sym.mark :: S2 (.inl 1)) with hS3
  obtain ⟨t4, e4, ht4⟩ := toUnary_eval (src := (.inr .pk : LK)) (dst := .inr .tz) (h := .inl 1)
    (u := .inr .u) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (some .mark) (encodeNat δ).reverse 0 S3
    (by simp [hS3, hS2, hS1, hclean .pk])
    (by simp [hS3, hS2, hS1, hclean .tz])
    (by simp [hS3, hS2, hS1, hclean .u])
  rw [accBits_encodeNat, List.reverse_reverse] at e4
  rw [accBits_encodeNat] at ht4
  set S4 := Function.update (Function.update (Function.update S3 (.inr .pk) []) (.inr .tz)
    (List.replicate δ uSym)) (.inl 1) ((encodeNat δ).map Sym.bit ++ S3 (.inl 1)) with hS4
  have e5 := eval_pushC (.inl 1 : LK) Sym.mark none S4
  set S5 := Function.update S4 (.inl 1) (Sym.mark :: S4 (.inl 1)) with hS5
  obtain ⟨t6, e6, ht6⟩ := toUnary_eval (src := (.inr .o : LK)) (dst := .inr .tc) (h := .inl 1)
    (u := .inr .u) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    none (encodeNat w).reverse 0 S5
    (by simp [hS5, hS4, hS3, hS2, hS1, hclean .o])
    (by simp [hS5, hS4, hS3, hS2, hS1, hclean .tc])
    (by simp [hS5, hS4, hS3, hS2, hS1, hclean .u])
  rw [accBits_encodeNat, List.reverse_reverse] at e6
  rw [accBits_encodeNat] at ht6
  refine ⟨_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ rfl,
    ?_⟩
  · congr 1
    funext k
    rcases k with i | e
    · fin_cases i
      · simp [hS5, hS4, hS3, hS2, hS1]
      · simp [hS5, hS4, hS3, hS2, hS1, hH']
    · cases e <;> simp [hS5, hS4, hS3, hS2, hS1, hclean _]
  · have hb1 : (encodeNat w).length ≤ w := bitLen_le_self w
    have hb2 : (encodeNat δ).length ≤ δ := bitLen_le_self δ
    simp only [List.length_reverse] at ht4 ht6
    omega

/-! ## The kernel skeleton -/

/-- The template state: `tz = uSym^δ`, `tc = uSym^w`, `u` empty. -/
def Tpl (δ w : ℕ) (S : LK → List Sym) : Prop :=
  S (.inr .tz) = List.replicate δ uSym ∧ S (.inr .tc) = List.replicate w uSym ∧ S (.inr .u) = []

theorem goodFrame_tpl (δ w : ℕ) : GoodFrame (.inl 0 : LK) (.inr .o) (Tpl δ w) := by
  rintro S L1 L2 ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [h1, h2, h3]

theorem fieldOK_lift (δ w : ℕ) :
    FieldOK (.inl 0 : LK) (.inr .o) (fieldL (.inl 0) (.inr .tz) (.inr .tc) (.inr .u) (.inr .o))
      w (7 * δ + 8 * w + 8) (fun g => List.replicate δ false ++ g) (Tpl δ w) := by
  rintro g RX S v hg ⟨hZ, hC, hU⟩ hX
  have e := fieldL_eval (x := (.inl 0 : LK)) (tz := .inr .tz) (tc := .inr .tc) (u := .inr .u)
    (o := .inr .o) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) δ v g RX S hZ (by rw [hC, hg]) hU hX
  rw [hg] at e
  exact ⟨none, e⟩

theorem fieldOK_lower (δ w : ℕ) :
    FieldOK (.inl 0 : LK) (.inr .o) (fieldD (.inl 0) (.inr .tz) (.inr .tc) (.inr .u) (.inr .o))
      (w + δ) (7 * δ + 8 * w + 8) (List.drop δ) (Tpl δ w) := by
  rintro g RX S v hg ⟨hZ, hC, hU⟩ hX
  have h1 : (g.take δ).length = δ := by rw [List.length_take, hg]; omega
  have h2 : (g.drop δ).length = w := by rw [List.length_drop, hg]; omega
  have e := fieldD_eval (x := (.inl 0 : LK)) (tz := .inr .tz) (tc := .inr .tc) (u := .inr .u)
    (o := .inr .o) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) v (g.take δ) (g.drop δ) RX S
    (by rw [hZ, h1]) (by rw [hC, h2]) hU (by rw [List.take_append_drop, hX])
  rw [h1, h2] at e
  exact ⟨none, e⟩

/-- **The kernel skeleton**, for a field program meeting `FieldOK` on fields of width `W ≥ 1`:
from the array `arrSyms (rs.map flatten)` (records = lists of fields) and the header
`hdrSyms [w, δ]`, with clean scratch, the array becomes the array of output records
`(fs.map F).flatten`; every other stack ends with its initial content. -/
theorem mainProg_eval {fld : SProg LK} {W cf : ℕ} (hW : 1 ≤ W) {F : List Bool → List Bool}
    (w δ : ℕ) (hfld : FieldOK (.inl 0 : LK) (.inr .o) fld W cf F (Tpl δ w))
    (rs : List (List (List Bool))) (rest hrest : List Sym) (S : LK → List Sym) (v : Option Sym)
    (hclean : KClean S) (hrs : ∀ fs ∈ rs, ∀ g ∈ fs, g.length = W) (hblk : BlkTerm rest)
    (hX : S (.inl 0) = arrSyms (rs.map List.flatten) ++ rest)
    (hH : S (.inl 1) = hdrSyms [w, δ] ++ hrest) :
    ∃ v' t, Eval [] (mainProg fld) ⟨v, S⟩
      ⟨v', Function.update S (.inl 0) (arrSyms (rs.map fun fs => (fs.map F).flatten) ++ rest)⟩ t ∧
      t ≤ 20 * (w + δ) + 10 + 1 + ((rs.map fun fs => fs.length * (cf + 2) + 6).sum + 2) +
        (3 * (arrSyms (rs.map fun fs => (fs.map F).flatten)).length + 2) + (2 * δ + 2) +
        (2 * w + 2) := by
  obtain ⟨t1, e1, ht1⟩ := build_eval w δ hrest S v hclean hH
  set S1 := Function.update (Function.update S (.inr .tz) (List.replicate δ uSym)) (.inr .tc)
    (List.replicate w uSym) with hS1
  have e2 := eval_pushC (.inr .o : LK) Sym.mark none S1
  set S2 := Function.update S1 (.inr .o) (Sym.mark :: S1 (.inr .o)) with hS2
  have hgood2 : Tpl δ w S2 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [hS2, hS1, hclean .u]
  obtain ⟨v3, e3⟩ := recLoop_eval (x := (.inl 0 : LK)) (o := .inr .o) (by decide) hW
    (goodFrame_tpl δ w) hfld rest hblk rs S2 none hrs hgood2
    (by simp [hS2, hS1, hX])
  set out := arrSyms (rs.map fun fs => (fs.map F).flatten) with hout
  set S3 := Function.update (Function.update S2 (.inl 0) rest) (.inr .o)
    (out.reverse ++ S2 (.inr .o)) with hS3
  have h3o : S3 (.inr .o) = out.reverse ++ Sym.mark :: [] := by
    simp [hS3, hS2, hS1, hclean .o]
  have e4 := WP.W9comp.rewindTo_eval (src := (.inr .o : LK)) (dst := .inl 0) (by decide) Sym.mark
    v3 out.reverse [] S3 (by rw [List.mem_reverse, hout]; exact mark_not_mem_arrSyms _) h3o
  set S4 := Function.update (Function.update S3 (.inr .o) []) (.inl 0)
    (out.reverse.reverse ++ S3 (.inl 0)) with hS4
  have e5 := clear_eval (.inr .tz : LK) (some Sym.mark) (List.replicate δ uSym) S4
    (by simp [hS4, hS3, hS2, hS1])
  have e6 := clear_eval (.inr .tc : LK) none (List.replicate w uSym)
    (Function.update S4 (.inr .tz) []) (by simp [hS4, hS3, hS2, hS1])
  refine ⟨none, _,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    rcases k with i | e
    · fin_cases i
      · simp [hS4, hS3, hS2, hS1]
      · simp [hS4, hS3, hS2, hS1]
    · cases e <;> simp [hS4, hS3, hS2, hS1, hclean _]
  · simp only [List.length_reverse, List.length_replicate]
    omega

/-! ## Costs -/

theorem rec_cost_le (w δ N : ℕ) (hw : 1 ≤ w) :
    2 * N * (7 * δ + 8 * w + 8 + 2) + 6 ≤ 18 * (2 * (w + δ) * N + 1) := by
  have h1 : N ≤ N * w := Nat.le_mul_of_pos_right N hw
  have e1 : 2 * N * (7 * δ + 8 * w + 8 + 2) + 6 = 14 * (N * δ) + 16 * (N * w) + 20 * N + 6 := by
    ring
  have e2 : 18 * (2 * (w + δ) * N + 1) = 36 * (N * w) + 36 * (N * δ) + 18 := by ring
  rw [e1, e2]
  omega

/-- The record-loop cost is at most `18·cvol (w + δ) v`. -/
theorem sum_le_cvol (w δ W' : ℕ) (hw : 1 ≤ w) : ∀ v : List (List CInt),
    ((v.map (fieldsOf W')).map fun fs => fs.length * (7 * δ + 8 * w + 8 + 2) + 6).sum ≤
      18 * cvol (w + δ) v
  | [] => by simp [cvol_eq_sum]
  | cs :: v => by
    have ih := sum_le_cvol w δ W' hw v
    rw [cvol_eq_sum] at ih ⊢
    simp only [List.map_cons, List.sum_cons, length_fieldsOf] at ih ⊢
    have key := rec_cost_le w δ cs.length hw
    rw [Nat.mul_add 18 (2 * (w + δ) * cs.length + 1)]
    omega

theorem total_le (w δ A V O : ℕ) (hA : A ≤ 18 * V) (hO : O ≤ V) :
    20 * (w + δ) + 10 + 1 + (A + 2) + (3 * O + 2) + (2 * δ + 2) + (2 * w + 2) ≤
      50 * (V + w + δ + 1) := by
  omega

/-! ## The contracts -/

/-- **K3.1, exact lift, proved** (`LiftMachineStmt`, `Contracts/Walsh.lean`; Lemma 5.3,
`lem:walsh-lift`). Every field of every coefficient gets `δ` zero bits below
it (`twosBits_mul_two_pow`), in one streaming pass after building a unary template from the
header. Scratch `Scr` (5 stacks, clean), registers `Option Sym`, constant `C = 50`. The guard
`CArrFits w v` is not needed. -/
theorem liftMachine_holds : LiftMachineStmt := by
  refine ⟨50, fun _ => ⟨Scr, inferInstance, inferInstance, Option Sym, liftProg, inferInstance,
    inferInstance, closed_liftProg, ?_⟩⟩
  intro w δ v rest hrest S hclean hw _ hrest' hS0 hS1
  apply Runs.of_eval
  intro v0
  obtain ⟨v', t, e, ht⟩ := mainProg_eval (fld := fieldL (.inl 0) (.inr .tz) (.inr .tc) (.inr .u)
    (.inr .o)) hw w δ (fieldOK_lift δ w) (v.map (fieldsOf w)) rest hrest S v0 hclean
    (by
      intro fs hfs g hg
      obtain ⟨cs, -, rfl⟩ := List.mem_map.1 hfs
      exact width_fieldsOf w cs g hg)
    hrest' (by rw [hS0, carrSyms_eq_fields]) hS1
  rw [← carrSyms_liftC_eq] at e ht
  refine ⟨v', t, e, trivial, ht.trans ?_⟩
  have hO : (carrSyms (w + δ) (mapC (liftC δ) v)).length ≤ cvol (w + δ) v := by
    rw [← cvol, cvol_mapC]
  exact total_le w δ _ _ _ (sum_le_cvol w δ w hw v) hO

/-- **K3.2, exact lowering, proved** (`LowerMachineStmt`, `Contracts/Walsh.lean`;
Proposition 5.5 (`prop:cnot-batch`)). Every `(w + δ)`-bit field loses its `δ` low bits, which are zero for the
input `mapC (liftC δ) v` (`fieldsOf_liftC_drop`). Scratch `Scr` (5 stacks, clean), registers
`Option Sym`, constant `C = 50`. The guard `CArrFits w v` is not needed. -/
theorem lowerMachine_holds : LowerMachineStmt := by
  refine ⟨50, fun _ => ⟨Scr, inferInstance, inferInstance, Option Sym, lowerProg, inferInstance,
    inferInstance, closed_lowerProg, ?_⟩⟩
  intro w δ v rest hrest S hclean hw _ hrest' hS0 hS1
  apply Runs.of_eval
  intro v0
  obtain ⟨v', t, e, ht⟩ := mainProg_eval (fld := fieldD (.inl 0) (.inr .tz) (.inr .tc) (.inr .u)
    (.inr .o)) (W := w + δ) (by omega) w δ (fieldOK_lower δ w)
    ((mapC (liftC δ) v).map (fieldsOf (w + δ))) rest hrest S v0 hclean
    (by
      intro fs hfs g hg
      obtain ⟨cs, -, rfl⟩ := List.mem_map.1 hfs
      exact width_fieldsOf (w + δ) cs g hg)
    hrest' (by rw [hS0, carrSyms_eq_fields]) hS1
  rw [← carrSyms_lower_eq] at e ht
  refine ⟨v', t, e, trivial, ht.trans ?_⟩
  have hA := sum_le_cvol w δ (w + δ) hw (mapC (liftC δ) v)
  rw [cvol_mapC] at hA
  have hO : (carrSyms w v).length ≤ cvol (w + δ) v := by
    rw [← cvol]
    exact cvol_le_cvol w δ v
  exact total_le w δ _ _ _ hA hO

end SubNLogN.Machine.WalshLift
