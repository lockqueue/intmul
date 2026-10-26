import WP.Top.Layout
import WP.W0m.Main
import Contracts.W9.Common

/-!
# WP.Top.Embed — where each stage's stacks live in the global layout

* **Input stage (W0m).** `ι0 : WP.W0m.Stk → GW`:
  * the outputs `oa, ob, nn, bb, kk, k0, lf, p0` go to `oa, ob, pn, pb, pk, pK0, pL, pP0`;
  * the 19 temporaries go to stacks that are idle at that point (`s`, `s'`, `w _`, `f`, `f'`, `tl`,
    `tr`, `ret`, `rq`, `c 0`, `mb 0..5`).
* **Table stage (W7).** `ι7 hm : Loc 4 m → GW` for `m ≤ W7.maxScratch = 32`:
  * the named stacks `0..3` (`TR`, `L`, `p`, `K`) go to `tr, pL, pP0, pK0`;
  * scratch `j` goes to `sc32 j`, a fixed list of the 32 other stacks. W7's scratch content is
    arbitrary and restored, so it may sit on live stacks (`oa`, `ob`, `pn`, …).
* **Tape converter.** `ιc hm : Loc 1 m → GW` for `m ≤ 75`: named `0` (`TR`) goes to `tr`, scratch `j`
  to `sc75 j` (the 75 other stacks).
* **Pipeline (W9).** `ι9 hm : W9.BLoc m → GW` for `m ≤ w9Scratch = 64`:
  * the named stacks `S W0 TL TR RET RQ C0..C3 OA OB` go to `s, w 0, tl, tr, ret, rq, c 0..3, oa, ob`;
  * scratch `j` goes to `sc64 j`: `s'`, `w 1..3`, `f`, `f'`, `mb _`, the parameter stacks and the
    42 spares. That is exactly the 64 stacks outside W9's named ones.

`afterIn_eq` turns W0m's postcondition into the exact global state `prodOf (prmState n a b)`.
`afterTab_eq` does the same for W7's (embedded) postcondition, giving `prodOf (tabOut n a b cSpec)`.
The later stages' states are in `WP.Top.States`.
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts IntMulTM IntMulTM.Contracts

/-! ## Production states from work states -/

/-- The production state with empty input and output stacks and work stacks `S`. -/
def prodOf (S : GW → List Sym) : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)
  | .input => []
  | .output => []
  | .work w => S w

theorem eq_prodOf {T : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)} {S : GW → List Sym}
    (hi : T .input = []) (ho : T .output = []) (hw : ∀ w, T (.work w) = S w) : T = prodOf S :=
  StackId.stk_ext T hi ho hw

/-! ## The input stage's stacks -/

/-- W0m's local stacks in the global layout. -/
def ι0 : WP.W0m.Stk → GW
  | .inp => .s | .oa => .oa | .ob => .ob | .la => .s' | .lb => .w 0
  | .nn => .pn | .bb => .pb | .kk => .pk | .k0 => .pK0 | .lf => .pL | .p0 => .pP0
  | .rr => .w 1 | .t1 => .w 2 | .t2 => .w 3 | .t3 => .f | .c4 => .f' | .tm => .tl | .ct => .tr
  | .cs => .ret | .x0 => .rq | .x1 => .c 0
  | .s i => .mb (Fin.castLE (by decide) i)

/-- A left inverse of `ι0`. -/
def back0 : GW → WP.W0m.Stk
  | .s => .inp | .oa => .oa | .ob => .ob | .s' => .la
  | .w i => if i.val = 0 then .lb else if i.val = 1 then .rr else if i.val = 2 then .t1 else .t2
  | .pn => .nn | .pb => .bb | .pk => .kk | .pK0 => .k0 | .pL => .lf | .pP0 => .p0
  | .f => .t3 | .f' => .c4 | .tl => .tm | .tr => .ct | .ret => .cs | .rq => .x0 | .c _ => .x1
  | .mb j => if h : j.val < 6 then .s ⟨j.val, h⟩ else .inp
  | .xs _ => .inp

theorem back0_ι0 : Function.LeftInverse back0 ι0 := by
  intro x
  cases x with
  | s i => exact dif_pos i.isLt
  | _ => rfl

theorem ι0_inj : Function.Injective ι0 := back0_ι0.injective

/-- W0m's outputs are the input-stage state. -/
theorem outW_eq (a b : ℕ) (x : WP.W0m.Stk) :
    WP.W0m.outW a b x = prmState (operandBits a b) a b (ι0 x) := by
  cases x <;> rfl

/-- Stacks outside `ι0`'s image are empty in the input-stage state. -/
theorem prmState_of_not_mem (n A B : ℕ) (w : GW) (h : ∀ x, ι0 x ≠ w) : prmState n A B w = [] := by
  cases w with
  | oa => exact absurd rfl (h .oa)
  | ob => exact absurd rfl (h .ob)
  | pn => exact absurd rfl (h .nn)
  | pb => exact absurd rfl (h .bb)
  | pk => exact absurd rfl (h .kk)
  | pK0 => exact absurd rfl (h .k0)
  | pL => exact absurd rfl (h .lf)
  | pP0 => exact absurd rfl (h .p0)
  | _ => rfl

/-- **W0m's postcondition is the exact input-stage state.** -/
theorem afterIn_eq (a b : ℕ) {T : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)}
    (hi : T .input = []) (ho : T .output = []) (hw : ∀ x, T (.work (ι0 x)) = WP.W0m.outW a b x)
    (hz : ∀ w, (∀ x, ι0 x ≠ w) → T (.work w) = []) :
    T = prodOf (prmState (operandBits a b) a b) := by
  refine eq_prodOf hi ho (fun w => ?_)
  by_cases hr : ∃ x, ι0 x = w
  · obtain ⟨x, rfl⟩ := hr
    rw [hw, outW_eq]
  · push_neg at hr
    rw [hz w hr, prmState_of_not_mem _ _ _ w hr]

/-! ## The table stage's stacks -/

/-- W7's named stacks: `TR`, `L`, `p`, `K`. -/
def named7 (i : Fin 4) : GW :=
  if i.val = 0 then .tr else if i.val = 1 then .pL else if i.val = 2 then .pP0 else .pK0

/-- The 32 stacks available as W7 scratch. -/
def sc32List : List GW :=
  [.oa, .ob, .s, .s', .w 0, .w 1, .w 2, .w 3, .f, .f', .tl, .ret, .rq, .c 0, .c 1, .c 2, .c 3,
    .mb 0, .mb 1, .mb 2, .mb 3, .mb 4, .mb 5, .mb 6, .mb 7, .mb 8, .mb 9, .pn, .pb, .pk, .xs 0, .xs 1]

/-- Scratch slot `j` of W7. -/
def sc32 (j : Fin 32) : GW := sc32List.getD j.val .tr

theorem named7_inj : Function.Injective named7 := by decide

theorem sc32_inj : Function.Injective sc32 := by decide

theorem named7_ne_sc32 : ∀ i j, named7 i ≠ sc32 j := by decide

/-- W7's stacks in the global layout. -/
def ι7 {m : ℕ} (hm : m ≤ 32) : Loc 4 m → GW :=
  WP.W0m.embL named7 (fun j => sc32 (Fin.castLE hm j))

theorem ι7_inj {m : ℕ} (hm : m ≤ 32) : Function.Injective (ι7 hm) :=
  WP.W0m.embL_inj named7_inj (sc32_inj.comp (fun _ _ h => Fin.castLE_inj.mp h))
    (fun i _ => named7_ne_sc32 i _)

theorem ι7_inl0 {m : ℕ} (hm : m ≤ 32) : ι7 hm (.inl 0) = .tr := rfl

/-- **W7's embedded postcondition is the exact pipeline entry state.** The table tape lands on `tr`;
every other stack keeps its input-stage content. -/
theorem afterTab_eq {m : ℕ} (hm : m ≤ 32) (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    {T : GW → List Sym}
    (h1 : ∀ l, T (ι7 hm l) = Function.update (fun l => prmState n A B (ι7 hm l)) (.inl 0)
      (W7.tape W7.snapshotSchedule.toTapeFormat cSpec ++ prmState n A B (ι7 hm (.inl 0))) l)
    (h2 : ∀ k, (∀ l, ι7 hm l ≠ k) → T k = prmState n A B k) :
    T = tabOut n A B cSpec := by
  funext w
  unfold tabOut
  by_cases hw : w = .tr
  · subst hw
    rw [Function.update_self, ← ι7_inl0 hm, h1, Function.update_self, ι7_inl0]
    exact List.append_nil _
  · rw [Function.update_of_ne hw]
    by_cases hr : ∃ l, ι7 hm l = w
    · obtain ⟨l, rfl⟩ := hr
      have hl : l ≠ .inl 0 := by
        rintro rfl
        exact hw (ι7_inl0 hm)
      rw [h1, Function.update_of_ne hl]
    · push_neg at hr
      exact h2 w hr


/-! ## The tape converter's and the pipeline's stacks -/

/-- Injectivity of a two-part stack map. -/
theorem sumElim_inj {α β K : Type} {f : α → K} {g : β → K} (hf : Function.Injective f)
    (hg : Function.Injective g) (hd : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hf h)
  · exact absurd h (hd a b)
  · exact absurd h.symm (hd b a)
  · exact congrArg Sum.inr (hg h)

/-- The 64 stacks outside W9's named ones: scratch of the converter and of W9. -/
def sc64List : List GW :=
  [.s', .w 1, .w 2, .w 3, .f, .f', .mb 0, .mb 1, .mb 2, .mb 3, .mb 4, .mb 5, .mb 6, .mb 7, .mb 8,
    .mb 9, .pn, .pb, .pk, .pK0, .pL, .pP0] ++ List.ofFn GW.xs

/-- Scratch slot `j` of the converter and of W9. -/
def sc64 (j : Fin 64) : GW := sc64List.getD j.val .tr

/-- A left inverse of `sc64`, for injectivity. -/
def back64 (w : GW) : Fin 64 :=
  ⟨sc64List.findIdx (· == w) % 64, Nat.mod_lt _ (by decide)⟩

theorem back64_sc64 : ∀ j : Fin 64, back64 (sc64 j) = j := by decide

theorem sc64_inj : Function.Injective sc64 :=
  Function.LeftInverse.injective back64_sc64

theorem tr_ne_sc64 : ∀ j, GW.tr ≠ sc64 j := by decide

/-- The 75 stacks other than `tr`: scratch of the converter. -/
def sc75List : List GW :=
  [.s, .w 0, .tl, .ret, .rq, .c 0, .c 1, .c 2, .c 3, .oa, .ob] ++ sc64List

/-- Scratch slot `j` of the converter. -/
def sc75 (j : Fin 75) : GW := sc75List.getD j.val .tr

/-- A left inverse of `sc75`, for injectivity. -/
def back75 (w : GW) : Fin 75 :=
  ⟨sc75List.findIdx (· == w) % 75, Nat.mod_lt _ (by decide)⟩

theorem back75_sc75 : ∀ j : Fin 75, back75 (sc75 j) = j := by decide

theorem sc75_inj : Function.Injective sc75 :=
  Function.LeftInverse.injective back75_sc75

theorem tr_ne_sc75 : ∀ j, GW.tr ≠ sc75 j := by decide

/-- The converter's stacks in the global layout: `TR` on `tr`, scratch on the other 75 stacks. -/
def ιc {m : ℕ} (hm : m ≤ 75) : Loc 1 m → GW :=
  Sum.elim (fun _ => .tr) (fun j => sc75 (Fin.castLE hm j))

theorem ιc_inj {m : ℕ} (hm : m ≤ 75) : Function.Injective (ιc hm) :=
  sumElim_inj (fun a b _ => Subsingleton.elim a b) (sc75_inj.comp (fun _ _ h => Fin.castLE_inj.mp h))
    (fun _ _ => tr_ne_sc75 _)

/-- W9's named stacks in the global layout. -/
def named9 : TMFw.Contracts.W9.LB → GW
  | .S => .s | .W0 => .w 0 | .TL => .tl | .TR => .tr | .RET => .ret | .RQ => .rq
  | .C0 => .c 0 | .C1 => .c 1 | .C2 => .c 2 | .C3 => .c 3 | .OA => .oa | .OB => .ob

/-- A left inverse of `named9`. -/
def back9 : GW → TMFw.Contracts.W9.LB
  | .s => .S | .tl => .TL | .tr => .TR | .ret => .RET | .rq => .RQ | .oa => .OA | .ob => .OB
  | .w _ => .W0
  | .c i => if i.val = 0 then .C0 else if i.val = 1 then .C1 else if i.val = 2 then .C2 else .C3
  | _ => .S

theorem back9_named9 : Function.LeftInverse back9 named9 := by
  intro l
  cases l <;> rfl

theorem named9_ne_sc64 : ∀ l j, named9 l ≠ sc64 j := by
  intro l
  cases l <;> decide

/-- W9's stacks in the global layout. -/
def ι9 {m : ℕ} (hm : m ≤ 64) : TMFw.Contracts.W9.BLoc m → GW :=
  Sum.elim named9 (fun j => sc64 (Fin.castLE hm j))

theorem ι9_inj {m : ℕ} (hm : m ≤ 64) : Function.Injective (ι9 hm) :=
  sumElim_inj back9_named9.injective (sc64_inj.comp (fun _ _ h => Fin.castLE_inj.mp h))
    (fun l _ => named9_ne_sc64 l _)

#assert_std_axioms eq_prodOf back0_ι0 ι0_inj outW_eq prmState_of_not_mem afterIn_eq named7_inj
  sc32_inj named7_ne_sc32 ι7_inj ι7_inl0 afterTab_eq sumElim_inj back64_sc64 sc64_inj tr_ne_sc64
  back75_sc75 sc75_inj tr_ne_sc75
  ιc_inj back9_named9 named9_ne_sc64 ι9_inj

end WP.Top
