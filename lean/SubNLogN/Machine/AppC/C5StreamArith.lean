/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateBase
import SubNLogN.Machine.Contracts.Layout
import WP.W3.AddSub
import IntMulTM.Framework.Lib.CompareEval
import IntMulTM.SpecFacts

/-!
# Mark-floored natural-number arithmetic on binary counters (`NatArith`)

A small, reusable library of TM2 programs on `natSyms` counters (LSB on top) for kernels whose
scratch stacks may contain **arbitrary junk**. Every program is generic in the stack type `K`
(with `DecidableEq K`) and runs on the register file `Reg`; callers lift it with their own lens
(`Prog.liftRegs`). All specifications are exact `Runs` facts (every stack not mentioned is
unchanged) with explicit costs. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Convention (*mark floor*): a temporary stack is first given a `mark` on top of its (arbitrary)
content, so that the numbers computed above it satisfy `TermOK`; `dropF` removes a number together
with its floor.

Public API (namespace `SubNLogN.Machine.NatArith`):
* `pushMark k`, `pushNat k c` (a compile-time constant), `copyN src dst t`, `dropN k`, `dropF k`;
* `addN x y z t1 t2 t3` (`z += a + b`), `subN …` (`z += a - b`, `b ≤ a`), via `WP.W3.addSubProg`;
* `mulN x y z A Bs Acc T` (`z += a * b`, shift-and-add; `runs_mulN`, cost `mulCost a b`);
* `mulConstN k c Q Tdst A Bs Acc T` (`a ↦ a * c` in place; `runs_mulConstN`, cost
  `mulConstCost a c`) and `powMulN k c ns Kc t Q Tdst A Bs Acc` (`a ↦ a * c ^ n` in place, `n` read
  from the counter on `ns`, `1 ≤ c`; `runs_powMulN`, cost `powCost c a n`);
* `cmpN x y t1 t2` (comparison into the compare register; no specification is stated here).

Operands have the form `natSyms a ++ r` with `TermOK r` and are restored; the temporaries named in
each program may hold arbitrary content and are restored exactly. Callers embed a program in their
own kernel with `callInj ι l` and `runs_callInj` (`Contracts/Layout.lean`).
-/

namespace SubNLogN.Machine.NatArith

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Register file of the library: work register, add/sub register, compare register. -/
abbrev Reg : Type := Option Sym × (WP.W3.AReg × CReg)

/-- Lens to the work register (library macros: copy, drop, push, peek). -/
def lW : Lens Reg (Option Sym) := Lens.fst _ _

/-- Lens to the add/sub register. -/
def lA : Lens Reg WP.W3.AReg := (Lens.snd _ _).comp (Lens.fst _ _)

/-- Lens to the compare register. -/
def lC : Lens Reg CReg := (Lens.snd _ _).comp (Lens.snd _ _)

section Prims

variable {K : Type}

/-- Push a `mark` (a floor) on `k`. -/
def pushMark (k : K) : Prog K (fun _ => Sym) Reg := (pushC k .mark).liftRegs lW

/-- Push the bits of `bs` on `k`, last bit first (so that `bs.head` ends on top). -/
def pushBits (k : K) : List Bool → Prog K (fun _ => Sym) Reg
  | [] => .load id
  | b :: bs => .seq (pushBits k bs) ((pushC k (.bit b)).liftRegs lW)

/-- Push the compile-time constant `c` (as `natSyms c`) on `k`. -/
def pushNat (k : K) (c : ℕ) : Prog K (fun _ => Sym) Reg := pushBits k (encodeNat c)

/-- Copy the number on top of `src` onto `dst` (`tmp` is a temporary, restored). -/
def copyN (src dst tmp : K) : Prog K (fun _ => Sym) Reg := (copyBlock src dst tmp).liftRegs lW

/-- Pop the number on top of `k`, keeping its terminator. -/
def dropN (k : K) : Prog K (fun _ => Sym) Reg := (WP.W3.dropNum k).liftRegs lW

/-- Pop the number on top of `k` together with the (non-bit) floor symbol below it. -/
def dropF (k : K) : Prog K (fun _ => Sym) Reg := (SubNLogN.Machine.K1.dropBits k).liftRegs lW

/-- Embedding of the six stacks of `WP.W3.addSubProg` (`x, y, z` and three temporaries). -/
def emb3 (x y z t1 t2 t3 : K) : Loc 3 3 → K
  | .inl i => if i.val = 0 then x else if i.val = 1 then y else z
  | .inr i => if i.val = 0 then t1 else if i.val = 1 then t2 else t3

/-- `z += a + b` (operands on `x`, `y`, restored; `t1, t2, t3` temporaries, restored). -/
def addN (x y z t1 t2 t3 : K) : Prog K (fun _ => Sym) Reg :=
  callInj (emb3 x y z t1 t2 t3) lA (WP.W3.addSubProg WP.W3.addBit)

/-- `z += a - b` for `b ≤ a` (operands restored; temporaries restored). -/
def subN (x y z t1 t2 t3 : K) : Prog K (fun _ => Sym) Reg :=
  callInj (emb3 x y z t1 t2 t3) lA (WP.W3.addSubProg WP.W3.subBit)

/-- Compare the numbers on `x` and `y` (both restored); the result is in the compare register. -/
def cmpN (x y t1 t2 : K) : Prog K (fun _ => Sym) Reg := (cmpNum x y t1 t2).liftRegs lC

theorem closed_pushMark (k : K) : (pushMark k).Closed :=
  SubNLogN.Machine.K1.Rot.closed_pushC_lift lW k _

theorem closed_pushBits (k : K) : ∀ bs : List Bool, (pushBits k bs).Closed
  | [] => WP.W3.closed_of_noRec rfl
  | _ :: bs => ⟨closed_pushBits k bs, SubNLogN.Machine.K1.Rot.closed_pushC_lift lW k _⟩

theorem closed_pushNat (k : K) (c : ℕ) : (pushNat k c).Closed := closed_pushBits k _

theorem closed_copyN (src dst tmp : K) : (copyN src dst tmp).Closed :=
  SubNLogN.Machine.K1.Rot.closed_copyBlock_lift lW src dst tmp

theorem closed_dropN (k : K) : (dropN k).Closed :=
  WP.W9comp.closed_liftRegs lW (WP.W3.closed_of_noRec rfl)

theorem closed_dropF (k : K) : (dropF k).Closed :=
  SubNLogN.Machine.K1.Rot.closed_dropBits_lift lW k

theorem closed_addN (x y z t1 t2 t3 : K) : (addN x y z t1 t2 t3).Closed :=
  closed_callInj _ lA (WP.W3.addSubProg_closed _)

theorem closed_subN (x y z t1 t2 t3 : K) : (subN x y z t1 t2 t3).Closed :=
  closed_callInj _ lA (WP.W3.addSubProg_closed _)

theorem emb3_injective {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) :
    Function.Injective (emb3 x y z t1 t2 t3) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hxz, hx1, hx2, hx3⟩, ⟨hyz, hy1, hy2, hy3⟩, ⟨hz1, hz2, hz3⟩, ⟨h12, h13⟩, h23⟩ := h
  intro u v huv
  rcases u with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases v with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
  · simp only [emb3] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    simp_all

theorem emb3_inl0 (x y z t1 t2 t3 : K) : emb3 x y z t1 t2 t3 (.inl 0) = x := rfl
theorem emb3_inl1 (x y z t1 t2 t3 : K) : emb3 x y z t1 t2 t3 (.inl 1) = y := rfl
theorem emb3_inl2 (x y z t1 t2 t3 : K) : emb3 x y z t1 t2 t3 (.inl 2) = z := rfl

end Prims

/-! ## Specifications of the primitives -/

section PrimSpecs

variable {K : Type} [DecidableEq K]

theorem runs_pushMark (k : K) (S : K → List Sym) :
    Runs (pushMark k) S (Function.update S k (Sym.mark :: S k)) (fun _ => True) 1 :=
  SubNLogN.Machine.K1.runs_wk_pushC lW k .mark S

theorem runs_pushBits (k : K) : ∀ (bs : List Bool) (S : K → List Sym),
    Runs (pushBits k bs) S (Function.update S k (bs.map Sym.bit ++ S k)) (fun _ => True)
      (bs.length + 1)
  | [], S => by
    refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_rfl⟩
    refine (Eval.load [] id v S).of_eq ?_ rfl
    simp
  | b :: bs, S => by
    have h1 := runs_pushBits k bs S
    have h2 := SubNLogN.Machine.K1.runs_wk_pushC lW k (.bit b)
      (Function.update S k (bs.map Sym.bit ++ S k))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ h => h) ?_
    · rw [Function.update_idem, Function.update_self]
      rfl
    · simp only [List.length_cons]
      omega

theorem runs_pushNat (k : K) (c : ℕ) (S : K → List Sym) :
    Runs (pushNat k c) S (Function.update S k (natSyms c ++ S k)) (fun _ => True)
      (bitLen c + 1) :=
  runs_pushBits k (encodeNat c) S

theorem runs_copyN {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S src = natSyms a ++ rx) :
    Runs (copyN src dst tmp) S (Function.update S dst (natSyms a ++ S dst)) (fun _ => True)
      (7 * bitLen a + 7) :=
  SubNLogN.Machine.K1.runs_liftRegs_of_eval lW fun v =>
    ⟨some .mark, _, copyBlock_eval hsd hst hdt [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropN (k : K) (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S k = natSyms a ++ rx) :
    Runs (dropN k) S (Function.update S k rx) (fun _ => True) (2 * bitLen a + 4) :=
  SubNLogN.Machine.K1.runs_liftRegs_of_eval lW fun v =>
    ⟨_, _, WP.W3.dropNum_eval [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropF (k : K) (a : ℕ) (t : Sym) (rest : List Sym) (S : K → List Sym)
    (ht : t.isBit = false) (hS : S k = natSyms a ++ t :: rest) :
    Runs (dropF k) S (Function.update S k rest) (fun _ => True) (2 * bitLen a + 2) :=
  SubNLogN.Machine.K1.runs_wk_dropBits lW k (encodeNat a) t rest S ht hS

/-- **`addN`**: `z += a + b`; every other stack (operands and temporaries) unchanged. -/
theorem runs_addN {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (addN x y z t1 t2 t3) S (Function.update S z (natSyms (a + b) ++ S z))
      (fun _ => True) (20 * (bitLen a + bitLen b + 1)) := by
  have hι := emb3_injective h
  refine runs_callInj hι lA (Q := fun _ => True) ?_ ?_
  · have hz : (Function.update S z (natSyms (a + b) ++ S z)) ∘ emb3 x y z t1 t2 t3 =
        Function.update (S ∘ emb3 x y z t1 t2 t3) WP.W3.kZ
          (natSyms (a + b) ++ (S ∘ emb3 x y z t1 t2 t3) WP.W3.kZ) :=
      Function.update_comp_eq_of_injective S hι WP.W3.kZ _
    rw [hz]
    refine Runs.of_eval fun v => ?_
    obtain ⟨v', t, e, ht⟩ := WP.W3.addSubProg_eval WP.W3.addBit (encodeNat a) (encodeNat b) rx ry
      hrx hry (S ∘ emb3 x y z t1 t2 t3) hx hy v
    have h0 : false.toNat = 0 := rfl
    have hval : bitsVal (WP.W3.rip WP.W3.addBit (max (encodeNat a).length (encodeNat b).length)
        false (encodeNat a) (encodeNat b)) = a + b := by
      rw [WP.W3.bitsVal_rip_add (max (encodeNat a).length (encodeNat b).length) false
        (encodeNat a) (encodeNat b) (le_max_left _ _) (le_max_right _ _), bitsVal_encodeNat,
        bitsVal_encodeNat, h0, Nat.add_zero]
    rw [hval] at e
    exact ⟨v', t, e, trivial, by simp only [bitLen]; omega⟩
  · intro k hk
    rw [Function.update_of_ne]
    intro hkz
    exact hk (.inl 2) hkz.symm

/-- **`subN`**: `z += a - b` for `b ≤ a`; every other stack unchanged. -/
theorem runs_subN {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hab : b ≤ a)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (subN x y z t1 t2 t3) S (Function.update S z (natSyms (a - b) ++ S z))
      (fun _ => True) (20 * (bitLen a + bitLen b + 1)) := by
  have hι := emb3_injective h
  refine runs_callInj hι lA (Q := fun _ => True) ?_ ?_
  · have hz : (Function.update S z (natSyms (a - b) ++ S z)) ∘ emb3 x y z t1 t2 t3 =
        Function.update (S ∘ emb3 x y z t1 t2 t3) WP.W3.kZ
          (natSyms (a - b) ++ (S ∘ emb3 x y z t1 t2 t3) WP.W3.kZ) :=
      Function.update_comp_eq_of_injective S hι WP.W3.kZ _
    rw [hz]
    refine Runs.of_eval fun v => ?_
    obtain ⟨v', t, e, ht⟩ := WP.W3.addSubProg_eval WP.W3.subBit (encodeNat a) (encodeNat b) rx ry
      hrx hry (S ∘ emb3 x y z t1 t2 t3) hx hy v
    have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
      rw [bitsVal_encodeNat, bitsVal_encodeNat]
      exact hab
    have hval : bitsVal (WP.W3.rip WP.W3.subBit (max (encodeNat a).length (encodeNat b).length)
        false (encodeNat a) (encodeNat b)) = a - b := by
      rw [WP.W3.bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
        (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
        bitsVal_encodeNat]
    rw [hval] at e
    exact ⟨v', t, e, trivial, by simp only [bitLen]; omega⟩
  · intro k hk
    rw [Function.update_of_ne]
    intro hkz
    exact hk (.inl 2) hkz.symm

end PrimSpecs

/-! ## Multiplication (shift-and-add) -/

section MulDefs

variable {K : Type}

/-- Peek the top of `k` into the work register. -/
def peekW (k : K) : Prog K (fun _ => Sym) Reg := (peekR k).liftRegs lW

/-- Pop the top of `k` into the work register. -/
def popW (k : K) : Prog K (fun _ => Sym) Reg := (popR k).liftRegs lW

/-- Push the symbol `x` on `k`. -/
def pushW (k : K) (x : Sym) : Prog K (fun _ => Sym) Reg := (pushC k x).liftRegs lW

/-- Double the number on top of `k` in place (`0` stays `0`, so the result is canonical). -/
def dblN (k : K) : Prog K (fun _ => Sym) Reg :=
  .seq (peekW k) (.ite (fun r => optIsBit r.1) (pushW k (.bit false)) (.load id))

/-- Accumulate: `Acc += Bs` (via `T`; `x, y, z`, `A` serve as temporaries and are restored). -/
def mulAddStep (x y z A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (addN Acc Bs T x y z) (.seq (dropN Acc) (.seq (copyN T Acc A) (dropN T)))

/-- One iteration: the work register holds the current low bit of `A`. -/
def mulStep (x y z A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (.ite (fun r => decide (r.1 = some (Sym.bit true))) (mulAddStep x y z A Bs Acc T)
      (.load id))
    (.seq (popW A) (.seq (dblN Bs) (peekW A)))

/-- Setup of `mulN`: floors on the four temporaries, copies of the operands on `A` and `Bs`. -/
def mulSetup (x y A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark A) (.seq (copyN x A T) (.seq (pushMark Bs) (.seq (copyN y Bs T)
    (.seq (pushMark Acc) (pushMark T)))))

/-- Cleanup of `mulN`: pop the floors and copy the product onto `z`. -/
def mulPost (z A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (popW A) (.seq (dropF Bs) (.seq (popW T) (.seq (copyN Acc z T) (dropF Acc))))

/-- **`z += a * b`** (operands on `x`, `y`, restored; `A, Bs, Acc, T` temporaries, restored). -/
def mulN (x y z A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (mulSetup x y A Bs Acc T) (.seq (peekW A)
    (.seq (.loop (fun r => optIsBit r.1) (mulStep x y z A Bs Acc T)) (mulPost z A Bs Acc T)))

theorem closed_peekW (k : K) : (peekW k).Closed := SubNLogN.Machine.K1.Rot.closed_peekR_lift lW k
theorem closed_popW (k : K) : (popW k).Closed := SubNLogN.Machine.K1.Rot.closed_popR_lift lW k
theorem closed_pushW (k : K) (x : Sym) : (pushW k x).Closed :=
  SubNLogN.Machine.K1.Rot.closed_pushC_lift lW k x

theorem closed_dblN (k : K) : (dblN k).Closed :=
  ⟨closed_peekW k, closed_pushW k _, by simp [Prog.FreeBelow]⟩

theorem closed_mulStep (x y z A Bs Acc T : K) : (mulStep x y z A Bs Acc T).Closed :=
  ⟨⟨⟨closed_addN _ _ _ _ _ _, closed_dropN _, closed_copyN _ _ _, closed_dropN _⟩,
    by simp [Prog.FreeBelow]⟩, closed_popW A, closed_dblN Bs, closed_peekW A⟩

theorem closed_mulN (x y z A Bs Acc T : K) : (mulN x y z A Bs Acc T).Closed :=
  ⟨⟨closed_pushMark A, closed_copyN x A T, closed_pushMark Bs, closed_copyN y Bs T,
    closed_pushMark Acc, closed_pushMark T⟩, closed_peekW A, closed_mulStep x y z A Bs Acc T,
    closed_popW A, closed_dropF Bs, closed_popW T, closed_copyN Acc z T, closed_dropF Acc⟩

end MulDefs

section NatFacts

theorem natSyms_add_self {n : ℕ} (hn : n ≠ 0) : natSyms (n + n) = Sym.bit false :: natSyms n := by
  have h : encodeNat n ≠ [] := fun h => hn ((encodeNat_eq_nil_iff n).1 h)
  simp only [natSyms, encodeNat_add, if_neg h, List.map_cons]

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem termOK_mark (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons rfl _

theorem bitsVal_append_single (l : List Bool) (d : Bool) :
    bitsVal (l ++ [d]) = bitsVal l + 2 ^ l.length * d.toNat := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.cons_append, bitsVal_cons, ih, List.length_cons, pow_succ]
    ring

theorem bitLen_le_of_lt' {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le.2 h

theorem bitLen_mono'' {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  rw [bitLen, bitLen, IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.lt_size_self n

end NatFacts

/-! ## Specification of the multiplication -/

section MulSpec

variable {K : Type} [DecidableEq K]

theorem runs_loadId (S : K → List Sym) :
    Runs (.load id : Prog K (fun _ => Sym) Reg) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v S, trivial, le_rfl⟩

theorem runs_popW (k : K) (S : K → List Sym) :
    Runs (popW k) S (Function.update S k (S k).tail) (fun _ => True) 1 :=
  SubNLogN.Machine.K1.runs_wk_popR lW k S

theorem runs_pushW (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushW k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  SubNLogN.Machine.K1.runs_wk_pushC lW k x S

theorem triple_peekW (k : K) (S : K → List Sym) :
    Triple [] (fun s => s.stk = S) (peekW k) (fun s => s.stk = S ∧ s.var.1 = (S k).head?) 1 :=
  SubNLogN.Machine.K1.triple_peek_lens lW k S

theorem natSyms_cons_of_ne {n : ℕ} (hn : n ≠ 0) : ∃ d L, natSyms n = Sym.bit d :: L := by
  have h : encodeNat n ≠ [] := fun h => hn ((encodeNat_eq_nil_iff n).1 h)
  obtain ⟨d, L, hL⟩ := List.exists_cons_of_ne_nil h
  exact ⟨d, L.map Sym.bit, by simp [natSyms, hL]⟩

theorem optIsBit_head_natSyms (n : ℕ) (rest : List Sym) (hrest : TermOK rest) :
    optIsBit (natSyms n ++ rest).head? = decide (n ≠ 0) := by
  by_cases hn : n = 0
  · subst hn
    rw [natSyms_zero, List.nil_append]
    simp only [ne_eq, not_true_eq_false, decide_false]
    exact optIsBit_head?_of_termOK hrest
  · obtain ⟨d, L, hL⟩ := natSyms_cons_of_ne hn
    rw [hL]
    simp [optIsBit, hn]

theorem runs_dblN (k : K) (n : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms n ++ rest) :
    Runs (dblN k) S (Function.update S k (natSyms (n + n) ++ rest)) (fun _ => True) 3 := by
  have hc := optIsBit_head_natSyms n rest hrest
  refine Triple.cost_mono (Triple.seq (triple_peekW k S) (Triple.ite (T := 1) ?_ ?_)) le_rfl
  · rintro s ⟨⟨hs, hv⟩, hct⟩
    have hn : n ≠ 0 := by
      have : optIsBit s.var.1 = true := hct
      rw [hv, hS, hc] at this
      simpa using this
    have r := runs_pushW k (Sym.bit false) S s hs
    obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := r
    refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
    rw [hs', natSyms_add_self hn, hS]
    rfl
  · rintro s ⟨⟨hs, hv⟩, hcf⟩
    have hn : n = 0 := by
      have : optIsBit s.var.1 = false := hcf
      rw [hv, hS, hc] at this
      simpa using this
    obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := runs_loadId S s hs
    refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
    subst hn
    rw [natSyms_zero, List.nil_append] at hS
    rw [hs', Nat.add_zero, natSyms_zero, List.nil_append, ← hS, Function.update_eq_self]

/-- The four work stacks of `mulN` overridden on top of `S`. -/
def st4 (S : K → List Sym) (A Bs Acc T : K) (a bs acc t : List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update (Function.update S A a) Bs bs) Acc acc) T t

section St4

variable {A Bs Acc T : K} (S : K → List Sym) (a bs acc t : List Sym)

theorem st4_T : st4 S A Bs Acc T a bs acc t T = t := by simp [st4]

theorem st4_Acc (h1 : Acc ≠ T) : st4 S A Bs Acc T a bs acc t Acc = acc := by
  simp [st4, h1]

theorem st4_Bs (h1 : Bs ≠ T) (h2 : Bs ≠ Acc) : st4 S A Bs Acc T a bs acc t Bs = bs := by
  simp [st4, h1, h2]

theorem st4_A (h1 : A ≠ T) (h2 : A ≠ Acc) (h3 : A ≠ Bs) : st4 S A Bs Acc T a bs acc t A = a := by
  simp [st4, h1, h2, h3]

theorem st4_other {k : K} (h1 : k ≠ T) (h2 : k ≠ Acc) (h3 : k ≠ Bs) (h4 : k ≠ A) :
    st4 S A Bs Acc T a bs acc t k = S k := by
  simp [st4, h1, h2, h3, h4]

variable (hAB : A ≠ Bs) (hAAc : A ≠ Acc) (hAT : A ≠ T) (hBAc : Bs ≠ Acc) (hBT : Bs ≠ T)
  (hAcT : Acc ≠ T)
include hAB hAAc hAT hBAc hBT hAcT

theorem st4_upd_A (v : List Sym) :
    Function.update (st4 S A Bs Acc T a bs acc t) A v = st4 S A Bs Acc T v bs acc t := by
  funext k
  by_cases h1 : k = T <;> by_cases h2 : k = Acc <;> by_cases h3 : k = Bs <;>
    by_cases h4 : k = A <;> simp_all [st4, Function.update_apply]

theorem st4_upd_Bs (v : List Sym) :
    Function.update (st4 S A Bs Acc T a bs acc t) Bs v = st4 S A Bs Acc T a v acc t := by
  funext k
  by_cases h1 : k = T <;> by_cases h2 : k = Acc <;> by_cases h3 : k = Bs <;>
    by_cases h4 : k = A <;> simp_all [st4, Function.update_apply]

theorem st4_upd_Acc (v : List Sym) :
    Function.update (st4 S A Bs Acc T a bs acc t) Acc v = st4 S A Bs Acc T a bs v t := by
  funext k
  by_cases h1 : k = T <;> by_cases h2 : k = Acc <;> by_cases h3 : k = Bs <;>
    by_cases h4 : k = A <;> simp_all [st4, Function.update_apply]

theorem st4_upd_T (v : List Sym) :
    Function.update (st4 S A Bs Acc T a bs acc t) T v = st4 S A Bs Acc T a bs acc v := by
  funext k
  by_cases h1 : k = T <;> by_cases h2 : k = Acc <;> by_cases h3 : k = Bs <;>
    by_cases h4 : k = A <;> simp_all [st4, Function.update_apply]

theorem st4_self : st4 S A Bs Acc T (S A) (S Bs) (S Acc) (S T) = S := by
  funext k
  by_cases h1 : k = T <;> by_cases h2 : k = Acc <;> by_cases h3 : k = Bs <;>
    by_cases h4 : k = A <;> simp_all [st4]

end St4

end MulSpec

section MulCore

variable {K : Type} [DecidableEq K]

theorem bitLen_add_le' (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  apply bitLen_le_of_lt'
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem bitLen_mul_two_pow_le (b x : ℕ) : bitLen (b * 2 ^ x) ≤ bitLen b + x := by
  apply bitLen_le_of_lt'
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen b) (by positivity)

theorem loopB_le {α : Type} (B : ℕ → α → ℕ) (M : ℕ) :
    ∀ (vs : List α) (x : ℕ), (∀ j a, j < x + vs.length → B j a ≤ M) →
      SubNLogN.Machine.K1.loopB B x vs ≤ vs.length * (M + 1) + 1
  | [], _, _ => by simp [SubNLogN.Machine.K1.loopB]
  | a :: vs, x, h => by
    have ih := loopB_le B M vs (x + 1) (fun j a' hj => h j a' (by simp only [List.length_cons]; omega))
    have h0 := h x a (by simp only [List.length_cons]; omega)
    simp only [SubNLogN.Machine.K1.loopB, List.length_cons]
    nlinarith

/-- One iteration of the multiplication loop. -/
theorem triple_mulStep {x y z A Bs Acc T : K} (h : [x, y, z, A, Bs, Acc, T].Nodup)
    (S : K → List Sym) (d : Bool) (vs : List Bool) (acc bb : ℕ) :
    Triple [] (fun s => s.stk = st4 S A Bs Acc T ((d :: vs).map Sym.bit ++ Sym.mark :: S A)
        (natSyms bb ++ Sym.mark :: S Bs) (natSyms acc ++ Sym.mark :: S Acc) (Sym.mark :: S T) ∧
        s.var.1 = some (Sym.bit d))
      (mulStep x y z A Bs Acc T)
      (fun s => s.stk = st4 S A Bs Acc T (vs.map Sym.bit ++ Sym.mark :: S A)
        (natSyms (bb + bb) ++ Sym.mark :: S Bs)
        (natSyms (acc + (if d then bb else 0)) ++ Sym.mark :: S Acc) (Sym.mark :: S T) ∧
        s.var.1 = (vs.map Sym.bit ++ Sym.mark :: S A).head?)
      (40 * (bitLen acc + bitLen bb + 2)) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hxz, hxA, hxB, hxAc, hxT⟩, ⟨hyz, hyA, hyB, hyAc, hyT⟩, ⟨hzA, hzB, hzAc, hzT⟩,
    ⟨hAB, hAAc, hAT⟩, ⟨hBAc, hBT⟩, hAcT⟩ := h
  -- phase 1: the conditional accumulation
  have hph1 : Triple [] (fun s => s.stk = st4 S A Bs Acc T
        ((d :: vs).map Sym.bit ++ Sym.mark :: S A)
        (natSyms bb ++ Sym.mark :: S Bs) (natSyms acc ++ Sym.mark :: S Acc) (Sym.mark :: S T) ∧
        s.var.1 = some (Sym.bit d))
      (.ite (fun r => decide (r.1 = some (Sym.bit true))) (mulAddStep x y z A Bs Acc T) (.load id))
      (fun s => s.stk = st4 S A Bs Acc T ((d :: vs).map Sym.bit ++ Sym.mark :: S A)
        (natSyms bb ++ Sym.mark :: S Bs)
        (natSyms (acc + (if d then bb else 0)) ++ Sym.mark :: S Acc) (Sym.mark :: S T))
      (31 * (bitLen acc + bitLen bb) + 45) := by
    refine Triple.cost_mono (Triple.ite (T := 31 * (bitLen acc + bitLen bb) + 44) ?_ ?_)
      (by omega)
    · -- the bit is `true`
      rintro s ⟨⟨hs, hv⟩, hc⟩
      have hd : d = true := by
        have h1 : s.var.1 = some (Sym.bit true) := by simpa using hc
        rw [hv] at h1
        simpa using h1
      subst hd
      have hnd1 : [Acc, Bs, T, x, y, z].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          not_false_eq_true, List.nodup_nil, and_true]
        exact ⟨⟨Ne.symm hBAc, hAcT, Ne.symm hxAc, Ne.symm hyAc, Ne.symm hzAc⟩,
          ⟨hBT, Ne.symm hxB, Ne.symm hyB, Ne.symm hzB⟩, ⟨Ne.symm hxT, Ne.symm hyT, Ne.symm hzT⟩,
          ⟨hxy, hxz⟩, hyz⟩
      have r1 := runs_addN hnd1 acc bb (Sym.mark :: S Acc) (Sym.mark :: S Bs)
        (st4 S A Bs Acc T ((true :: vs).map Sym.bit ++ Sym.mark :: S A)
          (natSyms bb ++ Sym.mark :: S Bs) (natSyms acc ++ Sym.mark :: S Acc) (Sym.mark :: S T))
        (termOK_mark _) (termOK_mark _) (st4_Acc _ _ _ _ _ hAcT) (st4_Bs _ _ _ _ _ hBT hBAc)
      rw [st4_T, st4_upd_T S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r1
      have r2 := runs_dropN Acc acc (Sym.mark :: S Acc)
        (st4 S A Bs Acc T ((true :: vs).map Sym.bit ++ Sym.mark :: S A)
          (natSyms bb ++ Sym.mark :: S Bs) (natSyms acc ++ Sym.mark :: S Acc)
          (natSyms (acc + bb) ++ Sym.mark :: S T)) (termOK_mark _) (st4_Acc _ _ _ _ _ hAcT)
      rw [st4_upd_Acc S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r2
      have r3 := runs_copyN (src := T) (dst := Acc) (tmp := A) (Ne.symm hAcT) (Ne.symm hAT)
        (Ne.symm hAAc) (acc + bb) (Sym.mark :: S T)
        (st4 S A Bs Acc T ((true :: vs).map Sym.bit ++ Sym.mark :: S A)
          (natSyms bb ++ Sym.mark :: S Bs) (Sym.mark :: S Acc)
          (natSyms (acc + bb) ++ Sym.mark :: S T)) (termOK_mark _) (st4_T _ _ _ _ _)
      rw [st4_Acc _ _ _ _ _ hAcT, st4_upd_Acc S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r3
      have r4 := runs_dropN T (acc + bb) (Sym.mark :: S T)
        (st4 S A Bs Acc T ((true :: vs).map Sym.bit ++ Sym.mark :: S A)
          (natSyms bb ++ Sym.mark :: S Bs) (natSyms (acc + bb) ++ Sym.mark :: S Acc)
          (natSyms (acc + bb) ++ Sym.mark :: S T)) (termOK_mark _) (st4_T _ _ _ _ _)
      rw [st4_upd_T S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r4
      have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))
      obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := r s hs
      refine ⟨s', t, e, ?_, ?_⟩
      · show s'.stk = _
        rw [hs']
        simp
      · have e1 := bitLen_add_le' acc bb
        omega
    · -- the bit is `false`
      rintro s ⟨⟨hs, hv⟩, hc⟩
      have hc' : decide (s.var.1 = some (Sym.bit true)) = false := hc
      have hd : d = false := by
        cases d
        · rfl
        · rw [hv] at hc'
          simp at hc'
      subst hd
      obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := runs_loadId _ s hs
      refine ⟨s', t, e, ?_, by omega⟩
      show s'.stk = _
      rw [hs']
      simp
  -- phases 2-4
  have r5 := runs_popW A (st4 S A Bs Acc T ((d :: vs).map Sym.bit ++ Sym.mark :: S A)
    (natSyms bb ++ Sym.mark :: S Bs) (natSyms (acc + (if d then bb else 0)) ++ Sym.mark :: S Acc)
    (Sym.mark :: S T))
  rw [st4_A _ _ _ _ _ hAT hAAc hAB, st4_upd_A S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r5
  have r6 := runs_dblN Bs bb (Sym.mark :: S Bs) (st4 S A Bs Acc T
    (((d :: vs).map Sym.bit ++ Sym.mark :: S A).tail) (natSyms bb ++ Sym.mark :: S Bs)
    (natSyms (acc + (if d then bb else 0)) ++ Sym.mark :: S Acc) (Sym.mark :: S T)) (termOK_mark _)
    (st4_Bs _ _ _ _ _ hBT hBAc)
  rw [st4_upd_Bs S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r6
  have r7 := triple_peekW A (st4 S A Bs Acc T
    (((d :: vs).map Sym.bit ++ Sym.mark :: S A).tail) (natSyms (bb + bb) ++ Sym.mark :: S Bs)
    (natSyms (acc + (if d then bb else 0)) ++ Sym.mark :: S Acc) (Sym.mark :: S T))
  rw [st4_A _ _ _ _ _ hAT hAAc hAB] at r7
  have hrest := Triple.seq hph1 (SubNLogN.Machine.K1.runs_seq_triple r5
    (SubNLogN.Machine.K1.runs_seq_triple r6 r7))
  refine Triple.cost_mono (Triple.post hrest ?_) (by omega)
  rintro s ⟨hs, hv⟩
  exact ⟨hs, hv⟩

end MulCore

section MulMain

variable {K : Type} [DecidableEq K]

theorem bitsVal_lt_two_pow : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by simp
  | d :: l => by
    have ih := bitsVal_lt_two_pow l
    simp only [bitsVal_cons, List.length_cons, pow_succ]
    cases d <;> simp <;> omega

theorem bitLen_mul_le' (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  apply bitLen_le_of_lt'
  rw [pow_add]
  exact Nat.mul_lt_mul'' (lt_two_pow_bitLen a) (lt_two_pow_bitLen b)

/-- Cost bound of `mulN`. -/
def mulCost (a b : ℕ) : ℕ := 100 * (bitLen a + 1) * (bitLen a + bitLen b + 2)

/-- The loop of `mulN`, from the state after the setup to the state before the cleanup. -/
theorem triple_mulLoop {x y z A Bs Acc T : K} (h : [x, y, z, A, Bs, Acc, T].Nodup) (a b : ℕ)
    (S : K → List Sym) :
    Triple [] (fun s => s.stk = st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A)
        (natSyms b ++ Sym.mark :: S Bs) (Sym.mark :: S Acc) (Sym.mark :: S T) ∧
        s.var.1 = (natSyms a ++ Sym.mark :: S A).head?)
      (.loop (fun r : Reg => optIsBit r.1) (mulStep x y z A Bs Acc T))
      (fun s => s.stk = st4 S A Bs Acc T (Sym.mark :: S A)
        (natSyms (b * 2 ^ bitLen a) ++ Sym.mark :: S Bs) (natSyms (a * b) ++ Sym.mark :: S Acc)
        (Sym.mark :: S T))
      (SubNLogN.Machine.K1.loopB (fun i (_ : Bool) => 40 * (2 * (bitLen b + i) + 2)) 0
        (encodeNat a)) := by
  have hloop := SubNLogN.Machine.K1.triple_loop_list (c := fun r : Reg => optIsBit r.1)
    (body := mulStep x y z A Bs Acc T)
    (fun i (vs : List Bool) (_ : Unit) => st4 S A Bs Acc T (vs.map Sym.bit ++ Sym.mark :: S A)
      (natSyms (b * 2 ^ i) ++ Sym.mark :: S Bs)
      (natSyms (b * bitsVal ((encodeNat a).take i)) ++ Sym.mark :: S Acc) (Sym.mark :: S T))
    (fun (vs : List Bool) (r : Reg) => r.1 = (vs.map Sym.bit ++ Sym.mark :: S A).head?)
    (fun _ _ _ => ()) (fun i (_ : Bool) => 40 * (2 * (bitLen b + i) + 2))
    (fun i vs => vs = (encodeNat a).drop i)
    (fun i d vs hok => by simpa [List.tail_drop] using congrArg List.tail hok)
    (fun r hr => by
      have h1 : r.1 = some Sym.mark := hr
      show optIsBit r.1 = false
      rw [h1]
      rfl)
    (fun d vs r hr => by
      have h1 : r.1 = some (Sym.bit d) := hr
      show optIsBit r.1 = true
      rw [h1]
      rfl)
    (fun i d vs _ hok => by
      have hok' : d :: vs = (encodeNat a).drop i := hok
      have hi : i < (encodeNat a).length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hok'
        exact List.cons_ne_nil _ _ hok'
      have hget : (encodeNat a)[i]? = some d := by
        have h2 := congrArg List.head? hok'
        simpa using h2.symm
      have htake : (encodeNat a).take (i + 1) = (encodeNat a).take i ++ [d] := by
        rw [List.take_add_one, hget]
        rfl
      have hlen : ((encodeNat a).take i).length = i := List.length_take_of_le hi.le
      have hacc : b * bitsVal ((encodeNat a).take i) + (if d then b * 2 ^ i else 0) =
          b * bitsVal ((encodeNat a).take (i + 1)) := by
        rw [htake, bitsVal_append_single, hlen]
        cases d
        · simp
        · simp only [if_true, Bool.toNat_true, Nat.mul_one]
          ring
      have hbb : b * 2 ^ i + b * 2 ^ i = b * 2 ^ (i + 1) := by ring
      have hstep := triple_mulStep h S d vs (b * bitsVal ((encodeNat a).take i)) (b * 2 ^ i)
      rw [hacc, hbb] at hstep
      refine Triple.cost_mono (Triple.pre (Triple.post hstep fun s hs => hs)
        fun s hs => ⟨hs.1, hs.2⟩) ?_
      show _ ≤ 40 * (2 * (bitLen b + i) + 2)
      have hlt : bitsVal ((encodeNat a).take i) < 2 ^ i := by
        have h3 := bitsVal_lt_two_pow ((encodeNat a).take i)
        rwa [hlen] at h3
      have h4 : bitLen (b * bitsVal ((encodeNat a).take i)) ≤ bitLen b + i :=
        le_trans (bitLen_mono'' (Nat.mul_le_mul_left b hlt.le)) (bitLen_mul_two_pow_le b i)
      have h5 := bitLen_mul_two_pow_le b i
      omega)
    (encodeNat a) 0 () rfl
  have hSt0 : st4 S A Bs Acc T ((encodeNat a).map Sym.bit ++ Sym.mark :: S A)
      (natSyms (b * 2 ^ 0) ++ Sym.mark :: S Bs)
      (natSyms (b * bitsVal ((encodeNat a).take 0)) ++ Sym.mark :: S Acc) (Sym.mark :: S T) =
      st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A) (natSyms b ++ Sym.mark :: S Bs)
        (Sym.mark :: S Acc) (Sym.mark :: S T) := by
    simp only [pow_zero, Nat.mul_one, List.take_zero, bitsVal_nil, Nat.mul_zero, natSyms_zero,
      List.nil_append]
    rfl
  refine Triple.pre (Triple.post hloop ?_) ?_
  · intro s hs
    have hs' : s.stk = _ := hs
    show s.stk = _
    rw [hs']
    simp only [List.map_nil, List.nil_append, Nat.zero_add, List.take_length, bitsVal_encodeNat,
      bitLen, Nat.mul_comm b a]
  · rintro s ⟨hs1, hs2⟩
    exact ⟨hs1.trans hSt0.symm, hs2⟩

/-- **`mulN`**: `z += a * b`; the operands on `x`, `y` and the temporaries `A, Bs, Acc, T` are
restored (their initial content is arbitrary). -/
theorem runs_mulN {x y z A Bs Acc T : K} (h : [x, y, z, A, Bs, Acc, T].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (mulN x y z A Bs Acc T) S (Function.update S z (natSyms (a * b) ++ S z))
      (fun _ => True) (mulCost a b) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hxz, hxA, hxB, hxAc, hxT⟩, ⟨hyz, hyA, hyB, hyAc, hyT⟩, ⟨hzA, hzB, hzAc, hzT⟩,
    ⟨hAB, hAAc, hAT⟩, ⟨hBAc, hBT⟩, hAcT⟩ := h'
  have e0 : S = st4 S A Bs Acc T (S A) (S Bs) (S Acc) (S T) :=
    (st4_self S hAB hAAc hAT hBAc hBT hAcT).symm
  -- setup
  have r1 := runs_pushMark A (st4 S A Bs Acc T (S A) (S Bs) (S Acc) (S T))
  rw [st4_A _ _ _ _ _ hAT hAAc hAB, st4_upd_A S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r1
  have r2 := runs_copyN (src := x) (dst := A) (tmp := T) hxA hxT hAT a rx
    (st4 S A Bs Acc T (Sym.mark :: S A) (S Bs) (S Acc) (S T)) hrx
    (by rw [st4_other _ _ _ _ _ hxT hxAc hxB hxA]; exact hx)
  rw [st4_A _ _ _ _ _ hAT hAAc hAB, st4_upd_A S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r2
  have r3 := runs_pushMark Bs (st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A) (S Bs) (S Acc) (S T))
  rw [st4_Bs _ _ _ _ _ hBT hBAc, st4_upd_Bs S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r3
  have r4 := runs_copyN (src := y) (dst := Bs) (tmp := T) hyB hyT hBT b ry
    (st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A) (Sym.mark :: S Bs) (S Acc) (S T)) hry
    (by rw [st4_other _ _ _ _ _ hyT hyAc hyB hyA]; exact hy)
  rw [st4_Bs _ _ _ _ _ hBT hBAc, st4_upd_Bs S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r4
  have r5 := runs_pushMark Acc (st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A)
    (natSyms b ++ Sym.mark :: S Bs) (S Acc) (S T))
  rw [st4_Acc _ _ _ _ _ hAcT, st4_upd_Acc S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r5
  have r6 := runs_pushMark T (st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A)
    (natSyms b ++ Sym.mark :: S Bs) (Sym.mark :: S Acc) (S T))
  rw [st4_T, st4_upd_T S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r6
  have r7 := triple_peekW A (st4 S A Bs Acc T (natSyms a ++ Sym.mark :: S A)
    (natSyms b ++ Sym.mark :: S Bs) (Sym.mark :: S Acc) (Sym.mark :: S T))
  rw [st4_A _ _ _ _ _ hAT hAAc hAB] at r7
  -- the loop
  have hloop := triple_mulLoop (x := x) (y := y) (z := z) h a b S
  -- cleanup
  have r8 := runs_popW A (st4 S A Bs Acc T (Sym.mark :: S A)
    (natSyms (b * 2 ^ bitLen a) ++ Sym.mark :: S Bs) (natSyms (a * b) ++ Sym.mark :: S Acc)
    (Sym.mark :: S T))
  rw [st4_A _ _ _ _ _ hAT hAAc hAB, st4_upd_A S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r8
  have r9 := runs_dropF Bs (b * 2 ^ bitLen a) Sym.mark (S Bs) (st4 S A Bs Acc T (S A)
    (natSyms (b * 2 ^ bitLen a) ++ Sym.mark :: S Bs) (natSyms (a * b) ++ Sym.mark :: S Acc)
    (Sym.mark :: S T)) rfl (st4_Bs _ _ _ _ _ hBT hBAc)
  rw [st4_upd_Bs S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r9
  have r10 := runs_popW T (st4 S A Bs Acc T (S A) (S Bs)
    (natSyms (a * b) ++ Sym.mark :: S Acc) (Sym.mark :: S T))
  rw [st4_T, st4_upd_T S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT] at r10
  have r11 := runs_copyN (src := Acc) (dst := z) (tmp := T) (Ne.symm hzAc) hAcT hzT (a * b)
    (Sym.mark :: S Acc) (st4 S A Bs Acc T (S A) (S Bs)
      (natSyms (a * b) ++ Sym.mark :: S Acc) (S T)) (termOK_mark _)
    (st4_Acc _ _ _ _ _ hAcT)
  rw [st4_other _ _ _ _ _ hzT hzAc hzB hzA] at r11
  have r12 := runs_dropF Acc (a * b) Sym.mark (S Acc)
    (Function.update (st4 S A Bs Acc T (S A) (S Bs)
      (natSyms (a * b) ++ Sym.mark :: S Acc) (S T)) z (natSyms (a * b) ++ S z)) rfl
    (by rw [Function.update_of_ne (Ne.symm hzAc)]; exact st4_Acc _ _ _ _ _ hAcT)
  rw [Function.update_comm hzAc, st4_upd_Acc S _ _ _ _ hAB hAAc hAT hBAc hBT hAcT,
    st4_self S hAB hAAc hAT hBAc hBT hAcT] at r12
  -- assemble
  have hsetup := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 r6))))
  have hpost := WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9 (WP.W9comp.runs_seq r10
    (WP.W9comp.runs_seq r11 r12)))
  have hall := SubNLogN.Machine.K1.runs_seq_triple hsetup
    (Triple.seq r7 (Triple.seq hloop hpost))
  refine Triple.cost_mono (Triple.pre hall fun s hs => hs.trans e0) ?_
  -- the cost
  have hlb : SubNLogN.Machine.K1.loopB (fun i (_ : Bool) => 40 * (2 * (bitLen b + i) + 2)) 0
      (encodeNat a) ≤ bitLen a * (40 * (2 * (bitLen b + bitLen a) + 2) + 1) + 1 :=
    loopB_le _ _ (encodeNat a) 0 (fun j _ hj => by
      rw [Nat.zero_add] at hj
      have hj' : j < bitLen a := hj
      show 40 * (2 * (bitLen b + j) + 2) ≤ 40 * (2 * (bitLen b + bitLen a) + 2)
      omega)
  have e1 := bitLen_mul_two_pow_le b (bitLen a)
  have e2 := bitLen_mul_le' a b
  simp only [mulCost]
  nlinarith [hlb, e1, e2, Nat.zero_le (bitLen a * bitLen b), Nat.zero_le (bitLen a * bitLen a)]

end MulMain

/-! ## Multiplication by a constant, and by a power of a constant -/

section MulConst

variable {K : Type}

/-- **`a ↦ a * c`** in place on `k` (`c` a compile-time constant). `Q` (holds `c`), `Tdst`
(holds the product) and `A, Bs, Acc, T` (temporaries of `mulN`) are restored. -/
def mulConstN (k : K) (c : ℕ) (Q Tdst A Bs Acc T : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushMark Q) (.seq (pushNat Q c) (.seq (pushMark Tdst) (.seq (mulN k Q Tdst A Bs Acc T)
    (.seq (dropN k) (.seq (copyN Tdst k A) (.seq (dropF Tdst) (dropF Q)))))))

/-- **`a ↦ a * c ^ n`** in place on `k`, `n` read from the counter on `ns` (restored); `Kc, t`
are the loop counter and its temporary, `Q, Tdst, A, Bs, Acc` the temporaries of `mulConstN`
(all restored). -/
def powMulN (k : K) (c : ℕ) (ns Kc t Q Tdst A Bs Acc : K) : Prog K (fun _ => Sym) Reg :=
  SubNLogN.Machine.K1.Rot.nLoop lW ns Kc t (mulConstN k c Q Tdst A Bs Acc t)

theorem closed_mulConstN (k : K) (c : ℕ) (Q Tdst A Bs Acc T : K) :
    (mulConstN k c Q Tdst A Bs Acc T).Closed :=
  ⟨closed_pushMark Q, closed_pushNat Q c, closed_pushMark Tdst, closed_mulN k Q Tdst A Bs Acc T,
    closed_dropN k, closed_copyN Tdst k A, closed_dropF Tdst, closed_dropF Q⟩

theorem closed_powMulN (k : K) (c : ℕ) (ns Kc t Q Tdst A Bs Acc : K) :
    (powMulN k c ns Kc t Q Tdst A Bs Acc).Closed :=
  SubNLogN.Machine.K1.Rot.closed_nLoop lW ns Kc t (closed_mulConstN k c Q Tdst A Bs Acc t)

/-- Cost bound of `mulConstN`. -/
def mulConstCost (a c : ℕ) : ℕ :=
  mulCost a c + 2 * bitLen a + 9 * bitLen (a * c) + 3 * bitLen c + 18

/-- Cost bound of `powMulN` (with `1 ≤ c`). -/
def powCost (c a n : ℕ) : ℕ := (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2)

theorem mulConstCost_le {a c L : ℕ} (ha : bitLen a ≤ L) :
    mulConstCost a c ≤ 114 * (L + bitLen c + 2) ^ 2 + 9 * bitLen (a * c) := by
  have h1 : (bitLen a + 1) * (bitLen a + bitLen c + 2) ≤
      (L + bitLen c + 2) * (L + bitLen c + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * (L + bitLen c + 2) ≤ (L + bitLen c + 2) * (L + bitLen c + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [mulConstCost, mulCost]
  nlinarith [h1, h2]

theorem sum_range_le {f : ℕ → ℕ} {M : ℕ} :
    ∀ n, (∀ j, j < n → f j ≤ M) → ((List.range n).map f).sum ≤ n * M
  | 0, _ => by simp
  | n + 1, h => by
    have ih := sum_range_le n (fun j hj => h j (by omega))
    have h1 := h n (by omega)
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.succ_mul]
    omega

end MulConst

section MulConstSpec

variable {K : Type} [DecidableEq K]

/-- **`mulConstN`**: `S k = natSyms a ++ rk` becomes `natSyms (a * c) ++ rk`; every other stack
(in particular the six temporaries, whose initial content is arbitrary) is unchanged. -/
theorem runs_mulConstN {k Q Tdst A Bs Acc T : K} (h : [k, Q, Tdst, A, Bs, Acc, T].Nodup)
    (c a : ℕ) (rk : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hk : S k = natSyms a ++ rk) :
    Runs (mulConstN k c Q Tdst A Bs Acc T) S (Function.update S k (natSyms (a * c) ++ rk))
      (fun _ => True) (mulConstCost a c) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkQ, hkD, hkA, -, -, -⟩, ⟨hQD, hQA, -, -, -⟩, ⟨hDA, -, -, -⟩, -, -, -⟩ := h'
  have uQ : ∀ u1 u2 u3 u4 v, Function.update (st4 S Q Tdst k A u1 u2 u3 u4) Q v =
      st4 S Q Tdst k A v u2 u3 u4 := fun u1 u2 u3 u4 v =>
    st4_upd_A S u1 u2 u3 u4 hQD (Ne.symm hkQ) hQA (Ne.symm hkD) hDA hkA v
  have uD : ∀ u1 u2 u3 u4 v, Function.update (st4 S Q Tdst k A u1 u2 u3 u4) Tdst v =
      st4 S Q Tdst k A u1 v u3 u4 := fun u1 u2 u3 u4 v =>
    st4_upd_Bs S u1 u2 u3 u4 hQD (Ne.symm hkQ) hQA (Ne.symm hkD) hDA hkA v
  have uk : ∀ u1 u2 u3 u4 v, Function.update (st4 S Q Tdst k A u1 u2 u3 u4) k v =
      st4 S Q Tdst k A u1 u2 v u4 := fun u1 u2 u3 u4 v =>
    st4_upd_Acc S u1 u2 u3 u4 hQD (Ne.symm hkQ) hQA (Ne.symm hkD) hDA hkA v
  have gQ : ∀ u1 u2 u3 u4, st4 S Q Tdst k A u1 u2 u3 u4 Q = u1 := fun u1 u2 u3 u4 =>
    st4_A S u1 u2 u3 u4 hQA (Ne.symm hkQ) hQD
  have gD : ∀ u1 u2 u3 u4, st4 S Q Tdst k A u1 u2 u3 u4 Tdst = u2 := fun u1 u2 u3 u4 =>
    st4_Bs S u1 u2 u3 u4 hDA (Ne.symm hkD)
  have gk : ∀ u1 u2 u3 u4, st4 S Q Tdst k A u1 u2 u3 u4 k = u3 := fun u1 u2 u3 u4 =>
    st4_Acc S u1 u2 u3 u4 hkA
  have e0 : S = st4 S Q Tdst k A (S Q) (S Tdst) (S k) (S A) :=
    (st4_self S hQD (Ne.symm hkQ) hQA (Ne.symm hkD) hDA hkA).symm
  have r1 := runs_pushMark Q (st4 S Q Tdst k A (S Q) (S Tdst) (S k) (S A))
  rw [gQ, uQ] at r1
  have r2 := runs_pushNat Q c (st4 S Q Tdst k A (Sym.mark :: S Q) (S Tdst) (S k) (S A))
  rw [gQ, uQ] at r2
  have r3 := runs_pushMark Tdst
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (S Tdst) (S k) (S A))
  rw [gD, uD] at r3
  have r4 := runs_mulN (x := k) (y := Q) (z := Tdst) (A := A) (Bs := Bs) (Acc := Acc) (T := T)
    h a c rk (Sym.mark :: S Q)
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (Sym.mark :: S Tdst) (S k) (S A))
    hrk (termOK_mark _) ((gk _ _ _ _).trans hk) (gQ _ _ _ _)
  rw [gD, uD] at r4
  have r5 := runs_dropN k a rk
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (natSyms (a * c) ++ Sym.mark :: S Tdst)
      (S k) (S A)) hrk ((gk _ _ _ _).trans hk)
  rw [uk] at r5
  have r6 := runs_copyN (src := Tdst) (dst := k) (tmp := A) (Ne.symm hkD) hDA hkA (a * c)
    (Sym.mark :: S Tdst)
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (natSyms (a * c) ++ Sym.mark :: S Tdst)
      rk (S A)) (termOK_mark _) (gD _ _ _ _)
  rw [gk, uk] at r6
  have r7 := runs_dropF Tdst (a * c) Sym.mark (S Tdst)
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (natSyms (a * c) ++ Sym.mark :: S Tdst)
      (natSyms (a * c) ++ rk) (S A)) rfl (gD _ _ _ _)
  rw [uD] at r7
  have r8 := runs_dropF Q c Sym.mark (S Q)
    (st4 S Q Tdst k A (natSyms c ++ Sym.mark :: S Q) (S Tdst) (natSyms (a * c) ++ rk) (S A)) rfl
    (gQ _ _ _ _)
  rw [uQ] at r8
  have hfin : st4 S Q Tdst k A (S Q) (S Tdst) (natSyms (a * c) ++ rk) (S A) =
      Function.update S k (natSyms (a * c) ++ rk) := by
    rw [← uk (S Q) (S Tdst) (S k) (S A), st4_self S hQD (Ne.symm hkQ) hQA (Ne.symm hkD) hDA hkA]
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 r8))))))
  rw [hfin] at hall
  refine Triple.cost_mono (Triple.pre hall fun s hs => hs.trans e0) ?_
  simp only [mulConstCost]
  omega

/-- **`powMulN`** (`1 ≤ c`): `S k = natSyms a ++ rk` becomes `natSyms (a * c ^ n) ++ rk`, where
`S ns = natSyms n ++ rn`; every other stack (the counter on `ns` and the seven temporaries, whose
initial content is arbitrary) is unchanged. -/
theorem runs_powMulN {k ns Kc t Q Tdst A Bs Acc : K}
    (h : [k, ns, Kc, t, Q, Tdst, A, Bs, Acc].Nodup) (c : ℕ) (hc : 1 ≤ c) (a n : ℕ)
    (rk rn : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrn : TermOK rn)
    (hk : S k = natSyms a ++ rk) (hn : S ns = natSyms n ++ rn) :
    Runs (powMulN k c ns Kc t Q Tdst A Bs Acc) S
      (Function.update S k (natSyms (a * c ^ n) ++ rk)) (fun _ => True) (powCost c a n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkn, hkK, hkt, hkQ, hkD, hkA, hkB, hkAc⟩, ⟨hnK, hnt, -, -, -, -, -⟩,
    ⟨hKt, -, -, -, -, -⟩, ⟨htQ, htD, htA, htB, htAc⟩, ⟨hQD, hQA, hQB, hQAc⟩,
    ⟨hDA, hDB, hDAc⟩, ⟨hAB, hAAc⟩, hBAc⟩ := h'
  have hnd7 : [k, Q, Tdst, A, Bs, Acc, t].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨hkQ, hkD, hkA, hkB, hkAc, hkt⟩, ⟨hQD, hQA, hQB, hQAc, Ne.symm htQ⟩,
      ⟨hDA, hDB, hDAc, Ne.symm htD⟩, ⟨hAB, hAAc, Ne.symm htA⟩, ⟨hBAc, Ne.symm htB⟩, Ne.symm htAc⟩
  have r := SubNLogN.Machine.K1.Rot.runs_nLoop lW hnK hnt hKt (mulConstN k c Q Tdst A Bs Acc t)
    (fun j => Function.update S k (natSyms (a * c ^ j) ++ rk)) n rn hrn
    ((Function.update_of_ne (Ne.symm hkn) _ _).trans hn)
    ((Function.update_of_ne (Ne.symm hkK) _ _).trans
      (Function.update_of_ne (Ne.symm hkK) _ _).symm)
    (fun j => mulConstCost (a * c ^ j) c)
    (fun j _ => by
      have hpow : a * c ^ j * c = a * c ^ (j + 1) := by rw [pow_succ, mul_assoc]
      have r0 := runs_mulConstN hnd7 c (a * c ^ j) rk
        (Function.update (Function.update S k (natSyms (a * c ^ j) ++ rk)) Kc
          (natSyms (n - (j + 1)) ++
            Sym.mark :: Function.update S k (natSyms (a * c ^ 0) ++ rk) Kc))
        hrk (by rw [Function.update_of_ne hkK, Function.update_self])
      rw [hpow] at r0
      refine WP.W9comp.runs_congr r0 ?_
      show _ = Function.update (Function.update S k (natSyms (a * c ^ (j + 1)) ++ rk)) Kc
        (natSyms (n - (j + 1)) ++ Sym.mark :: Function.update S k (natSyms (a * c ^ 0) ++ rk) Kc)
      rw [Function.update_comm hkK, Function.update_comm hkK, Function.update_idem])
  have hS0 : Function.update S k (natSyms (a * c ^ 0) ++ rk) = S := by
    rw [pow_zero, Nat.mul_one, ← hk, Function.update_eq_self]
  rw [hS0] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  -- the cost
  have hX2 : 2 ≤ bitLen (a * c ^ n) + bitLen c + 2 := by omega
  have hXX : 2 * (bitLen (a * c ^ n) + bitLen c + 2) ≤
      (bitLen (a * c ^ n) + bitLen c + 2) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hX2
  have hterm : ∀ j, j < n →
      mulConstCost (a * c ^ j) c ≤ 120 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2 := by
    intro j hj
    have h1 : bitLen (a * c ^ j) ≤ bitLen (a * c ^ n) :=
      bitLen_mono'' (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hc hj.le))
    have h2 : bitLen (a * c ^ j * c) ≤ bitLen (a * c ^ n) := by
      rw [mul_assoc, ← pow_succ]
      exact bitLen_mono'' (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hc hj))
    have h3 := mulConstCost_le (c := c) h1
    nlinarith [h3, h2, hXX]
  have hsum := sum_range_le n hterm
  have hbn : bitLen n ≤ n := bitLen_le_of_lt' Nat.lt_two_pow_self
  have hX4 : 4 ≤ (bitLen (a * c ^ n) + bitLen c + 2) ^ 2 := by nlinarith [hXX, hX2]
  have hnX := Nat.mul_le_mul_left n hX4
  show _ ≤ (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2)
  nlinarith [hsum, hbn, hX4, hnX]

end MulConstSpec

end SubNLogN.Machine.NatArith
