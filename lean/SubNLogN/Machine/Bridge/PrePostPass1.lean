/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostLoop

/-!
# K5-PP pass 1 (`Bridge/PrePostPass1.lean`): tagging the input fields

First pass of the pre-scaling scan (Section 4.4 (`sec:bridge-alg`), step (1); Theorem 4.7 (`thm:bridge-precision`): "scan `x` once to find `H`").
The source holds one-coefficient records `coefBits w c ++ [sep]` (`Contracts/Records.lean`); a
counter stack `T` holds `w` bits `false`. Each `w`-bit field `b_0 … b_{w-1}` (LSB first) is popped
and its bits are pushed onto `Y` as **tags** `tagOf b_k f_k`, where `f_k = b_0 ∨ … ∨ b_{k-1}`
(some lower bit is set); the record end `sep` is moved too. Since `Y` receives the symbols in
reverse, pass 2 (`PrePostPass2.lean`) reads every field most significant bit first, together with
the lower-bits flags it needs.

**Scope (honest summary).** Programs and proved `Eval`/`Runs` lemmas (no `sorry`):
`p1Loop_eval` (one field, exact), `runs_p1Field`, `runs_p1Rec` (one record), `runs_p1Arr` (the
whole array; cost `≤ R·(14 w + 13) + 2`).
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

/-! ## Tags -/

/-- The tag of a bit `b` with lower-bits flag `f`: `tag (2b + f)`. -/
def tagOf (b f : Bool) : Sym :=
  .tag ⟨(if b then 2 else 0) + (if f then 1 else 0), by split_ifs <;> decide⟩

/-- The bit of a tag. -/
def tagB : Option Sym → Bool
  | some (.tag t) => decide (2 ≤ t.val)
  | _ => false

/-- The lower-bits flag of a tag. -/
def tagF : Option Sym → Bool
  | some (.tag t) => decide (t.val % 2 = 1)
  | _ => false

@[simp] theorem tagB_tagOf (b f : Bool) : tagB (some (tagOf b f)) = b := by
  cases b <;> cases f <;> rfl

@[simp] theorem tagF_tagOf (b f : Bool) : tagF (some (tagOf b f)) = f := by
  cases b <;> cases f <;> rfl

theorem tagOf_ne_sep (b f : Bool) : tagOf b f ≠ Sym.sep := by
  cases b <;> cases f <;> simp [tagOf]

/-- The tags of a field (LSB first), from the flag `f` of the bits below it. -/
def tagList : Bool → List Bool → List Sym
  | _, [] => []
  | f, b :: bs => tagOf b f :: tagList (f || b) bs

@[simp] theorem length_tagList : ∀ (f : Bool) (bs : List Bool), (tagList f bs).length = bs.length
  | _, [] => rfl
  | f, _ :: bs => by simp [tagList, length_tagList _ bs]

/-! ## Programs -/

variable {K : Type}

/-- Pass 1, one bit: pop the source bit, push its tag on `Y`, update `f`, move one counter bit
from `T` to `T2`. -/
def p1Body (src Y T T2 : K) : PProg K :=
  .seq (.pop src fun v o => { v with o := o })
  (.seq (.push Y fun v => tagOf (bitOf v.o) v.f)
  (.seq (.load fun v => { v with f := v.f || bitOf v.o })
  (.seq (.pop T fun v _ => v)
  (.seq (.push T2 fun _ => .bit false)
    (peekT T)))))

/-- Pass 1, the loop over the bits of one field (driven by the counter `T`). -/
def p1Loop (src Y T T2 : K) : PProg K := .loop (fun v => isBitO v.t) (p1Body src Y T T2)

/-- Pass 1, one field. -/
def p1Field (src Y T T2 : K) : PProg K :=
  .seq (.load fun v => { v with f := false }) (.seq (peekT T) (p1Loop src Y T T2))

/-- Pass 1, one record: two fields (the counter goes `T → T2 → T`), then the record end. -/
def p1Rec (src Y T T2 : K) : PProg K :=
  .seq (p1Field src Y T T2) (.seq (p1Field src Y T2 T) ((moveSym src Y).liftRegs lensPO))

/-- Pass 1, the array loop (while the source shows a bit). -/
def p1Arr (src Y T T2 : K) : PProg K :=
  .seq (peekT src) (.loop (fun v => isBitO v.t) (.seq (p1Rec src Y T T2) (peekT src)))

theorem closed_p1Arr (src Y T T2 : K) : (p1Arr src Y T T2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, p1Arr, p1Rec, p1Field, p1Loop, p1Body, peekT, moveSym, popR,
    pushR, Prog.liftRegs]

/-! ## One field -/

section Eval

variable [DecidableEq K]

theorem p1Body_eval {src Y T T2 : K} (h1 : src ≠ Y) (h2 : src ≠ T) (h3 : src ≠ T2) (h4 : Y ≠ T)
    (h5 : Y ≠ T2) (h6 : T ≠ T2) (b : Bool) (Ls LT : List Sym) (v : PReg) (S : K → List Sym)
    (hsrc : S src = Sym.bit b :: Ls) (hT : S T = Sym.bit false :: LT) :
    Eval [] (p1Body src Y T T2) ⟨v, S⟩
      ⟨{ v with o := some (.bit b), f := v.f || b, t := LT.head? },
        Function.update (Function.update (Function.update (Function.update S src Ls) Y
          (tagOf b v.f :: S Y)) T LT) T2 (Sym.bit false :: S T2)⟩ 6 := by
  have e := Eval.seq (Eval.pop (Γ := fun _ => Sym) [] src (fun v o => { v with o := o }) v S)
    (Eval.seq (Eval.push (Γ := fun _ => Sym) [] Y (fun v : PReg => tagOf (bitOf v.o) v.f) _ _)
    (Eval.seq (Eval.load (Γ := fun _ => Sym) [] (fun v : PReg => { v with f := v.f || bitOf v.o })
      _ _)
    (Eval.seq (Eval.pop (Γ := fun _ => Sym) [] T (fun v _ => v) _ _)
    (Eval.seq (Eval.push (Γ := fun _ => Sym) [] T2 (fun _ : PReg => Sym.bit false) _ _)
      (Eval.peek (Γ := fun _ => Sym) [] T (fun v o => { v with t := o }) _ _)))))
  refine e.of_eq ?_ rfl
  have hT' : Function.update (Function.update S src Ls) Y (tagOf b v.f :: S Y) T = Sym.bit false :: LT := by
    rw [Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, hT]
  simp only [hsrc, List.head?_cons, List.tail_cons, bitOf_bit, hT', Function.update_of_ne h1.symm,
    Function.update_of_ne h5.symm, Function.update_of_ne h6.symm, Function.update_of_ne h3.symm]
  congr 1
  rw [Function.update_of_ne h6, Function.update_self]

theorem p1Loop_eval {src Y T T2 : K} (h1 : src ≠ Y) (h2 : src ≠ T) (h3 : src ≠ T2) (h4 : Y ≠ T)
    (h5 : Y ≠ T2) (h6 : T ≠ T2) :
    ∀ (bs : List Bool) (L DT : List Sym) (v : PReg) (S : K → List Sym), TermOK DT →
      S src = bs.map Sym.bit ++ L → S T = List.replicate bs.length (Sym.bit false) ++ DT →
      v.t = (S T).head? →
      ∃ v' : PReg, Eval [] (p1Loop src Y T T2) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S src L) Y
          ((tagList v.f bs).reverse ++ S Y)) T DT) T2
          (List.replicate bs.length (Sym.bit false) ++ S T2)⟩ (7 * bs.length + 1)
  | [], L, DT, v, S, hDT, hsrc, hT, hv => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.map_nil] at hT hsrc
    refine ⟨v, (Eval.loop_false ?_).of_eq ?_ rfl⟩
    · show isBitO v.t = false
      rw [hv, hT]
      exact isBitO_of_termOK hDT
    · simp only [tagList, List.reverse_nil, List.nil_append, List.length_nil, List.replicate_zero]
      rw [← hsrc, ← hT, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self]
  | b :: bs, L, DT, v, S, hDT, hsrc, hT, hv => by
    simp only [List.map_cons, List.cons_append, List.length_cons, List.replicate_succ] at hsrc hT
    have eb := p1Body_eval h1 h2 h3 h4 h5 h6 b (bs.map Sym.bit ++ L)
      (List.replicate bs.length (Sym.bit false) ++ DT) v S hsrc hT
    set S5 := Function.update (Function.update (Function.update (Function.update S src
      (bs.map Sym.bit ++ L)) Y (tagOf b v.f :: S Y)) T
      (List.replicate bs.length (Sym.bit false) ++ DT)) T2 (Sym.bit false :: S T2) with hS5
    have h5src : S5 src = bs.map Sym.bit ++ L := by
      rw [hS5, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
        Function.update_self]
    have h5T : S5 T = List.replicate bs.length (Sym.bit false) ++ DT := by
      rw [hS5, Function.update_of_ne h6, Function.update_self]
    obtain ⟨v', e'⟩ := p1Loop_eval h1 h2 h3 h4 h5 h6 bs L DT
      { v with
        o := some (.bit b), f := v.f || b,
        t := (List.replicate bs.length (Sym.bit false) ++ DT).head? } S5 hDT h5src h5T
      (by rw [h5T])
    refine ⟨v', (Eval.loop_true ?_ eb e').of_eq ?_ (by simp only [List.length_cons]; ring)⟩
    · show isBitO v.t = true
      rw [hv, hT]
      rfl
    · congr 1
      have hY : S5 Y = tagOf b v.f :: S Y := by
        rw [hS5, Function.update_of_ne h5, Function.update_of_ne h4, Function.update_self]
      have hT2 : S5 T2 = Sym.bit false :: S T2 := by rw [hS5, Function.update_self]
      rw [hY, hT2]
      funext k
      simp only [hS5, Function.update_apply, tagList, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all [List.replicate_succ']

/-- **Pass 1, one field**, as `Runs` (any register). -/
theorem runs_p1Field {src Y T T2 : K} (h1 : src ≠ Y) (h2 : src ≠ T) (h3 : src ≠ T2) (h4 : Y ≠ T)
    (h5 : Y ≠ T2) (h6 : T ≠ T2) (bs : List Bool) (L DT : List Sym) (S : K → List Sym)
    (hDT : TermOK DT) (hsrc : S src = bs.map Sym.bit ++ L)
    (hT : S T = List.replicate bs.length (Sym.bit false) ++ DT) :
    Runs (p1Field src Y T T2) S
      (Function.update (Function.update (Function.update (Function.update S src L) Y
        ((tagList false bs).reverse ++ S Y)) T DT) T2
        (List.replicate bs.length (Sym.bit false) ++ S T2)) (fun _ => True) (7 * bs.length + 3) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', e'⟩ := p1Loop_eval h1 h2 h3 h4 h5 h6 bs L DT
    { { v with f := false } with t := (S T).head? } S hDT hsrc hT rfl
  exact ⟨v', _, Eval.seq (Eval.load [] _ v S) (Eval.seq (Eval.peek [] T _ _ S) e'), trivial,
    by omega⟩

/-! ## Records and the array -/

/-- `twosBits w z` has length `w`. -/
theorem length_twosBits' (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

/-- The stack content of one input record `[c]` (`carrSyms`, `Contracts/Records.lean`). -/
def recC (w : ℕ) (c : CInt) : List Sym :=
  (twosBits w c.1 ++ twosBits w c.2).map Sym.bit ++ [Sym.sep]

/-- What pass 1 pushes on `Y` for one record (top first). -/
def yRec (w : ℕ) (c : CInt) : List Sym :=
  Sym.sep :: ((tagList false (twosBits w c.2)).reverse ++ (tagList false (twosBits w c.1)).reverse)

/-- **Pass 1, one record.** -/
theorem runs_p1Rec {src Y T T2 : K} (h1 : src ≠ Y) (h2 : src ≠ T) (h3 : src ≠ T2) (h4 : Y ≠ T)
    (h5 : Y ≠ T2) (h6 : T ≠ T2) (w : ℕ) (c : CInt) (L DT : List Sym) (S : K → List Sym)
    (hDT : TermOK DT) (hT2 : TermOK (S T2)) (hsrc : S src = recC w c ++ L)
    (hT : S T = List.replicate w (Sym.bit false) ++ DT) :
    Runs (p1Rec src Y T T2) S (Function.update (Function.update S src L) Y (yRec w c ++ S Y))
      (fun _ => True) (14 * w + 8) := by
  have hsrc1 : S src = (twosBits w c.1).map Sym.bit ++
      ((twosBits w c.2).map Sym.bit ++ Sym.sep :: L) := by
    rw [hsrc]
    simp [recC]
  have r1 := runs_p1Field h1 h2 h3 h4 h5 h6 (twosBits w c.1) _ DT S hDT hsrc1
    (by rw [length_twosBits', hT])
  rw [length_twosBits'] at r1
  set S1 := Function.update (Function.update (Function.update (Function.update S src
    ((twosBits w c.2).map Sym.bit ++ Sym.sep :: L)) Y
    ((tagList false (twosBits w c.1)).reverse ++ S Y)) T DT) T2
    (List.replicate w (Sym.bit false) ++ S T2) with hS1
  have r2 := runs_p1Field h1 h3 h2 h5 h4 h6.symm (twosBits w c.2) (Sym.sep :: L) (S T2) S1 hT2
    (by rw [hS1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_self])
    (by rw [hS1, Function.update_self, length_twosBits'])
  rw [length_twosBits'] at r2
  set S2 := Function.update (Function.update (Function.update (Function.update S1 src
    (Sym.sep :: L)) Y ((tagList false (twosBits w c.2)).reverse ++ S1 Y)) T2 (S T2)) T
    (List.replicate w (Sym.bit false) ++ S1 T) with hS2
  have r3 := runs_liftRegs lensPO (runs_moveSym h1 Sym.sep L S2
    (by rw [hS2, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1,
      Function.update_self]))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1
    (WP.W9comp.runs_seq r2 r3)) ?_) (fun _ _ => trivial) (by omega)
  funext k
  simp only [hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all [yRec]

theorem head_recC_isBit {w : ℕ} (hw : 1 ≤ w) (c : CInt) (L : List Sym) :
    isBitO (recC w c ++ L).head? = true := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp [recC, twosBits, bitsLE, List.range_succ_eq_map]

theorem isBitO_of_blkTerm {L : List Sym} (h : BlkTerm L) : isBitO L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · obtain ⟨hd, -⟩ := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [isDataSym]

/-- **Pass 1, the whole array.** -/
theorem runs_p1Arr {src Y T T2 : K} (h1 : src ≠ Y) (h2 : src ≠ T) (h3 : src ≠ T2) (h4 : Y ≠ T)
    (h5 : Y ≠ T2) (h6 : T ≠ T2) {w : ℕ} (hw : 1 ≤ w) (cs : List CInt) (rsrc DT : List Sym)
    (S : K → List Sym) (hDT : TermOK DT) (hT2 : TermOK (S T2)) (hrsrc : BlkTerm rsrc)
    (hsrc : S src = (cs.map (recC w)).flatten ++ rsrc)
    (hT : S T = List.replicate w (Sym.bit false) ++ DT) :
    Runs (p1Arr src Y T T2) S
      (Function.update (Function.update S src rsrc) Y ((cs.reverse.map (yRec w)).flatten ++ S Y))
      (fun _ => True) (cs.length * (14 * w + 10) + 2) := by
  let st : List CInt → List CInt → K → List Sym := fun done rest =>
    Function.update (Function.update S src ((rest.map (recC w)).flatten ++ rsrc)) Y
      ((done.reverse.map (yRec w)).flatten ++ S Y)
  have h0 : st [] cs = S := by
    simp only [st, List.reverse_nil, List.map_nil, List.flatten_nil, List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  have hw' := runs_while (pk := peekT src) (body := p1Rec src Y T T2)
    (c := fun v => isBitO v.t) st 1 (fun _ _ _ => 14 * w + 8)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT src (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h1, Function.update_self] at hv ⊢
      rw [hv]
      rcases rest with _ | ⟨x, rest⟩
      · simpa using isBitO_of_blkTerm hrsrc
      · simp only [List.map_cons, List.flatten_cons, List.append_assoc]
        rw [head_recC_isBit hw]
        rfl)
    (fun done x rest => by
      have hr := runs_p1Rec h1 h2 h3 h4 h5 h6 w x ((rest.map (recC w)).flatten ++ rsrc) DT
        (st done (x :: rest)) hDT
        (by simp only [st, Function.update_of_ne h3.symm, Function.update_of_ne h5.symm]; exact hT2)
        (by simp [st, Function.update_of_ne h1])
        (by simp only [st, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm]; exact hT)
      refine WP.W9comp.runs_congr hr ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all)
    cs []
  rw [h0] at hw'
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw' ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 (14 * w + 8) (fun _ _ _ => 14 * w + 8) (fun _ _ _ => le_rfl) cs []
    nlinarith

end Eval

end SubNLogN.Machine.BridgePP
