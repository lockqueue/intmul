/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Park
import WP.W0m.Macros

/-!
# Framed procedure calculus, layer 3 (`Calculus/Desc.lean`): the descriptor stack

A recursive procedure reads its call descriptor from the top of a descriptor stack `d`. Before a
child call the parent pushes the child's descriptor above a `mark`, keeping its own descriptor
below; after the return it pops the child's descriptor. Ancestors' descriptors are never read.
The descriptor here is one counter `natSyms k`; multi-field descriptors (`hdrSyms`) follow the same
pattern with their own field arithmetic.

* `pushPred d t1 t2`: `d = natSyms (k+1) ++ tl` ↦ `d = natSyms k ++ mark :: natSyms (k+1) ++ tl`
  (temporaries `t1`, `t2` restored), cost `≤ 22·bitLen (k+1) + 29` (`runs_pushPred`).
* `popDesc d`: `d = natSyms k ++ mark :: tl` ↦ `d = tl`, cost `2·bitLen k + 5` (`runs_popDesc`).
* `runs_descRec`: the **depth-first recursion pattern**. The body is
  `zeroTest d ; ite (top of d is a bit) internal leaf`; the leaf runs at descriptor `0`, the
  internal branch at descriptors `> 0` may call `recur 0` on any spec instance with a smaller
  descriptor. Then `fix body` meets the whole spec family.
-/

namespace SubNLogN.Machine.Calculus

open Computability TMFw TMFw.Contracts TMFw.Lib

section Programs

variable {K : Type}

/-- **Push the predecessor descriptor** above a `mark`, keeping the parent's descriptor below. -/
def pushPred (d t1 t2 : K) : SProg K :=
  .seq (pushC t1 .mark) (.seq (copyBlock d t1 t2) (.seq (pushC d .mark) (.seq (copyBlock t1 d t2)
    (.seq (WP.W0m.dropNat t1) (.seq (popR t1) (dec d t2))))))

/-- **Pop a child descriptor** and its `mark`. -/
def popDesc (d : K) : SProg K := .seq (WP.W0m.dropNat d) (popR d)

theorem closed_pushPred (d t1 t2 : K) : (pushPred d t1 t2).Closed := by
  simp [Prog.Closed, pushPred, Prog.FreeBelow, pushC, popR, pushR, copyBlock, moveBlock,
    moveBits, moveBitsBody, moveBitsDup, dupBody, restoreR, Lib.skip, WP.W0m.dropNat,
    WP.W0m.dropLoop, dec, decFix, scanLoop, scanBody, peekR]

theorem closed_popDesc (d : K) : (popDesc d).Closed := by
  simp [Prog.Closed, popDesc, Prog.FreeBelow, popR, pushR, restoreR, Lib.skip, WP.W0m.dropNat,
    WP.W0m.dropLoop]

end Programs

section Eval

variable {K : Type} [DecidableEq K]

/-- **pushPred**, exact. -/
theorem pushPred_eval {d t1 t2 : K} (hd1 : d ≠ t1) (hd2 : d ≠ t2) (h12 : t1 ≠ t2)
    (ρ : List (SProg K)) (v : Option Sym) (k : ℕ) (tl : List Sym) (S : K → List Sym)
    (htl : TermOK tl) (hS : S d = natSyms (k + 1) ++ tl) :
    ∃ t, t ≤ 22 * bitLen (k + 1) + 29 ∧ Eval ρ (pushPred d t1 t2) ⟨v, S⟩
      ⟨some .mark, Function.update S d (natSyms k ++ Sym.mark :: (natSyms (k + 1) ++ tl))⟩ t := by
  set L := encodeNat (k + 1) with hL
  have e0 : Eval ρ (pushC t1 .mark) ⟨v, S⟩ ⟨v, Function.update S t1 (.mark :: S t1)⟩ 1 :=
    Eval.push ρ t1 (fun _ => .mark) v S
  set S0 := Function.update S t1 (.mark :: S t1) with hS0
  have e1 := copyBlock_eval hd1 hd2 h12 ρ v L tl S0 htl
    (by rw [hS0, Function.update_of_ne hd1, hS]; rfl)
  set S1 := Function.update S0 t1 (L.map Sym.bit ++ S0 t1) with hS1
  have e2 : Eval ρ (pushC d .mark) ⟨some .mark, S1⟩
      ⟨some .mark, Function.update S1 d (.mark :: S1 d)⟩ 1 :=
    Eval.push ρ d (fun _ => .mark) (some .mark) S1
  set S2 := Function.update S1 d (.mark :: S1 d) with hS2
  have hS2t1 : S2 t1 = L.map Sym.bit ++ (Sym.mark :: S t1) := by
    rw [hS2, Function.update_of_ne (Ne.symm hd1), hS1, Function.update_self, hS0,
      Function.update_self]
  have e3 := copyBlock_eval (Ne.symm hd1) h12 hd2 ρ (some .mark) L (Sym.mark :: S t1) S2
    (TermOK.cons (by rfl) _) hS2t1
  set S3 := Function.update S2 d (L.map Sym.bit ++ S2 d) with hS3
  have hS3t1 : S3 t1 = L.map Sym.bit ++ (Sym.mark :: S t1) := by
    rw [hS3, Function.update_of_ne (Ne.symm hd1), hS2t1]
  have e4 := WP.W0m.dropNat_eval ρ (some .mark) L (Sym.mark :: S t1) S3 (TermOK.cons (by rfl) _)
    hS3t1
  set S4 := Function.update S3 t1 (Sym.mark :: S t1) with hS4
  have e5 : Eval ρ (popR t1) ⟨some .mark, S4⟩ ⟨some .mark, Function.update S4 t1 (S t1)⟩ 1 := by
    refine (Eval.pop ρ t1 (fun _ o => o) (some .mark) S4).of_eq ?_ rfl
    rw [hS4, Function.update_self]
    rfl
  set S5 := Function.update S4 t1 (S t1) with hS5
  have hS1d : S1 d = natSyms (k + 1) ++ tl := by
    rw [hS1, Function.update_of_ne hd1, hS0, Function.update_of_ne hd1, hS]
  have hS5d : S5 d = (encodeNat (k + 1)).map Sym.bit ++ (Sym.mark :: (natSyms (k + 1) ++ tl)) := by
    rw [hS5, Function.update_of_ne hd1, hS4, Function.update_of_ne hd1, hS3, Function.update_self,
      hS2, Function.update_self, hS1d]
  have e6 := dec_eval hd2 ρ (some .mark) k (Sym.mark :: (natSyms (k + 1) ++ tl)) S5
    (TermOK.cons (by rfl) _) hS5d
  refine ⟨_, ?_, (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq e5 e6)))))).of_eq ?_ rfl⟩
  · have hz : zerosLead (encodeNat (k + 1)) ≤ L.length := by
      rw [hL]
      exact zerosLead_le_length _
    have hb' : L.length = bitLen (k + 1) := rfl
    omega
  · congr 1
    funext j
    simp only [hS5, hS4, hS3, hS2, hS1, hS0, Function.update_apply]
    by_cases hj1 : j = t1
    · subst hj1
      simp [Ne.symm hd1]
    · by_cases hjd : j = d
      · subst hjd
        simp [natSyms]
      · simp [hj1, hjd]

/-- **popDesc**, exact. -/
theorem popDesc_eval {d : K} (ρ : List (SProg K)) (v : Option Sym) (k : ℕ) (tl : List Sym)
    (S : K → List Sym) (hS : S d = natSyms k ++ Sym.mark :: tl) :
    Eval ρ (popDesc d) ⟨v, S⟩ ⟨some .mark, Function.update S d tl⟩ (2 * bitLen k + 5) := by
  have e1 := WP.W0m.dropNat_eval ρ v (encodeNat k) (Sym.mark :: tl) S (TermOK.cons (by rfl) _) hS
  have e2 : Eval ρ (popR d) ⟨(Sym.mark :: tl).head?, Function.update S d (Sym.mark :: tl)⟩
      ⟨some .mark, Function.update S d tl⟩ 1 := by
    refine (Eval.pop ρ d (fun _ o => o) _ _).of_eq ?_ rfl
    rw [Function.update_self, Function.update_idem]
    rfl
  exact (Eval.seq e1 e2).of_eq rfl rfl

theorem runs_pushPred {d t1 t2 : K} (hd1 : d ≠ t1) (hd2 : d ≠ t2) (h12 : t1 ≠ t2) (k : ℕ)
    (tl : List Sym) (S : K → List Sym) (htl : TermOK tl) (hS : S d = natSyms (k + 1) ++ tl) :
    Runs (pushPred d t1 t2) S
      (Function.update S d (natSyms k ++ Sym.mark :: (natSyms (k + 1) ++ tl))) (fun _ => True)
      (22 * bitLen (k + 1) + 29) :=
  Runs.of_eval fun v => by
    obtain ⟨t, ht, e⟩ := pushPred_eval hd1 hd2 h12 [] v k tl S htl hS
    exact ⟨_, t, e, trivial, ht⟩

theorem runs_popDesc {d : K} (k : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = natSyms k ++ Sym.mark :: tl) :
    Runs (popDesc d) S (Function.update S d tl) (fun _ => True) (2 * bitLen k + 5) :=
  Runs.of_eval fun v => ⟨_, _, popDesc_eval [] v k tl S hS, trivial, le_rfl⟩

end Eval

/-! ## The depth-first recursion pattern -/

section DFS

variable {K σ : Type} [DecidableEq K]

/-- The body of a descriptor-driven recursive procedure: test the counter on top of `d` (through
the symbol-register lens `l`); run `leaf` at `0` and `internal` otherwise. -/
def descBody (l : Lens σ (Option Sym)) (d : K) (leaf internal : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((zeroTest d).liftRegs l) (.ite (fun v => optIsBit (l.get v)) internal leaf)

theorem runs_zeroTest (d : K) (n : ℕ) (tl : List Sym) (S : K → List Sym) (htl : TermOK tl)
    (hS : S d = natSyms n ++ tl) :
    Runs (zeroTest d) S S (fun r => optIsBit r = !decide (n = 0)) 1 :=
  Runs.of_eval fun v => by
    obtain ⟨r, hr, e⟩ := zeroTest_eval [] v n tl S htl hS
    exact ⟨r, 1, e, hr, le_rfl⟩

/-- **The depth-first recursion pattern** (descriptor counter on `d`). Spec instances `x` carry a
descriptor `desc x` on top of `d` (above a number terminator). If the leaf meets the spec at
descriptor `0`, and the internal branch meets it at descriptors `> 0` assuming that `recur 0` meets
the spec at every instance with a smaller descriptor, then the procedure `fix (descBody …)` meets
the whole family, with cost `T x + 4` (`zeroTest`, branch test, call and return). -/
theorem runs_descRec (l : Lens σ (Option Sym)) (d : K) {leaf internal : Prog K (fun _ => Sym) σ}
    {X : Type} (desc : X → ℕ) {S S' : X → K → List Sym} {T : X → ℕ}
    (hd : ∀ x, ∃ tl, TermOK tl ∧ S x d = natSyms (desc x) ++ tl)
    (hleaf : ∀ x, desc x = 0 →
      RunsIn [descBody l d leaf internal] leaf (S x) (S' x) (fun _ => True) (T x))
    (hint : ∀ x, desc x ≠ 0 →
      (∀ y, desc y < desc x →
        RunsIn [descBody l d leaf internal] (.recur 0) (S y) (S' y) (fun _ => True) (T y + 4)) →
      RunsIn [descBody l d leaf internal] internal (S x) (S' x) (fun _ => True) (T x)) :
    ∀ x, Runs (.fix (descBody l d leaf internal)) (S x) (S' x) (fun _ => True) (T x + 4) := by
  have key := runs_fix (b := descBody l d leaf internal) (Q := fun _ _ => True)
    (T := fun x => T x + 2) desc (S := S) (S' := S') (fun x ih => ?_)
  · exact key
  · obtain ⟨tl, htl, hSd⟩ := hd x
    have hz := RunsIn.of_runs_liftRegs l (runs_zeroTest d (desc x) tl (S x) htl hSd)
      (by simp [Prog.Closed, zeroTest, peekR, Prog.FreeBelow]) [descBody l d leaf internal]
    by_cases h0 : desc x = 0
    · have hz' : RunsIn [descBody l d leaf internal] ((zeroTest d).liftRegs l) (S x) (S x)
          (fun v => optIsBit (l.get v) = false) 1 :=
        RunsIn.mono hz (fun v hv => by rw [hv, h0]; rfl) le_rfl
      exact RunsIn.mono (RunsIn.ite_false hz' (hleaf x h0)) (fun _ _ => trivial) (by omega)
    · have hz' : RunsIn [descBody l d leaf internal] ((zeroTest d).liftRegs l) (S x) (S x)
          (fun v => optIsBit (l.get v) = true) 1 :=
        RunsIn.mono hz (fun v hv => by rw [hv, decide_eq_false h0]; rfl) le_rfl
      exact RunsIn.mono (RunsIn.ite_true hz' (hint x h0 ih)) (fun _ _ => trivial) (by omega)

end DFS

#assert_std_axioms closed_pushPred closed_popDesc pushPred_eval popDesc_eval runs_pushPred
  runs_popDesc runs_zeroTest runs_descRec

end SubNLogN.Machine.Calculus
