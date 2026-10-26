/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge
import IntMulTM.Framework.Lib.Counter

/-!
# K5-PP base (`Bridge/PrePostBase.lean`): `Runs` wrappers and header traversal

Support for the K5 parts `PreScaleStmt`, `PostStmt`, `InitCtrStmt`
(`SubNLogN/Machine/Contracts/Bridge.lean`, §7). Programs here are `TMFw.Lib` macros (register
`Option Sym`) over an arbitrary stack type `K`.

**Scope (honest summary).** Proved `Runs` facts with exact final stacks and explicit costs
(no `sorry`):
* wrappers of `TMFw.Lib` macros: `runs_moveSym`, `runs_moveBlock`, `runs_copyBlock`,
  `runs_reverseBlock`, `runs_pushC`, `runs_rewindTo`, `runs_decIfPos` (decrement unless zero);
* header traversal: `skipFields src dst n` moves the first `n` fields of a header
  `hdrSyms fs ++ L` (`Contracts/W9/Common.lean:121`: each field is `natSyms a ++ [mark]`) from
  `src` onto `dst`, reversed (`runs_skipFields`); `rewindTo dst src g` moves them back.

## Plan of the K5-PP parts (shared by `InitCtr.lean`, `PrePost*.lean`)
* **Header.** `BrPar.hdr = [p, P, ω, wI, wT, wOut, pIn, wIn, d] ++ List.ofFn t` on `par`. A field
  is reached by pushing a guard `sep2` on a clean scratch stack, skipping the preceding fields onto
  it (`skipFields`), copying the field (`copyBlock`), and rewinding to the guard (`rewindTo`):
  `par` is restored exactly; cost `O(|hdrSyms hdr|)`, paid by `BrPar.setup`.
* **Costs.** Every header-only step costs `≤ c·(|hdrSyms hdr| + 1) ≤ c·setup`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

section Wrappers

variable {K : Type} [DecidableEq K]

/-- Move the top symbol of `src` onto `dst` through the register. -/
def moveSym (src dst : K) : SProg K := .seq (popR src) (pushR dst)

omit [DecidableEq K] in
theorem closed_moveSym (src dst : K) : (moveSym src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveSym, popR, pushR]

theorem runs_moveSym {src dst : K} (hne : src ≠ dst) (x : Sym) (L : List Sym) (S : K → List Sym)
    (hS : S src = x :: L) :
    Runs (moveSym src dst) S (Function.update (Function.update S src L) dst (x :: S dst))
      (fun _ => True) 2 := by
  refine Runs.of_eval fun v => ⟨some x, 2, ?_, trivial, le_refl _⟩
  have e1 : Eval [] (popR src) ⟨v, S⟩ ⟨some x, Function.update S src L⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have e2 : Eval [] (pushR dst) ⟨some x, Function.update S src L⟩
      ⟨some x, Function.update (Function.update S src L) dst (x :: S dst)⟩ 1 := by
    have h := Eval.push (Γ := fun _ => Sym) [] dst (fun r : Option Sym => r.getD Sym.sep) (some x)
      (Function.update S src L)
    refine h.of_eq ?_ rfl
    rw [Function.update_of_ne (Ne.symm hne)]
    rfl
  exact Eval.seq e1 e2

theorem runs_moveBlock {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBlock src dst) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  Runs.of_eval fun v => ⟨_, _, moveBlock_eval hne [] v es rest S hrest hS, trivial, le_refl _⟩

theorem runs_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (blk : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = blk.map Sym.bit ++ rest) :
    Runs (copyBlock src dst tmp) S (Function.update S dst (blk.map Sym.bit ++ S dst))
      (fun _ => True) (7 * blk.length + 7) :=
  Runs.of_eval fun v =>
    ⟨_, _, copyBlock_eval hsd hst hdt [] v blk rest S hrest hS, trivial, le_refl _⟩

theorem runs_reverseBlock {k t1 t2 : K} (h1 : k ≠ t1) (h2 : k ≠ t2) (h12 : t1 ≠ t2)
    (blk : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = blk.map Sym.bit ++ rest) :
    Runs (reverseBlock k t1 t2) S (Function.update S k (blk.reverse.map Sym.bit ++ rest))
      (fun _ => True) (9 * blk.length + 10) :=
  Runs.of_eval fun v =>
    ⟨_, _, reverseBlock_eval h1 h2 h12 [] v blk rest S hrest hS, trivial, le_refl _⟩

theorem runs_pushC (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push (Γ := fun _ => Sym) [] k (fun _ : Option Sym => x) v S,
    trivial, le_refl _⟩

theorem runs_rewindTo {src dst : K} (hne : src ≠ dst) (g : Sym) (L rest : List Sym)
    (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Runs (WP.W9comp.rewindTo src dst g) S
      (Function.update (Function.update S src rest) dst (L.reverse ++ S dst)) (fun _ => True)
      (3 * L.length + 2) :=
  Runs.of_eval fun v =>
    ⟨_, _, WP.W9comp.rewindTo_eval hne g v L rest S hg hS, trivial, le_refl _⟩

/-- Decrement the counter on `k` unless it is zero (`n ↦ n - 1`). -/
def decIfPos (k t : K) : SProg K := .seq (zeroTest k) (.ite optIsBit (dec k t) skip)

omit [DecidableEq K] in
theorem closed_decIfPos (k t : K) : (decIfPos k t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, decIfPos, zeroTest, dec, decFix, scanLoop, scanBody, peekR,
    popR, pushC, skip, moveBits, moveBitsBody, pushR]

theorem runs_decIfPos {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (decIfPos k t) S (Function.update S k (natSyms (n - 1) ++ rest)) (fun _ => True)
      (8 * bitLen n + 10) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨r, hr, e1⟩ := zeroTest_eval (k := k) [] v n rest S hrest hS
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hS' : Function.update S k (natSyms (0 - 1) ++ rest) = S := by
      rw [Nat.zero_sub, ← hS, Function.update_eq_self]
    rw [hS']
    exact ⟨r, 1 + (1 + 1), Eval.seq e1 (Eval.ite_false (by simpa using hr) (skip_eval [] _)),
      trivial, by omega⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e2 := dec_eval hkt [] r m rest S hrest hS
    refine ⟨some .mark, _, Eval.seq e1 (Eval.ite_true (by simpa using hr) e2), trivial, ?_⟩
    have hz : zerosLead (encodeNat (m + 1)) ≤ bitLen (m + 1) := by
      unfold bitLen
      exact zerosLead_le_length _
    omega

end Wrappers

/-! ## Header traversal -/

section Header

variable {K : Type} [DecidableEq K]

theorem hdrSyms_cons (a : ℕ) (fs : List ℕ) :
    hdrSyms (a :: fs) = natSyms a ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem length_hdrSyms_cons (a : ℕ) (fs : List ℕ) :
    (hdrSyms (a :: fs)).length = bitLen a + 1 + (hdrSyms fs).length := by
  rw [hdrSyms_cons]
  simp [length_natSyms]
  omega

theorem mark_not_mem_natSyms (a : ℕ) : Sym.mark ∉ natSyms a := by
  simp [natSyms]

theorem sep2_not_mem_hdrSyms (fs : List ℕ) : Sym.sep2 ∉ hdrSyms fs := by
  simp [hdrSyms, natSyms]

theorem termOK_mark_cons (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons (by rfl) L

/-- Skip one header field `natSyms a ++ [mark]`: its bits (reversed), then the mark. -/
def skipField (src dst : K) : SProg K := .seq (moveBlock src dst) (moveSym src dst)

/-- Skip `n` header fields. -/
def skipFields (src dst : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (skipField src dst) (skipFields src dst n)

omit [DecidableEq K] in
theorem closed_skipFields (src dst : K) : ∀ n, (skipFields src dst n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, skipFields, skip]
  | n + 1 => by
    have h := closed_skipFields src dst n
    simp only [Prog.Closed] at h ⊢
    refine ⟨?_, h⟩
    simp [Prog.FreeBelow, skipField, moveSym, moveBlock, moveBits, moveBitsBody, restoreR, popR,
      pushR, skip]

theorem runs_skipField {src dst : K} (hne : src ≠ dst) (a : ℕ) (L : List Sym) (S : K → List Sym)
    (hS : S src = natSyms a ++ Sym.mark :: L) :
    Runs (skipField src dst) S
      (Function.update (Function.update S src L) dst
        ((natSyms a ++ [Sym.mark]).reverse ++ S dst)) (fun _ => True) (3 * bitLen a + 6) := by
  have h1 := runs_moveBlock hne (encodeNat a) (Sym.mark :: L) S (termOK_mark_cons L) hS
  have h2 := runs_moveSym hne Sym.mark L (Function.update (Function.update S src (Sym.mark :: L))
    dst ((encodeNat a).reverse.map Sym.bit ++ S dst))
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) (by unfold bitLen; omega)
  funext k
  simp only [Function.update_apply]
  split_ifs with h3 h4 <;> simp_all [natSyms, List.map_reverse]

theorem runs_skipFields {src dst : K} (hne : src ≠ dst) :
    ∀ (fs : List ℕ) (L : List Sym) (S : K → List Sym), S src = hdrSyms fs ++ L →
      Runs (skipFields src dst fs.length) S
        (Function.update (Function.update S src L) dst ((hdrSyms fs).reverse ++ S dst))
        (fun _ => True) (6 * (hdrSyms fs).length + 1)
  | [], L, S, hS => by
    refine Runs.of_eval fun v => ⟨v, 1, (skip_eval [] _).of_eq ?_ rfl, trivial, le_refl _⟩
    simp only [hdrSyms, List.flatMap_nil, List.nil_append] at hS
    simp only [hdrSyms, List.flatMap_nil, List.reverse_nil, List.nil_append]
    rw [← hS, Function.update_eq_self, Function.update_eq_self]
  | a :: fs, L, S, hS => by
    rw [hdrSyms_cons, List.append_assoc, List.cons_append] at hS
    have h1 := runs_skipField hne a (hdrSyms fs ++ L) S hS
    have h2 := runs_skipFields hne fs L (Function.update (Function.update S src (hdrSyms fs ++ L))
      dst ((natSyms a ++ [Sym.mark]).reverse ++ S dst))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ _ => trivial) ?_
    · funext k
      simp only [Function.update_apply]
      split_ifs with h3 h4 <;> simp_all [hdrSyms_cons]
    · rw [length_hdrSyms_cons]
      omega

end Header

end SubNLogN.Machine.BridgePP
