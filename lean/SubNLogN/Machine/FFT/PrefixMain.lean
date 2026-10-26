/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixLayout
import SubNLogN.Machine.FFT.PrefixKit2

/-!
# K4-PREFIX, the driver program (`Machine/FFT/PrefixMain.lean`)

The prefix-round kernel (`PrefixRoundStmt`, `Contracts/FFT.lean:239`; Theorem 6.5, `thm:direct-fft`,
Section 6.4):
1. the parameter phase (`PrefixParamStmt`): `H = mark^{2^L}`; `G = mark^{2^D-1}` for `v < b₀`, empty
   for `v = ℓ - 1`; the widths `natSyms (w + D)` on `WB1` and `natSyms w` on `WS`;
2. `ONE = natSyms 1`, and a copy `WB2` of `natSyms (w + D)`;
3. widening `w → W = w + D` (`TruncShiftStmt` with `s = 0`) from the data stack onto `E1`;
4. for `v = ℓ - 1` (`G` empty): count the `2^{n}` blocks of `2^L` records, then `G := 2^n - 1`;
5. the pass loop, while `G` is nonempty: `G := ⌊G/2⌋`, count the pass on `NP`, one exact
   butterfly pass (`PrefixPassStmt`) with half-blocks `H`, then `H := 2H`;
6. `n` truncations by `2` at width `W` (`TruncShiftStmt`, `s = 1`), counted by `NP`;
7. narrowing `W → w` (`s = 0`) from `E1` back onto the data stack;
8. emptying the kernel stacks.

This file contains the state notation (`st`) and the program (`mainProg`).
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF SubNLogN.Math.Walsh

section State

variable {Er Ep Et : Type} [DecidableEq Er] [DecidableEq Ep] [DecidableEq Et]

/-- A state: the named stacks and the sub-kernel scratch from `S`, the kernel stacks from `f`. -/
def st (S : KP Er Ep Et → List Sym) (f : PS → List Sym) : KP Er Ep Et → List Sym
  | .inr (.inl d) => f d
  | x => S x

@[simp] theorem st_ps (S : KP Er Ep Et → List Sym) (f : PS → List Sym) (d : PS) :
    st S f (ps d) = f d := rfl

@[simp] theorem st_inl (S : KP Er Ep Et → List Sym) (f : PS → List Sym) (i : Fin 4) :
    st S f (.inl i) = S (.inl i) := rfl

@[simp] theorem st_inrr (S : KP Er Ep Et → List Sym) (f : PS → List Sym)
    (e : Er ⊕ (Ep ⊕ Et)) : st S f (.inr (.inr e)) = S (.inr (.inr e)) := rfl

theorem st_nD (S : KP Er Ep Et → List Sym) (f : PS → List Sym) : st S f nD = S nD := rfl
theorem st_nH (S : KP Er Ep Et → List Sym) (f : PS → List Sym) : st S f nH = S nH := rfl
theorem st_nV (S : KP Er Ep Et → List Sym) (f : PS → List Sym) : st S f nV = S nV := rfl

theorem st_upd_ps (S : KP Er Ep Et → List Sym) (f : PS → List Sym) (d : PS) (v : List Sym) :
    Function.update (st S f) (ps d) v = st S (Function.update f d v) := by
  funext x
  rcases x with i | (d' | e)
  · simp [st, ps, Function.update_apply]
  · by_cases h : d' = d
    · subst h; simp [st, ps]
    · simp [st, ps, Function.update_apply, h]
  · simp [st, ps, Function.update_apply]

theorem st_upd_inl (S : KP Er Ep Et → List Sym) (f : PS → List Sym) (i : Fin 4) (v : List Sym) :
    Function.update (st S f) (.inl i) v = st (Function.update S (.inl i) v) f := by
  funext x
  rcases x with i' | (d' | e)
  · by_cases h : i' = i
    · subst h; simp [st]
    · simp [st, Function.update_apply, h]
  · simp [st, Function.update_apply]
  · simp [st, Function.update_apply]

theorem st_upd_nD (S : KP Er Ep Et → List Sym) (f : PS → List Sym) (v : List Sym) :
    Function.update (st S f) nD v = st (Function.update S nD v) f := st_upd_inl S f 0 v

theorem st_of_clean (S : KP Er Ep Et → List Sym) (hS : ∀ d, S (ps d) = []) :
    st S (fun _ => []) = S := by
  funext x
  rcases x with i | (d | e)
  · rfl
  · exact (hS d).symm
  · rfl

end State

/-! ## The program -/

section Prog

variable {Er Ep Et σ Rr Rp Rt : Type} [DecidableEq Er] [DecidableEq Ep] [DecidableEq Et]
  (lO : Lens σ (Option Sym)) (lr : Lens σ Rr) (lp : Lens σ Rp) (lt : Lens σ Rt)
  (Pr : Prog (KLoc (Fin 6) Er) (fun _ => Sym) Rr) (Pp : Prog (KLoc (Fin 3) Ep) (fun _ => Sym) Rp)
  (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)

/-- Case `v = ℓ - 1`: count the blocks of `|H|` records (on `G`), restore the array on `E1`, and
remove one mark from `G`. -/
def countA : Prog (KP Er Ep Et) (fun _ => Sym) σ :=
  .seq (countBlk lO (ps .E1) (ps .T) (ps .G) (ps .H) (ps .HA))
    (.seq (movePrefix lO (ps .T) (ps .E1) isRecO) (popO lO (ps .G)))

/-- One iteration of the pass loop. -/
def passBody : Prog (KP Er Ep Et) (fun _ => Sym) σ :=
  .seq (halveTo lO (ps .G) (ps .GA)) (.seq (movePrefix lO (ps .GA) (ps .G) Option.isSome)
    (.seq (pushK (ps .NP) .mark) (.seq (callInj ιp lp Pp)
    (.seq (dbl1 lO (ps .H) (ps .AUX)) (popO lO (ps .H))))))

/-- One iteration of the truncation loop. -/
def truncBody : Prog (KP Er Ep Et) (fun _ => Sym) σ :=
  .seq (popO lO (ps .NP)) (.seq (callInj ιt1 lt Pt)
    (.seq (movePrefix lO (ps .E2) (ps .E3) isRecO) (movePrefix lO (ps .E3) (ps .E1) isRecO)))

/-- **The prefix-round kernel.** -/
def mainProg : Prog (KP Er Ep Et) (fun _ => Sym) σ :=
  .seq (callInj ιr lr Pr)
  (.seq (pushK (ps .ONE) (.bit true))
  (.seq (copyBits lO (ps .WB1) (ps .WB2) (ps .TMP))
  (.seq (callInj ιtW lt Pt)
  (.seq (.seq (peekO lO (ps .G)) (.ite (fun v => (lO.get v).isSome) skipP (countA lO)))
  (.seq (ploop lO (ps .G) Option.isSome (passBody lO lp Pp))
  (.seq (ploop lO (ps .NP) Option.isSome (truncBody lO lt Pt))
  (.seq (callInj ιtF lt Pt)
  (.seq (drain lO (ps .H)) (.seq (drain lO (ps .WB1)) (.seq (drain lO (ps .WB2))
  (.seq (drain lO (ps .WS)) (drain lO (ps .ONE)))))))))))))

theorem closed_mainProg (hPr : Pr.Closed) (hPp : Pp.Closed) (hPt : Pt.Closed) :
    (mainProg lO lr lp lt Pr Pp Pt).Closed := by
  refine ⟨closed_callInj _ _ hPr, closed_pushK _ _, closed_copyBits lO _ _ _,
    closed_callInj _ _ hPt, ⟨closed_peekO lO _, closed_skipP,
      closed_countBlk lO _ _ _ _ _, closed_movePrefix lO _ _ _, closed_popO lO _⟩,
    closed_ploop lO _ _ ⟨closed_halveTo lO _ _, closed_movePrefix lO _ _ _, closed_pushK _ _,
      closed_callInj _ _ hPp, closed_dbl1 lO _ _, closed_popO lO _⟩,
    closed_ploop lO _ _ ⟨closed_popO lO _, closed_callInj _ _ hPt, closed_movePrefix lO _ _ _,
      closed_movePrefix lO _ _ _⟩,
    closed_callInj _ _ hPt, closed_drain lO _, closed_drain lO _, closed_drain lO _,
    closed_drain lO _, closed_drain lO _⟩

end Prog

end SubNLogN.Machine.FFT.PrefixAux
