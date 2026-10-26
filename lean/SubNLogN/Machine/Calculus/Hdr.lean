/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Desc
import SubNLogN.Machine.Calculus.Guard
import SubNLogN.Machine.Calculus.Rules
import Contracts.W9.Common

/-!
# Framed procedure calculus (`Calculus/Hdr.lean`): multi-field descriptors

Headers `W9.hdrSyms fs` (each field `natSyms f` followed by a `mark`) and the C-core descriptor
blocks `descSyms kind fs = [kind] ++ hdrSyms (fields) ++ [Sym.tag 13]`
for multi-field call descriptors. All programs are
closed `SProg K` programs (one `Option Sym` register); every rule below is an exact `Runs` fact
(final stacks exactly determined, explicit cost), usable in any environment through
`RunsIn.of_runs` / `RunsIn.of_runs_liftRegs` with the `closed_*` lemmas.

* `dropField d` (the program `popDesc` of `Desc.lean`) and `dropHdr d n`: drop the top field /
  the top `n` fields; cost `Σ_{f ∈ fs} (2·bitLen f + 5) + 1` (`runs_dropHdr`).
* `moveFieldTo d t` / `moveFieldBack t d`: move one field to a temporary (bits reversed below a
  `mark`, `fieldRev f`) and back; cost `3·bitLen f + 6` each.
* `copyHdr n src dst t`: copy the top `n`-field header of `src` onto `dst` in the same order;
  `src` and `t` restored; cost `Σ_{f ∈ fs} (13·bitLen f + 20) + 2` (`runs_copyHdr`).
* `updField i d t ker`: apply a number kernel `ker` (any closed `SProg` with an exact `Runs` spec
  `natSyms a ++ rest ↦ natSyms b ++ rest` on `d`) to field `i` in place; cost
  `2·Σ_{f ∈ fs.take i} (3·bitLen f + 6) + T_ker + 2` (`runs_updField`).
* `saveDesc descSep cur desc` / `restoreDesc descSep desc cur` (the `parkG`/`unparkG` of
  `Guard.lean` with stop symbol `Sym.tag 13`) and `eraseDesc cur n`: save the current descriptor
  above a `descSep` (leaving its end tag on `cur`), restore it, and erase a returned child
  descriptor down to its end tag (`runs_saveDesc`, `runs_restoreDesc`, `runs_eraseDesc`).
* `runs_descRecField`: the depth-first recursion pattern of `Desc.lean` with the leaf test
  reading field `j` of the header on top of `d`.
-/

namespace SubNLogN.Machine.Calculus

open Computability TMFw TMFw.Contracts TMFw.Lib

/-! ## Headers, descriptors and field blocks -/

/-- A descriptor block with any number of fields: kind symbol, header, end tag `Sym.tag 13`. -/
def descSymsL (kind : Sym) (fs : List ℕ) : List Sym := kind :: W9.hdrSyms fs ++ [Sym.tag 13]

/-- Fixed 24-field natural-number call descriptor format. -/
def descSyms (kind : Sym) (fs : Fin 24 → ℕ) : List Sym :=
  [kind] ++ W9.hdrSyms ((List.finRange 24).map fs) ++ [Sym.tag 13]

theorem descSyms_eq (kind : Sym) (fs : Fin 24 → ℕ) :
    descSyms kind fs = descSymsL kind ((List.finRange 24).map fs) := rfl

/-- A field moved to a temporary: a `mark` above the reversed bits. -/
def fieldRev (f : ℕ) : List Sym := Sym.mark :: (encodeNat f).reverse.map Sym.bit

/-- The content left on the temporary after moving the fields `gs` (in order): the last moved
field on top. -/
def movedFields (gs : List ℕ) : List Sym := gs.reverse.flatMap fieldRev

namespace HdrAux

theorem hdrSyms_nil : W9.hdrSyms [] = [] := rfl

theorem hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    W9.hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: W9.hdrSyms fs := by
  simp [W9.hdrSyms]

theorem hdrSyms_append (fs gs : List ℕ) :
    W9.hdrSyms (fs ++ gs) = W9.hdrSyms fs ++ W9.hdrSyms gs := by
  simp [W9.hdrSyms]

theorem length_hdrSyms (fs : List ℕ) :
    (W9.hdrSyms fs).length = (fs.map fun f => bitLen f + 1).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [hdrSyms_cons, List.length_append, List.length_cons, ih, List.map_cons, List.sum_cons]
    simp [natSyms, bitLen]
    omega

/-- Header symbols are bits and `mark`s. -/
theorem freeOf_hdrSyms {g : Sym} (hg : g.isBit = false) (hgm : g ≠ Sym.mark) (fs : List ℕ) :
    FreeOf g (W9.hdrSyms fs) := by
  intro x hx hxg
  subst hxg
  simp only [W9.hdrSyms, List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
  obtain ⟨f, -, hx | hx⟩ := hx
  · simp only [natSyms, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    simp [Sym.isBit] at hg
  · exact hgm hx

theorem movedFields_cons (f : ℕ) (gs : List ℕ) :
    movedFields (f :: gs) = movedFields gs ++ fieldRev f := by
  simp [movedFields]

theorem termOK_flatMap_fieldRev (hs : List ℕ) (T0 : List Sym) (h : TermOK T0) :
    TermOK (hs.flatMap fieldRev ++ T0) := by
  cases hs with
  | nil => simpa using h
  | cons h hs => exact TermOK.cons rfl _

theorem forEachProg_map_const {K : Type} {Γ : K → Type} {σ α β : Type} (g : α → β)
    (P : Prog K Γ σ) : ∀ l : List α, forEachProg (l.map g) (fun _ => P) = forEachProg l (fun _ => P)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, forEachProg_cons, forEachProg_cons, forEachProg_map_const g P l]

theorem forEachRange_succ_const {K : Type} {Γ : K → Type} {σ : Type} (n : ℕ) (P : Prog K Γ σ) :
    forEachRange (n + 1) (fun _ => P) = .seq P (forEachRange n (fun _ => P)) := by
  unfold forEachRange
  rw [List.range_succ_eq_map, forEachProg_cons, forEachProg_map_const]

variable {K : Type} [DecidableEq K]

theorem runs_forEachRange_zero {σ : Type} (f : ℕ → Prog K (fun _ => Sym) σ) (S : K → List Sym) :
    Runs (forEachRange 0 f) S S (fun _ => True) 1 := by
  have h := runs_forEachRange 0 f (fun _ => 0) (fun _ => S) (fun i hi => absurd hi (by omega))
  simpa using h

theorem runs_moveBlock {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBlock src dst) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  Runs.of_eval fun v => ⟨_, _, moveBlock_eval hne [] v es rest S hrest hS, trivial, le_rfl⟩

theorem runs_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (blk : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = blk.map Sym.bit ++ rest) :
    Runs (copyBlock src dst tmp) S (Function.update S dst (blk.map Sym.bit ++ S dst))
      (fun _ => True) (7 * blk.length + 7) :=
  Runs.of_eval fun v => ⟨_, _, copyBlock_eval hsd hst hdt [] v blk rest S hrest hS, trivial, le_rfl⟩

end HdrAux

/-! ## Programs -/

section Programs

variable {K : Type}

/-- Drop the top field `natSyms f ++ [mark]` of a header (this is `popDesc` of `Desc.lean`). -/
def dropField (d : K) : SProg K := popDesc d

/-- Drop the top `n` fields of a header. -/
def dropHdr (d : K) (n : ℕ) : SProg K := forEachRange n (fun _ => dropField d)

/-- Move the top field of `d` to `t`: its bits land reversed on `t`, below a `mark`. -/
def moveFieldTo (d t : K) : SProg K := .seq (moveBlock d t) (.seq (popR d) (pushC t .mark))

/-- Move a field back from `t` to `d` (inverse of `moveFieldTo`). -/
def moveFieldBack (t d : K) : SProg K := .seq (popR t) (.seq (pushC d .mark) (moveBlock t d))

/-- Move a field back from `t` to `src`, then copy it onto `dst` (same order, with its `mark`). -/
def moveFieldBackCopy (t src dst : K) : SProg K :=
  .seq (moveFieldBack t src) (.seq (pushC dst .mark) (copyBlock src dst t))

/-- **Copy a header**: copy the top `n`-field header of `src` onto `dst` (same field order); `src`
and the temporary `t` are restored. -/
def copyHdr (n : ℕ) (src dst t : K) : SProg K :=
  .seq (forEachRange n (fun _ => moveFieldTo src t))
    (forEachRange n (fun _ => moveFieldBackCopy t src dst))

/-- **Update a field**: run the number kernel `ker` (acting on the top number of `d`) on field `i`
of the header on `d`, moving the fields above it to the temporary `t` and back. -/
def updField (i : ℕ) (d t : K) (ker : SProg K) : SProg K :=
  .seq (forEachRange i (fun _ => moveFieldTo d t))
    (.seq ker (forEachRange i (fun _ => moveFieldBack t d)))

/-- **Save the current descriptor**: push `descSep` on `desc` and move
the descriptor body above `cur`'s end tag `Sym.tag 13` onto it (reversed); the end tag stays on
`cur`. -/
def saveDesc (descSep : Sym) (cur desc : K) : SProg K := parkG (Sym.tag 13) descSep cur desc

/-- **Restore the saved descriptor**: move it back above the end tag on `cur` and
drop its `descSep`. -/
def restoreDesc (descSep : Sym) (desc cur : K) : SProg K := unparkG descSep desc cur

/-- **Erase a returned child descriptor**: pop its kind symbol and its `n` fields;
its end tag stays on `cur`. -/
def eraseDesc (cur : K) (n : ℕ) : SProg K := .seq (popR cur) (dropHdr cur n)

theorem closed_dropField (d : K) : (dropField d).Closed := closed_popDesc d

theorem closed_dropHdr (d : K) (n : ℕ) : (dropHdr d n).Closed :=
  closed_forEachRange n _ (fun _ _ => closed_dropField d)

theorem closed_moveFieldTo (d t : K) : (moveFieldTo d t).Closed := by
  simp [Prog.Closed, moveFieldTo, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR,
    popR, pushR, pushC, Lib.skip]

theorem closed_moveFieldBack (t d : K) : (moveFieldBack t d).Closed := by
  simp [Prog.Closed, moveFieldBack, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR,
    popR, pushR, pushC, Lib.skip]

theorem closed_moveFieldBackCopy (t src dst : K) : (moveFieldBackCopy t src dst).Closed := by
  simp [Prog.Closed, moveFieldBackCopy, moveFieldBack, Prog.FreeBelow, moveBlock, moveBits,
    moveBitsBody, restoreR, popR, pushR, pushC, Lib.skip, copyBlock, moveBitsDup, dupBody]

theorem closed_copyHdr (n : ℕ) (src dst t : K) : (copyHdr n src dst t).Closed :=
  ⟨closed_forEachRange n _ (fun _ _ => closed_moveFieldTo src t),
    closed_forEachRange n _ (fun _ _ => closed_moveFieldBackCopy t src dst)⟩

theorem closed_updField (i : ℕ) (d t : K) {ker : SProg K} (hk : ker.Closed) :
    (updField i d t ker).Closed :=
  ⟨closed_forEachRange i _ (fun _ _ => closed_moveFieldTo d t), hk,
    closed_forEachRange i _ (fun _ _ => closed_moveFieldBack t d)⟩

theorem closed_saveDesc (descSep : Sym) (cur desc : K) : (saveDesc descSep cur desc).Closed :=
  closed_parkG _ _ cur desc

theorem closed_restoreDesc (descSep : Sym) (desc cur : K) :
    (restoreDesc descSep desc cur).Closed :=
  closed_unparkG _ desc cur

theorem closed_eraseDesc (cur : K) (n : ℕ) : (eraseDesc cur n).Closed :=
  ⟨by simp [Prog.FreeBelow, popR], closed_dropHdr cur n⟩

end Programs

/-! ## Exact rules -/

section Rules

variable {K : Type} [DecidableEq K]

/-- **`dropField`**, exact (this is `runs_popDesc`). -/
theorem runs_dropField (d : K) (f : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = natSyms f ++ Sym.mark :: tl) :
    Runs (dropField d) S (Function.update S d tl) (fun _ => True) (2 * bitLen f + 5) :=
  runs_popDesc f tl S hS

/-- **`dropHdr`**, exact: the header `hdrSyms fs` on top of `d` is removed;
cost `Σ_{f ∈ fs} (2·bitLen f + 5) + 1`. -/
theorem runs_dropHdr (d : K) :
    ∀ (fs : List ℕ) (tl : List Sym) (S : K → List Sym), S d = W9.hdrSyms fs ++ tl →
      Runs (dropHdr d fs.length) S (Function.update S d tl) (fun _ => True)
        ((fs.map fun f => 2 * bitLen f + 5).sum + 1)
  | [], tl, S, hS => by
    have h0 := HdrAux.runs_forEachRange_zero (fun _ => dropField d) S
    have hd : S d = tl := by simpa [HdrAux.hdrSyms_nil] using hS
    have hS' : Function.update S d tl = S := by
      rw [← hd, Function.update_eq_self]
    rw [hS']
    simpa [dropHdr] using h0
  | f :: fs, tl, S, hS => by
    have h1 := runs_dropField d f (W9.hdrSyms fs ++ tl) S
      (by rw [hS, HdrAux.hdrSyms_cons, List.append_assoc]; rfl)
    have h2 := runs_dropHdr d fs tl (Function.update S d (W9.hdrSyms fs ++ tl))
      (Function.update_self _ _ _)
    rw [Function.update_idem] at h2
    have h := RunsIn.seq (RunsIn.iff_runs.mpr h1) (RunsIn.iff_runs.mpr h2)
    rw [dropHdr, List.length_cons, HdrAux.forEachRange_succ_const]
    exact RunsIn.iff_runs.mp (RunsIn.mono h (fun _ _ => trivial)
      (by simp only [List.map_cons, List.sum_cons]; omega))

/-- **`moveFieldTo`**, exact: the top field `natSyms f ++ [mark]` of `d` goes to `t` as
`fieldRev f`; cost `3·bitLen f + 6`. -/
theorem runs_moveFieldTo {d t : K} (hdt : d ≠ t) (f : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = natSyms f ++ Sym.mark :: tl) :
    Runs (moveFieldTo d t) S (Function.update (Function.update S d tl) t (fieldRev f ++ S t))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := HdrAux.runs_moveBlock hdt (encodeNat f) (Sym.mark :: tl) S (TermOK.cons rfl tl) hS
  have h2 := runs_popR d (Function.update (Function.update S d (Sym.mark :: tl)) t
    ((encodeNat f).reverse.map Sym.bit ++ S t)) Sym.mark tl
    (by rw [Function.update_of_ne hdt, Function.update_self])
  have h3 := runs_pushC t Sym.mark (Function.update (Function.update (Function.update S d
    (Sym.mark :: tl)) t ((encodeNat f).reverse.map Sym.bit ++ S t)) d tl)
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))) ?_ ?_)
  · funext k
    simp only [fieldRev, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

/-- **`moveFieldBack`**, exact: `t = fieldRev f ++ tt` (`tt` a number terminator) gives the field
`natSyms f ++ [mark]` back on top of `d`; cost `3·bitLen f + 6`. -/
theorem runs_moveFieldBack {t d : K} (htd : t ≠ d) (f : ℕ) (tt : List Sym) (S : K → List Sym)
    (htt : TermOK tt) (hS : S t = fieldRev f ++ tt) :
    Runs (moveFieldBack t d) S
      (Function.update (Function.update S t tt) d (natSyms f ++ Sym.mark :: S d))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := runs_popR t S Sym.mark ((encodeNat f).reverse.map Sym.bit ++ tt)
    (by rw [hS]; rfl)
  have h2 := runs_pushC d Sym.mark
    (Function.update S t ((encodeNat f).reverse.map Sym.bit ++ tt))
  have h3 := HdrAux.runs_moveBlock htd (encodeNat f).reverse tt
    (Function.update (Function.update S t ((encodeNat f).reverse.map Sym.bit ++ tt)) d
      (Sym.mark :: Function.update S t ((encodeNat f).reverse.map Sym.bit ++ tt) d)) htt
    (by rw [Function.update_of_ne htd, Function.update_self])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))) ?_ ?_)
  · funext k
    simp only [natSyms, List.reverse_reverse, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [bitLen, List.length_reverse]
    omega

/-- **`moveFieldBackCopy`**, exact: as `moveFieldBack t src`, and the field is also copied onto
`dst`; cost `10·bitLen f + 14`. -/
theorem runs_moveFieldBackCopy {t src dst : K} (hts : t ≠ src) (htd : t ≠ dst) (hsd : src ≠ dst)
    (f : ℕ) (tt : List Sym) (S : K → List Sym) (htt : TermOK tt) (hS : S t = fieldRev f ++ tt) :
    Runs (moveFieldBackCopy t src dst) S
      (Function.update (Function.update (Function.update S t tt) src
        (natSyms f ++ Sym.mark :: S src)) dst (natSyms f ++ Sym.mark :: S dst))
      (fun _ => True) (10 * bitLen f + 14) := by
  have h1 := runs_moveFieldBack hts f tt S htt hS
  have h2 := runs_pushC dst Sym.mark (Function.update (Function.update S t tt) src
    (natSyms f ++ Sym.mark :: S src))
  have h3 := HdrAux.runs_copyBlock hsd (Ne.symm hts) (Ne.symm htd) (encodeNat f)
    (Sym.mark :: S src)
    (Function.update (Function.update (Function.update S t tt) src
      (natSyms f ++ Sym.mark :: S src)) dst (Sym.mark :: Function.update (Function.update S t tt)
        src (natSyms f ++ Sym.mark :: S src) dst)) (TermOK.cons rfl _)
    (by rw [Function.update_of_ne hsd, Function.update_self]; rfl)
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))) ?_ ?_)
  · funext k
    simp only [natSyms, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

/-- Moving the fields `gs` (in order) from the top of `d` to `t`; cost
`Σ_{f ∈ gs} (3·bitLen f + 6) + 1`. -/
theorem runs_moveFieldsTo {d t : K} (hdt : d ≠ t) :
    ∀ (gs : List ℕ) (X : List Sym) (S : K → List Sym), S d = W9.hdrSyms gs ++ X →
      Runs (forEachRange gs.length (fun _ => moveFieldTo d t)) S
        (Function.update (Function.update S d X) t (movedFields gs ++ S t)) (fun _ => True)
        ((gs.map fun f => 3 * bitLen f + 6).sum + 1)
  | [], X, S, hS => by
    have h0 := HdrAux.runs_forEachRange_zero (fun _ => moveFieldTo d t) S
    have hd : S d = X := by simpa [HdrAux.hdrSyms_nil] using hS
    have hS' : Function.update (Function.update S d X) t (movedFields [] ++ S t) = S := by
      rw [← hd, Function.update_eq_self]
      simp [movedFields]
    rw [hS']
    simpa using h0
  | f :: gs, X, S, hS => by
    have h1 := runs_moveFieldTo hdt f (W9.hdrSyms gs ++ X) S
      (by rw [hS, HdrAux.hdrSyms_cons, List.append_assoc]; rfl)
    have h2 := runs_moveFieldsTo hdt gs X
      (Function.update (Function.update S d (W9.hdrSyms gs ++ X)) t (fieldRev f ++ S t))
      (by rw [Function.update_of_ne hdt, Function.update_self])
    have h := RunsIn.seq (RunsIn.iff_runs.mpr h1) (RunsIn.iff_runs.mpr h2)
    rw [List.length_cons, HdrAux.forEachRange_succ_const]
    refine RunsIn.iff_runs.mp (RunsIn.congr h ?_
      (by simp only [List.map_cons, List.sum_cons]; omega))
    funext k
    simp only [HdrAux.movedFields_cons, List.append_assoc, Function.update_apply]
    split_ifs <;> simp_all

/-- Moving fields back from `t` (stack content `hs.flatMap fieldRev ++ T0`, first element of `hs`
on top) to `d`; cost `Σ_{f ∈ hs} (3·bitLen f + 6) + 1`. -/
theorem runs_moveFieldsBack {t d : K} (htd : t ≠ d) :
    ∀ (hs : List ℕ) (T0 : List Sym) (S : K → List Sym), TermOK T0 →
      S t = hs.flatMap fieldRev ++ T0 →
      Runs (forEachRange hs.length (fun _ => moveFieldBack t d)) S
        (Function.update (Function.update S t T0) d (W9.hdrSyms hs.reverse ++ S d))
        (fun _ => True) ((hs.map fun f => 3 * bitLen f + 6).sum + 1)
  | [], T0, S, _, hS => by
    have h0 := HdrAux.runs_forEachRange_zero (fun _ => moveFieldBack t d) S
    have hS' : Function.update (Function.update S t T0) d
        (W9.hdrSyms ([] : List ℕ).reverse ++ S d) = S := by
      have : S t = T0 := by simpa using hS
      rw [← this, Function.update_eq_self]
      simp [HdrAux.hdrSyms_nil]
    rw [hS']
    simpa using h0
  | h :: hs, T0, S, hT0, hS => by
    have htt := HdrAux.termOK_flatMap_fieldRev hs T0 hT0
    have h1 := runs_moveFieldBack htd h (hs.flatMap fieldRev ++ T0) S htt
      (by rw [hS, List.flatMap_cons, List.append_assoc])
    have h2 := runs_moveFieldsBack htd hs T0
      (Function.update (Function.update S t (hs.flatMap fieldRev ++ T0)) d
        (natSyms h ++ Sym.mark :: S d)) hT0
      (by rw [Function.update_of_ne htd, Function.update_self])
    have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1) (RunsIn.iff_runs.mpr h2)
    rw [List.length_cons, HdrAux.forEachRange_succ_const]
    refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_
      (by simp only [List.map_cons, List.sum_cons]; omega))
    funext k
    simp only [List.reverse_cons, HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons,
      HdrAux.hdrSyms_nil, List.append_assoc, List.singleton_append,
      Function.update_apply]
    split_ifs <;> simp_all

/-- Moving fields back from `t` to `src` and copying them onto `dst`; cost
`Σ_{f ∈ hs} (10·bitLen f + 14) + 1`. -/
theorem runs_moveFieldsBackCopy {t src dst : K} (hts : t ≠ src) (htd : t ≠ dst)
    (hsd : src ≠ dst) :
    ∀ (hs : List ℕ) (T0 : List Sym) (S : K → List Sym), TermOK T0 →
      S t = hs.flatMap fieldRev ++ T0 →
      Runs (forEachRange hs.length (fun _ => moveFieldBackCopy t src dst)) S
        (Function.update (Function.update (Function.update S t T0) src
          (W9.hdrSyms hs.reverse ++ S src)) dst (W9.hdrSyms hs.reverse ++ S dst))
        (fun _ => True) ((hs.map fun f => 10 * bitLen f + 14).sum + 1)
  | [], T0, S, _, hS => by
    have h0 := HdrAux.runs_forEachRange_zero (fun _ => moveFieldBackCopy t src dst) S
    have hS' : Function.update (Function.update (Function.update S t T0) src
        (W9.hdrSyms ([] : List ℕ).reverse ++ S src)) dst
        (W9.hdrSyms ([] : List ℕ).reverse ++ S dst) = S := by
      have : S t = T0 := by simpa using hS
      rw [← this, Function.update_eq_self]
      simp [HdrAux.hdrSyms_nil]
    rw [hS']
    simpa using h0
  | h :: hs, T0, S, hT0, hS => by
    have htt := HdrAux.termOK_flatMap_fieldRev hs T0 hT0
    have h1 := runs_moveFieldBackCopy hts htd hsd h (hs.flatMap fieldRev ++ T0) S htt
      (by rw [hS, List.flatMap_cons, List.append_assoc])
    have h2 := runs_moveFieldsBackCopy hts htd hsd hs T0
      (Function.update (Function.update (Function.update S t (hs.flatMap fieldRev ++ T0)) src
        (natSyms h ++ Sym.mark :: S src)) dst (natSyms h ++ Sym.mark :: S dst)) hT0
      (by rw [Function.update_of_ne htd, Function.update_of_ne hts, Function.update_self])
    have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1) (RunsIn.iff_runs.mpr h2)
    rw [List.length_cons, HdrAux.forEachRange_succ_const]
    refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_
      (by simp only [List.map_cons, List.sum_cons]; omega))
    funext k
    simp only [List.reverse_cons, HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons,
      HdrAux.hdrSyms_nil, List.append_assoc, List.singleton_append,
      Function.update_apply]
    split_ifs <;> simp_all

/-- **`copyHdr`**, exact: the header `hdrSyms fs` on top of `src` is copied onto `dst` in the same
field order; `src` and the temporary `t` (holding a number terminator `S t`) are restored. Cost
`Σ_{f ∈ fs} (13·bitLen f + 20) + 2`. -/
theorem runs_copyHdr {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (fs : List ℕ) (tl : List Sym) (S : K → List Sym) (hS : S src = W9.hdrSyms fs ++ tl)
    (ht : TermOK (S t)) :
    Runs (copyHdr fs.length src dst t) S (Function.update S dst (W9.hdrSyms fs ++ S dst))
      (fun _ => True) ((fs.map fun f => 13 * bitLen f + 20).sum + 2) := by
  have h1 := runs_moveFieldsTo hst fs tl S hS
  have h2 := runs_moveFieldsBackCopy (Ne.symm hst) (Ne.symm hdt) hsd fs.reverse (S t)
    (Function.update (Function.update S src tl) t (movedFields fs ++ S t)) ht
    (by rw [Function.update_self]; rfl)
  rw [List.length_reverse] at h2
  have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1) (RunsIn.iff_runs.mpr h2)
  refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_ ?_)
  · funext k
    simp only [List.reverse_reverse, Function.update_apply]
    split_ifs <;> simp_all
  · have e : ((fs.map fun f => 13 * bitLen f + 20).sum) =
        (fs.map fun f => 3 * bitLen f + 6).sum + (fs.map fun f => 10 * bitLen f + 14).sum := by
      rw [← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro f _
      omega
    rw [List.map_reverse, List.sum_reverse, e]
    omega

/-- **`updField`**, exact. Let `ker` be a kernel acting on the top number of `d` with exact spec
`natSyms (fs[i]) ++ tl' ↦ natSyms g ++ tl'` (every other stack restored) within `Tk`. Then
`updField i d t ker` replaces field `i` of the header `hdrSyms fs` on `d` by `g`; the temporary
`t` (holding a number terminator) is restored. Cost `2·Σ_{f ∈ fs.take i} (3·bitLen f + 6) + Tk + 2`. -/
theorem runs_updField {d t : K} (hdt : d ≠ t) (ker : SProg K) {i : ℕ} {fs : List ℕ}
    (hi : i < fs.length) (g Tk : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = W9.hdrSyms fs ++ tl) (ht : TermOK (S t))
    (hker : ∀ (tl' : List Sym) (S' : K → List Sym), TermOK tl' →
      S' d = natSyms fs[i] ++ tl' →
      Runs ker S' (Function.update S' d (natSyms g ++ tl')) (fun _ => True) Tk) :
    Runs (updField i d t ker) S (Function.update S d (W9.hdrSyms (fs.set i g) ++ tl))
      (fun _ => True) (2 * ((fs.take i).map fun f => 3 * bitLen f + 6).sum + Tk + 2) := by
  have hlen : (fs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : fs = fs.take i ++ fs[i] :: fs.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i fs, List.drop_eq_getElem_cons hi]
  have hS1 : S d = W9.hdrSyms (fs.take i) ++
      (natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl)) := by
    rw [hS]
    conv_lhs => rw [hsplit]
    rw [HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
    simp only [List.append_assoc, List.cons_append]
  have h1 := runs_moveFieldsTo hdt (fs.take i) _ S hS1
  rw [hlen] at h1
  have h2 := hker (Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))
    (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t))
    (TermOK.cons rfl _) (by rw [Function.update_of_ne hdt, Function.update_self])
  have h3 := runs_moveFieldsBack (Ne.symm hdt) (fs.take i).reverse (S t)
    (Function.update (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t)) d
      (natSyms g ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) ht
    (by rw [Function.update_of_ne (Ne.symm hdt), Function.update_self]; rfl)
  rw [List.length_reverse, hlen] at h3
  have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))
  have hset : fs.set i g = fs.take i ++ g :: fs.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hi]
  refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_ ?_)
  · funext k
    rw [List.reverse_reverse]
    by_cases hkd : k = d
    · rw [hkd, Function.update_self, Function.update_self, Function.update_self, hset,
        HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
      simp only [List.append_assoc, List.cons_append]
    · rw [Function.update_of_ne hkd, Function.update_of_ne hkd]
      by_cases hkt : k = t
      · rw [hkt, Function.update_self]
      · rw [Function.update_of_ne hkt, Function.update_of_ne hkd, Function.update_of_ne hkt,
          Function.update_of_ne hkd]
  · rw [List.map_reverse, List.sum_reverse]
    omega

/-- **`saveDesc`**, exact: the descriptor `descSymsL kind fs` on top of
`cur` is moved, reversed and without its end tag, onto `desc` above `descSep`; its end tag
`Sym.tag 13` stays on `cur`. Cost `3·|hdrSyms fs| + 8`. -/
theorem runs_saveDesc {descSep : Sym} {cur desc : K} (hcd : cur ≠ desc) (kind : Sym)
    (hkind : kind ≠ Sym.tag 13) (fs : List ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S cur = descSymsL kind fs ++ rest) :
    Runs (saveDesc descSep cur desc) S
      (Function.update (Function.update S cur (Sym.tag 13 :: rest)) desc
        ((kind :: W9.hdrSyms fs).reverse ++ descSep :: S desc))
      (fun _ => True) (3 * (W9.hdrSyms fs).length + 8) := by
  have hfree : FreeOf (Sym.tag 13) (kind :: W9.hdrSyms fs) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hkind
    · exact HdrAux.freeOf_hdrSyms rfl (by decide) fs x hx
  have h := runs_parkG (psep := descSep) hcd (kind :: W9.hdrSyms fs) (Sym.tag 13 :: rest) S hfree
    (StopTail.cons _ _) (by rw [hS]; simp [descSymsL])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) rfl ?_)
  simp only [List.length_cons]
  omega

/-- **`restoreDesc`**, exact: a descriptor saved by `saveDesc` (top of `desc`, above
`descSep`) is moved back onto `cur` above its end tag (`cur = Sym.tag 13 :: rest`), restoring
`descSymsL kind fs ++ rest`; the `descSep` is dropped. Cost `3·|hdrSyms fs| + 5`. -/
theorem runs_restoreDesc {descSep : Sym} {desc cur : K} (hdc : desc ≠ cur) (kind : Sym)
    (hkind : kind ≠ descSep) (hsep : descSep.isBit = false) (hsepm : descSep ≠ Sym.mark)
    (fs : List ℕ) (pt rest : List Sym) (S : K → List Sym)
    (hdesc : S desc = (kind :: W9.hdrSyms fs).reverse ++ descSep :: pt)
    (hcur : S cur = Sym.tag 13 :: rest) :
    Runs (restoreDesc descSep desc cur) S
      (Function.update (Function.update S desc pt) cur (descSymsL kind fs ++ rest))
      (fun _ => True) (3 * (W9.hdrSyms fs).length + 5) := by
  have hfree : FreeOf descSep (kind :: W9.hdrSyms fs) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hkind
    · exact HdrAux.freeOf_hdrSyms hsep hsepm fs x hx
  have h := runs_unparkG hdc (kind :: W9.hdrSyms fs) pt S hfree hdesc
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ ?_)
  · rw [hcur]
    simp [descSymsL]
  · simp only [List.length_cons]
    omega

/-- **`eraseDesc`**, exact: the descriptor `descSymsL kind fs` on top of `cur` is
erased down to its end tag, which stays. Cost `Σ_{f ∈ fs} (2·bitLen f + 5) + 2`. -/
theorem runs_eraseDesc (cur : K) (kind : Sym) (fs : List ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S cur = descSymsL kind fs ++ rest) :
    Runs (eraseDesc cur fs.length) S (Function.update S cur (Sym.tag 13 :: rest))
      (fun _ => True) ((fs.map fun f => 2 * bitLen f + 5).sum + 2) := by
  have h1 := runs_popR cur S kind (W9.hdrSyms fs ++ Sym.tag 13 :: rest)
    (by rw [hS]; simp [descSymsL])
  have h2 := runs_dropHdr cur fs (Sym.tag 13 :: rest)
    (Function.update S cur (W9.hdrSyms fs ++ Sym.tag 13 :: rest)) (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  refine RunsIn.iff_runs.mp (RunsIn.mono (RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.iff_runs.mpr h2)) (fun _ _ => trivial) (by omega))

end Rules

/-! ## The depth-first recursion pattern on a header field -/

section DFSField

variable {K σ : Type} [DecidableEq K]

/-- The body of a recursive procedure whose leaf test reads field `j` of the header on top of
`d`: move fields `0, …, j-1` to the temporary `t`, test field `j` for zero, move the fields back,
then run `internal` (field `j ≠ 0`) or `leaf` (field `j = 0`). -/
def descBodyField (l : Lens σ (Option Sym)) (d t : K) (j : ℕ)
    (leaf internal : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (.seq ((forEachRange j (fun _ => moveFieldTo d t)).liftRegs l) ((zeroTest d).liftRegs l))
    (.ite (fun v => optIsBit (l.get v))
      (.seq ((forEachRange j (fun _ => moveFieldBack t d)).liftRegs l) internal)
      (.seq ((forEachRange j (fun _ => moveFieldBack t d)).liftRegs l) leaf))

/-- The overhead of the field test of `descBodyField` on the header `fs`: moving `fs.take j` out
and back, the zero test and the branch. -/
def fieldTestCost (j : ℕ) (fs : List ℕ) : ℕ :=
  2 * ((fs.take j).map fun f => 3 * bitLen f + 6).sum + 4

/-- **The depth-first recursion pattern on a header field.** Spec instances `x` carry a header
`hdrSyms (fs x)` on top of `d` (with `j < |fs x|`) and a number terminator on the temporary `t`.
If the leaf meets the spec when field `j` is `0`, and the internal branch meets it when field `j`
is nonzero, assuming that `recur 0` meets the spec at every instance with a smaller field `j`,
then `fix (descBodyField …)` meets the whole family, with cost
`T x + fieldTestCost j (fs x) + 2`. -/
theorem runs_descRecField (l : Lens σ (Option Sym)) {d t : K} (hdt : d ≠ t) (j : ℕ)
    {leaf internal : Prog K (fun _ => Sym) σ} {X : Type} (fs : X → List ℕ) (tl : X → List Sym)
    {S S' : X → K → List Sym} {T : X → ℕ} (hj : ∀ x, j < (fs x).length)
    (hd : ∀ x, S x d = W9.hdrSyms (fs x) ++ tl x) (ht : ∀ x, TermOK (S x t))
    (hleaf : ∀ x, (fs x)[j]'(hj x) = 0 →
      RunsIn [descBodyField l d t j leaf internal] leaf (S x) (S' x) (fun _ => True) (T x))
    (hint : ∀ x, (fs x)[j]'(hj x) ≠ 0 →
      (∀ y, (fs y)[j]'(hj y) < (fs x)[j]'(hj x) →
        RunsIn [descBodyField l d t j leaf internal] (.recur 0) (S y) (S' y) (fun _ => True)
          (T y + fieldTestCost j (fs y) + 2)) →
      RunsIn [descBodyField l d t j leaf internal] internal (S x) (S' x) (fun _ => True) (T x)) :
    ∀ x, Runs (.fix (descBodyField l d t j leaf internal)) (S x) (S' x) (fun _ => True)
      (T x + fieldTestCost j (fs x) + 2) := by
  have key := runs_fix (b := descBodyField l d t j leaf internal) (Q := fun _ _ => True)
    (T := fun x => T x + fieldTestCost j (fs x)) (fun x => (fs x)[j]'(hj x)) (S := S) (S' := S')
    (fun x ih => ?_)
  · exact key
  · set ρ := [descBodyField l d t j leaf internal] with hρ
    have hjx := hj x
    have hlen : ((fs x).take j).length = j := List.length_take_of_le hjx.le
    set Xd := natSyms (fs x)[j] ++ Sym.mark :: (W9.hdrSyms ((fs x).drop (j + 1)) ++ tl x)
      with hXd
    have hsplit : W9.hdrSyms (fs x) ++ tl x = W9.hdrSyms ((fs x).take j) ++ Xd := by
      have e : fs x = (fs x).take j ++ (fs x)[j] :: (fs x).drop (j + 1) := by
        conv_lhs => rw [← List.take_append_drop j (fs x), List.drop_eq_getElem_cons hjx]
      conv_lhs => rw [e]
      rw [hXd, HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
      simp only [List.append_assoc, List.cons_append]
    have h1 := runs_moveFieldsTo hdt ((fs x).take j) Xd (S x) (by rw [hd x, hsplit])
    rw [hlen] at h1
    set S1 := Function.update (Function.update (S x) d Xd) t (movedFields ((fs x).take j) ++ S x t)
      with hS1
    have hS1d : S1 d = Xd := by
      rw [hS1, Function.update_of_ne hdt, Function.update_self]
    have hz := runs_zeroTest d (fs x)[j] (Sym.mark :: (W9.hdrSyms ((fs x).drop (j + 1)) ++ tl x))
      S1 (TermOK.cons rfl _) (by rw [hS1d, hXd])
    have h3 := runs_moveFieldsBack (Ne.symm hdt) ((fs x).take j).reverse (S x t) S1 (ht x)
      (by rw [hS1, Function.update_self]; rfl)
    rw [List.length_reverse, hlen] at h3
    have h3' : Function.update (Function.update S1 t (S x t)) d
        (W9.hdrSyms ((fs x).take j).reverse.reverse ++ S1 d) = S x := by
      funext k
      rw [List.reverse_reverse, hS1d]
      by_cases hkd : k = d
      · rw [hkd, Function.update_self, hd x, hsplit]
      · rw [Function.update_of_ne hkd]
        by_cases hkt : k = t
        · rw [hkt, Function.update_self]
        · rw [Function.update_of_ne hkt, hS1, Function.update_of_ne hkt,
            Function.update_of_ne hkd]
    rw [h3'] at h3
    have hout := RunsIn.of_runs_liftRegs l h1 (closed_forEachRange j _
      (fun _ _ => closed_moveFieldTo d t)) ρ
    have hzt := RunsIn.of_runs_liftRegs l hz
      (by simp [Prog.Closed, zeroTest, peekR, Prog.FreeBelow]) ρ
    have hback := RunsIn.of_runs_liftRegs l h3 (closed_forEachRange j _
      (fun _ _ => closed_moveFieldBack t d)) ρ
    have hP := RunsIn.seq hout hzt
    have hcost : ((((fs x).take j).reverse.map fun f => 3 * bitLen f + 6).sum) =
        (((fs x).take j).map fun f => 3 * bitLen f + 6).sum := by
      rw [List.map_reverse, List.sum_reverse]
    by_cases h0 : (fs x)[j]'(hj x) = 0
    · have hP' : RunsIn ρ (.seq ((forEachRange j (fun _ => moveFieldTo d t)).liftRegs l)
          ((zeroTest d).liftRegs l)) (S x) S1 (fun v => optIsBit (l.get v) = false) _ :=
        RunsIn.mono hP (fun v hv => by rw [hv, h0]; rfl) le_rfl
      refine RunsIn.mono (RunsIn.ite_false hP' (RunsIn.seq hback (hleaf x h0)))
        (fun _ _ => trivial) ?_
      simp only [fieldTestCost]
      omega
    · have hP' : RunsIn ρ (.seq ((forEachRange j (fun _ => moveFieldTo d t)).liftRegs l)
          ((zeroTest d).liftRegs l)) (S x) S1 (fun v => optIsBit (l.get v) = true) _ :=
        RunsIn.mono hP (fun v hv => by rw [hv, decide_eq_false h0]; rfl) le_rfl
      refine RunsIn.mono (RunsIn.ite_true hP' (RunsIn.seq hback (hint x h0 ih)))
        (fun _ _ => trivial) ?_
      simp only [fieldTestCost]
      omega

end DFSField

#assert_std_axioms descSyms_eq closed_dropField closed_dropHdr closed_moveFieldTo
  closed_moveFieldBack closed_moveFieldBackCopy closed_copyHdr closed_updField closed_saveDesc
  closed_restoreDesc closed_eraseDesc runs_dropField runs_dropHdr runs_moveFieldTo
  runs_moveFieldBack runs_moveFieldBackCopy runs_moveFieldsTo runs_moveFieldsBack
  runs_moveFieldsBackCopy runs_copyHdr runs_updField runs_saveDesc runs_restoreDesc
  runs_eraseDesc runs_descRecField

end SubNLogN.Machine.Calculus
