/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvArith
import SubNLogN.Machine.Layer.DrvParamsDefs

/-!
# Layer driver, parameter kernels: field access (`Machine/Layer/DrvParamsKit.lean`)

**Scope (honest summary).** Generic routines with exact `Runs` specifications, all proved (no
`sorry`), in the namespace `SubNLogN.Machine.Layer.DrvParamsAux`:
* `parkFieldsN src pk n`: move the first `n` fields of a header (`hdrSyms`, `Contracts/W9/Common.lean:121`)
  from `src` to `pk` (reversed);
* `xferSep src dst`: move every symbol of `src` above a `sep` floor onto `dst` (reversed), consuming
  the floor;
* `copyFieldN i src dst pk tmp`: push a copy of field `i` of the header on `src` onto `dst`; `src`,
  `pk` (a `sep` floor delimits the parked fields) and `tmp` are restored.
-/

namespace SubNLogN.Machine.Layer.DrvParamsAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine.NatArith
  SubNLogN.Machine.Layer.DrvArith

/-- Loop test of `xferSep`: the register is not the `sep` floor. -/
def notSepR (r : Option Sym) : Bool := decide (r ≠ some Sym.sep)

section Defs

variable {K : Type}

/-- Move the first `n` fields of `src` onto `pk` (each: bits reversed, then its `mark`). -/
def parkFieldsN (src pk : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (SubNLogN.Machine.WalshCubeAux.parkField src pk) (parkFieldsN src pk n)

/-- Move every symbol of `src` above its `sep` floor onto `dst` (reversed); the floor is popped. -/
def xferSep (src dst : K) : SProg K :=
  .seq (popR src) (.loop notSepR (SubNLogN.Machine.WalshCubeAux.xferBody src dst))

/-- **Copy field `i`** of the header on `src` onto `dst`. -/
def copyFieldN (i : ℕ) (src dst pk tmp : K) : Prog K (fun _ => Sym) Reg :=
  .seq (pushW pk Sym.sep) (.seq ((parkFieldsN src pk i).liftRegs lW)
    (.seq (copyN src dst tmp) ((xferSep pk src).liftRegs lW)))

theorem closed_parkFieldsN (src pk : K) : ∀ n, (parkFieldsN src pk n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, parkFieldsN, skip]
  | n + 1 => WP.W9comp.closed_seq (SubNLogN.Machine.WalshCubeAux.closed_parkField src pk)
      (closed_parkFieldsN src pk n)

theorem closed_xferSep (src dst : K) : (xferSep src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, xferSep, SubNLogN.Machine.WalshCubeAux.xferBody, pushR, popR]

theorem closed_copyFieldN (i : ℕ) (src dst pk tmp : K) : (copyFieldN i src dst pk tmp).Closed :=
  WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq
    (WP.W9comp.closed_liftRegs lW (closed_parkFieldsN _ _ _)) (WP.W9comp.closed_seq
      (closed_copyN _ _ _) (WP.W9comp.closed_liftRegs lW (closed_xferSep _ _))))

end Defs

theorem sep_not_mem_hdrSyms : ∀ fs : List ℕ, Sym.sep ∉ hdrSyms fs
  | [] => by simp [hdrSyms]
  | n :: fs => by
    have ih := sep_not_mem_hdrSyms fs
    simp only [hdrSyms, List.flatMap_cons, List.mem_append, List.mem_singleton, not_or] at ih ⊢
    refine ⟨⟨?_, by decide⟩, ih⟩
    simp [natSyms]

theorem hdrSyms_append (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms, List.flatMap_append]

theorem hdrSyms_cons_append' (n : ℕ) (fs : List ℕ) (L : List Sym) :
    hdrSyms (n :: fs) ++ L = natSyms n ++ Sym.mark :: (hdrSyms fs ++ L) := by
  simp [hdrSyms]

section Specs

variable {K : Type} [DecidableEq K]

theorem runs_parkFieldsN {src pk : K} (hne : src ≠ pk) :
    ∀ (fs gs : List ℕ) (rest : List Sym) (S : K → List Sym),
      S src = hdrSyms (fs ++ gs) ++ rest →
      Runs (parkFieldsN src pk fs.length) S
        (Function.update (Function.update S src (hdrSyms gs ++ rest)) pk
          ((hdrSyms fs).reverse ++ S pk)) (fun _ => True) (3 * (hdrSyms fs).length + 1)
  | [], gs, rest, S, hS => by
    have hS' : S src = hdrSyms gs ++ rest := by simpa using hS
    refine Runs.of_eval fun v => ⟨v, 1, (skip_eval [] _).of_eq ?_ rfl, trivial, by simp [hdrSyms]⟩
    rw [← hS', Function.update_eq_self]
    simp [hdrSyms]
  | f :: fs, gs, rest, S, hS => by
    have hS1 : S src = natSyms f ++ Sym.mark :: (hdrSyms (fs ++ gs) ++ rest) := by
      rw [hS, List.cons_append, hdrSyms_cons_append']
    have r1 := SubNLogN.Machine.WalshCubeAux.runs_parkField hne f _ S hS1
    have r2 := runs_parkFieldsN hne fs gs rest
      (Function.update (Function.update S src (hdrSyms (fs ++ gs) ++ rest)) pk
        (Sym.mark :: ((natSyms f).reverse ++ S pk)))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 r2) ?_)
      (fun _ _ => trivial) ?_
    · rw [upd2_upd2 hne, Function.update_self]
      simp [hdrSyms]
    · simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
        List.length_singleton]
      omega

theorem xferSep_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L J : List Sym) (S : K → List Sym), Sym.sep ∉ L → S src = (L ++ Sym.sep :: J).tail →
      Eval [] (.loop notSepR (SubNLogN.Machine.WalshCubeAux.xferBody src dst))
        ⟨(L ++ Sym.sep :: J).head?, S⟩
        ⟨some Sym.sep, Function.update (Function.update S src J) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], J, S, _, hS => by
    refine (Eval.loop_false (by simp [notSepR])).of_eq ?_ rfl
    have hS' : S src = J := hS
    show (⟨some Sym.sep, S⟩ : SSt K) = _
    rw [← hS', Function.update_eq_self]
    simp
  | x :: L, J, S, hx, hS => by
    have hxs : x ≠ Sym.sep := fun h => hx (h ▸ List.mem_cons_self)
    have hL : Sym.sep ∉ L := fun h => hx (List.mem_cons_of_mem _ h)
    have hS' : S src = L ++ Sym.sep :: J := hS
    have e1 : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      (Eval.push ([] : List (SProg K)) dst (fun r : Option Sym => r.getD Sym.sep) (some x)
        S).of_eq rfl rfl
    have e2 : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ Sym.sep :: J).head?, Function.update (Function.update S dst (x :: S dst)) src
          (L ++ Sym.sep :: J).tail⟩ 1 := by
      refine (Eval.pop ([] : List (SProg K)) src (fun (_ : Option Sym) (o : Option Sym) => o) _
        _).of_eq ?_ rfl
      rw [Function.update_of_ne hne, hS']
    have ih := xferSep_loop_eval hne L J (Function.update (Function.update S dst (x :: S dst)) src
      (L ++ Sym.sep :: J).tail) hL (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notSepR, hxs]) (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem runs_xferSep {src dst : K} (hne : src ≠ dst) (L J : List Sym) (S : K → List Sym)
    (hL : Sym.sep ∉ L) (hS : S src = L ++ Sym.sep :: J) :
    Runs (xferSep src dst) S (Function.update (Function.update S src J) dst (L.reverse ++ S dst))
      (fun _ => True) (3 * L.length + 2) := by
  apply Runs.of_eval
  intro v
  have e1 : Eval [] (popR src) ⟨v, S⟩ ⟨(L ++ Sym.sep :: J).head?,
      Function.update S src (L ++ Sym.sep :: J).tail⟩ 1 := by
    refine (Eval.pop ([] : List (SProg K)) src (fun (_ : Option Sym) (o : Option Sym) => o) v
      S).of_eq ?_ rfl
    rw [hS]
  have e2 := xferSep_loop_eval hne L J (Function.update S src (L ++ Sym.sep :: J).tail) hL
    (Function.update_self _ _ _)
  refine ⟨some Sym.sep, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by omega⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Specs

section CopyField

variable {K : Type} [DecidableEq K]

/-- The cost bound of `copyFieldN` (linear in the header length). -/
def copyFieldCost (fs : List ℕ) : ℕ := 13 * (hdrSyms fs).length + 12

theorem bitLen_hdr_mem {fs : List ℕ} {n : ℕ} (h : n ∈ fs) :
    bitLen n + 1 ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => simp at h
  | cons m fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_singleton] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := ih h'
      omega

theorem length_hdrSyms_take_le (fs : List ℕ) (i : ℕ) :
    (hdrSyms (fs.take i)).length ≤ (hdrSyms fs).length := by
  conv_rhs => rw [← List.take_append_drop i fs]
  rw [hdrSyms_append, List.length_append]
  omega

/-- **`copyFieldN`**: pushes a copy of field `i` of the header on `src` onto `dst`; `src`, `pk`,
`tmp` restored. -/
theorem runs_copyFieldN {src dst pk tmp : K} (h : [src, dst, pk, tmp].Nodup) (fs : List ℕ)
    (i : ℕ) (hi : i < fs.length) (rest : List Sym) (S : K → List Sym)
    (hS : S src = hdrSyms fs ++ rest) :
    Runs (copyFieldN i src dst pk tmp) S (Function.update S dst (natSyms fs[i] ++ S dst))
      (fun _ => True) (copyFieldCost fs) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨hsd, hsp, hst⟩, ⟨hdp, hdt⟩, hpt⟩ := h'
  have hsplit : fs.take i ++ fs.drop i = fs := List.take_append_drop i fs
  have hlen : (fs.take i).length = i := List.length_take_of_le hi.le
  have hdrop : fs.drop i = fs[i] :: fs.drop (i + 1) := List.drop_eq_getElem_cons hi
  obtain ⟨S1, hS1⟩ : ∃ T, T = Function.update S pk (Sym.sep :: S pk) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = Function.update (Function.update S1 src
      (hdrSyms (fs.drop i) ++ rest)) pk ((hdrSyms (fs.take i)).reverse ++ Sym.sep :: S pk) :=
    ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = Function.update S2 dst (natSyms fs[i] ++ S dst) := ⟨_, rfl⟩
  have r1 : Runs (pushW pk Sym.sep) S S1 (fun _ => True) 1 := by
    rw [hS1]; exact runs_pushW pk Sym.sep S
  have r2 : Runs ((parkFieldsN src pk i).liftRegs lW) S1 S2 (fun _ => True)
      (3 * (hdrSyms (fs.take i)).length + 1) := by
    have c := runs_liftRegs' lW (runs_parkFieldsN hsp (fs.take i) (fs.drop i) rest S1
      (by rw [hS1, Function.update_of_ne hsp, hS, hsplit]))
    rw [hlen] at c
    have e : S1 pk = Sym.sep :: S pk := by rw [hS1, Function.update_self]
    rw [e] at c
    rw [hS2]
    exact c
  have r3 : Runs (copyN src dst tmp) S2 S3 (fun _ => True) (7 * bitLen fs[i] + 7) := by
    have c := runs_copyN hsd hst hdt fs[i] (Sym.mark :: (hdrSyms (fs.drop (i + 1)) ++ rest)) S2
      (termOK_mark _) (by rw [hS2, Function.update_of_ne hsp, Function.update_self, hdrop,
        hdrSyms_cons_append'])
    have e : S2 dst = S dst := by
      rw [hS2, Function.update_of_ne hdp, Function.update_of_ne (Ne.symm hsd), hS1,
        Function.update_of_ne hdp]
    rw [e] at c
    rw [hS3]
    exact c
  have hL : Sym.sep ∉ (hdrSyms (fs.take i)).reverse := by
    rw [List.mem_reverse]; exact sep_not_mem_hdrSyms _
  have r4 := runs_liftRegs' lW (runs_xferSep (Ne.symm hsp) (hdrSyms (fs.take i)).reverse (S pk) S3 hL
    (by rw [hS3, Function.update_of_ne (Ne.symm hdp), hS2, Function.update_self]))
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · have e3 : S3 src = hdrSyms (fs.drop i) ++ rest := by
      rw [hS3, Function.update_of_ne hsd, hS2, Function.update_of_ne hsp, Function.update_self]
    rw [e3, List.reverse_reverse, ← List.append_assoc, ← hdrSyms_append, hsplit, ← hS]
    funext k
    by_cases e1 : k = src
    · rw [e1, Function.update_self, Function.update_of_ne hsd]
    by_cases e2 : k = pk
    · rw [e2, Function.update_of_ne (Ne.symm hsp), Function.update_self,
        Function.update_of_ne (Ne.symm hdp)]
    by_cases e3 : k = dst
    · rw [e3, Function.update_of_ne (Ne.symm hsd), Function.update_of_ne hdp, hS3,
        Function.update_self, Function.update_self]
    · rw [Function.update_of_ne e1, Function.update_of_ne e2, hS3, Function.update_of_ne e3, hS2,
        Function.update_of_ne e2, Function.update_of_ne e1, hS1, Function.update_of_ne e2,
        Function.update_of_ne e3]
  · have h1 := length_hdrSyms_take_le fs i
    have h2 := bitLen_hdr_mem (List.getElem_mem hi)
    simp only [copyFieldCost, List.length_reverse]
    omega

end CopyField

end SubNLogN.Machine.Layer.DrvParamsAux
