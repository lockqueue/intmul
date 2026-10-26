/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RadixBase

/-!
# Lemma A.8 radix padding, part 2 (`Machine/AppC/C6RadixRow.lean`): record moves and row passes

Record-level programs over an arbitrary stack type, as exact-stack `RunsIn` facts:
* `moveRecs src dst`: move the leading run of record symbols (bits and `sep`) of `src` onto `dst`
  (reversed) (`runsIn_moveRecs`);
* `copyRec`, `skipRec`, `emitZero`: copy one record onto an accumulator (reversed), discard one
  record, push one reversed zero record of width `w` (counter `mw`);
* `runsIn_copyRecs`, `runsIn_skipRecs`, `runsIn_emitZeros`: the same for a whole block, counting
  with a copy of a unary counter (`withCtr`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

The accumulator holds the reverse of the output produced so far (`(arrSyms pre).reverse`); the final
`moveRecs` restores the orientation.
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.Calculus SubNLogN.Machine.K1

theorem arrSyms_append (a b : List (List Bool)) : arrSyms (a ++ b) = arrSyms a ++ arrSyms b := by
  simp [arrSyms, blk]

theorem arrSyms_singleton (p : List Bool) : arrSyms [p] = recSyms p := by
  simp [arrSyms, blk]

theorem isRecTop_of_mem_arrSyms {v : List (List Bool)} {x : Sym} (hx : x ∈ arrSyms v) :
    isRecTop (some x) = true := by
  simp only [arrSyms, blk, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨p, _, rfl⟩, hx⟩ := hx
  simp only [recSyms, List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with ⟨b, _, rfl⟩ | rfl <;> rfl

theorem termOK_sep (rest : List Sym) : TermOK (Sym.sep :: rest) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

variable {K : Type} [DecidableEq K]

/-! ## Moving record symbols -/

/-- Pop the top of `src` and push it on `dst`. -/
theorem runsIn_popPush {ρ : List (SProg K)} {src dst : K} (hne : src ≠ dst) (x : Sym)
    (l : List Sym) (S : K → List Sym) (hS : S src = x :: l) :
    RunsIn ρ (.seq (popR src) (pushR dst)) S
      (Function.update (Function.update S src l) dst (x :: S dst)) (fun v => v = some x) 2 :=
  runsIn_of_eval fun v => by
    have e1 : Eval ρ (popR src) ⟨v, S⟩ ⟨some x, Function.update S src l⟩ 1 :=
      (Eval.pop ρ src (fun _ o => o) v S).of_eq (by simp [hS]) rfl
    have e2 := Eval.push ρ dst (fun r => r.getD .sep) (some x) (Function.update S src l)
    refine ⟨some x, 2, (Eval.seq e1 e2).of_eq ?_ rfl, rfl, le_rfl⟩
    rw [Function.update_of_ne (Ne.symm hne)]
    rfl

/-- Move the leading run of record symbols of `src` onto `dst` (reversed). -/
def moveRecs (src dst : K) : SProg K :=
  .seq (peekR src) (.loop isRecTop (.seq (.seq (popR src) (pushR dst)) (peekR src)))

theorem runsIn_moveRecs {ρ : List (SProg K)} {src dst : K} (hne : src ≠ dst) (l : List Sym)
    (hl : ∀ x ∈ l, isRecTop (some x) = true) {rest : List Sym}
    (hrest : isRecTop rest.head? = false) (S : K → List Sym) (hS : S src = l ++ rest) :
    RunsIn ρ (moveRecs src dst) S
      (Function.update (Function.update S src rest) dst (l.reverse ++ S dst)) (fun _ => True)
      (4 * l.length + 2) := by
  set L := l.length with hL
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := peekR src) (p := .seq (.seq (popR src) (pushR dst))
    (peekR src)) (c := isRecTop) (S := S)
    (st := fun m => Function.update (Function.update S src (l.drop (L - m) ++ rest)) dst
      ((l.take (L - m)).reverse ++ S dst))
    (B := fun _ => 3) (N := L) (T₀ := 1) ?h0 ?hstep
  · refine RunsIn.mono (RunsIn.congr h ?_ le_rfl) (fun _ _ => trivial) ?_
    · simp [hL]
    · rw [loopCost_const]; omega
  · have hp := runsIn_peekR ρ src S
    have e : S = Function.update (Function.update S src (l.drop (L - L) ++ rest)) dst
        ((l.take (L - L)).reverse ++ S dst) := by
      funext x
      simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        Function.update_apply]
      split_ifs with h1 h2 <;> simp_all
    refine RunsIn.mono (RunsIn.congr hp e le_rfl) (fun v hv => ?_) le_rfl
    rw [hv, hS]
    cases l with
    | nil => simpa [hL] using hrest
    | cons x l' =>
      simp only [List.cons_append, List.head?_cons, hL, List.length_cons]
      rw [hl x List.mem_cons_self]
      simp
  · intro m hm
    have hk : L - (m + 1) < l.length := by omega
    have hdrop : l.drop (L - (m + 1)) = l[L - (m + 1)] :: l.drop (L - m) := by
      rw [List.drop_eq_getElem_cons hk]
      congr 2
      omega
    have htake : l.take (L - m) = l.take (L - (m + 1)) ++ [l[L - (m + 1)]] := by
      have e1 : L - m = L - (m + 1) + 1 := by omega
      rw [e1, List.take_succ, List.getElem?_eq_getElem hk]
      rfl
    have hpp := runsIn_popPush (ρ := ρ) hne (l[L - (m + 1)]) (l.drop (L - m) ++ rest)
      (Function.update (Function.update S src (l.drop (L - (m + 1)) ++ rest)) dst
        ((l.take (L - (m + 1))).reverse ++ S dst))
      (by rw [Function.update_of_ne hne, Function.update_self, hdrop]; rfl)
    have hpk := runsIn_peekR ρ src (Function.update (Function.update S src (l.drop (L - m) ++ rest))
      dst ((l.take (L - m)).reverse ++ S dst))
    have e : Function.update (Function.update (Function.update (Function.update S src
        (l.drop (L - (m + 1)) ++ rest)) dst ((l.take (L - (m + 1))).reverse ++ S dst)) src
        (l.drop (L - m) ++ rest)) dst (l[L - (m + 1)] :: Function.update (Function.update S src
        (l.drop (L - (m + 1)) ++ rest)) dst ((l.take (L - (m + 1))).reverse ++ S dst) dst) =
        Function.update (Function.update S src (l.drop (L - m) ++ rest)) dst
          ((l.take (L - m)).reverse ++ S dst) := by
      rw [htake]
      funext x
      simp only [Function.update_apply, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.cons_append]
      split_ifs with h1 h2 h3 <;> simp_all
    rw [e] at hpp
    have hall := RunsIn.seq hpp hpk
    refine RunsIn.mono hall (fun v hv => ?_) le_rfl
    rw [hv, Function.update_of_ne hne, Function.update_self]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.sub_zero, hL, List.drop_length, List.nil_append, lt_self_iff_false,
        decide_false]
      exact hrest
    · have hlt : L - m < l.length := by omega
      rw [List.drop_eq_getElem_cons hlt]
      simp only [List.cons_append, List.head?_cons]
      rw [hl _ (List.getElem_mem hlt)]
      exact (decide_eq_true (by omega)).symm

/-! ## One record -/

/-- Copy one record from `src` onto `dst`, reversed. -/
def copyRec (src dst : K) : SProg K := .seq (moveBits src dst) (pushR dst)

theorem runsIn_copyRec {ρ : List (SProg K)} {src dst : K} (hne : src ≠ dst) (p : List Bool)
    (rest : List Sym) (S : K → List Sym) (hS : S src = recSyms p ++ rest) :
    RunsIn ρ (copyRec src dst) S
      (Function.update (Function.update S src rest) dst ((recSyms p).reverse ++ S dst))
      (fun _ => True) (3 * p.length + 3) :=
  runsIn_of_eval fun v => by
    have hS' : S src = p.map Sym.bit ++ (Sym.sep :: rest) := by rw [hS]; simp [recSyms]
    have e1 := moveBits_eval hne ρ v p (Sym.sep :: rest) S (termOK_sep rest) hS'
    have e2 := Eval.push ρ dst (fun r => r.getD .sep) (Sym.sep :: rest).head?
      (Function.update (Function.update S src (Sym.sep :: rest).tail) dst
        (p.reverse.map Sym.bit ++ S dst))
    refine ⟨(Sym.sep :: rest).head?, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by omega⟩
    congr 1
    funext x
    simp only [Function.update_apply, recSyms, List.reverse_append, List.map_reverse,
      List.reverse_singleton, List.singleton_append, List.cons_append, List.head?_cons,
      List.tail_cons, Option.getD_some]
    split_ifs with h1 h2 <;> simp_all

/-- Discard one record of `src`. -/
def skipRec (src : K) : SProg K := .seq (clearBits src) (popR src)

theorem runsIn_skipRec {ρ : List (SProg K)} (src : K) (p : List Bool) (rest : List Sym)
    (S : K → List Sym) (hS : S src = recSyms p ++ rest) :
    RunsIn ρ (skipRec src) S (Function.update S src rest) (fun _ => True) (4 * p.length + 3) := by
  have hS' : S src = p.map Sym.bit ++ (Sym.sep :: rest) := by rw [hS]; simp [recSyms]
  have h1 := runsIn_clearBits (ρ := ρ) src p (termOK_sep rest) S hS'
  have h2 := runsIn_popR ρ src (Function.update S src (Sym.sep :: rest)) Sym.sep rest
    (by rw [Function.update_self])
  rw [Function.update_idem] at h2
  exact RunsIn.mono (RunsIn.seq h1 h2) (fun _ _ => trivial) (by omega)

/-- Push one reversed zero record of width `w` (the counter on `mw`) on `acc`. -/
def emitZero (acc mw cw tmp : K) : SProg K :=
  .seq (withCtr mw cw tmp (pushC acc (.bit false))) (pushC acc .sep)

theorem recSyms_zero_reverse (w : ℕ) :
    (recSyms (List.replicate w false)).reverse = Sym.sep :: List.replicate w (Sym.bit false) := by
  simp [recSyms]

theorem runsIn_emitZero {ρ : List (SProg K)} {acc mw cw tmp : K} (ham : acc ≠ mw)
    (hac : acc ≠ cw) (hmc : mw ≠ cw) (hmt : mw ≠ tmp) (hct : cw ≠ tmp) (w : ℕ) {Tw : List Sym}
    (hTw : TermOK Tw) (S : K → List Sym) (hS : S mw = ublk w ++ Tw) :
    RunsIn ρ (emitZero acc mw cw tmp) S
      (Function.update S acc ((recSyms (List.replicate w false)).reverse ++ S acc))
      (fun _ => True) (11 * w + 12) := by
  have h1 := runsIn_withCtr (ρ := ρ) (body := pushC acc (.bit false)) hmc hmt hct w hTw
    (fun i => Function.update S acc (List.replicate i (Sym.bit false) ++ S acc))
    (by rw [Function.update_of_ne (Ne.symm ham)]; exact hS)
    (by simp only [Function.update_of_ne (Ne.symm hac)]) (fun _ => 1)
    (fun i _ => by
      have h := runsIn_pushC ρ acc (Sym.bit false)
        (Function.update (Function.update S acc (List.replicate i (Sym.bit false) ++ S acc)) cw
          (ublk (w - (i + 1)) ++ Sym.mark :: Function.update S acc
            (List.replicate 0 (Sym.bit false) ++ S acc) cw))
      refine RunsIn.congr h ?_ le_rfl
      funext x
      simp only [Function.update_apply, List.replicate_succ, List.cons_append]
      split_ifs with h1 h2 <;> simp_all)
  simp only [List.replicate_zero, List.nil_append, Function.update_eq_self] at h1
  have h2 := runsIn_pushC ρ acc Sym.sep
    (Function.update S acc (List.replicate w (Sym.bit false) ++ S acc))
  rw [Function.update_idem, Function.update_self] at h2
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq h1 h2) ?_ le_rfl) (fun _ _ => trivial) ?_
  · rw [recSyms_zero_reverse, List.cons_append]
  · rw [loopCost_const]; omega

/-! ## Blocks of records -/

/-- Copy a block of records (all of width `w`) onto the accumulator, counting with a copy of the
counter on `mK`. -/
theorem runsIn_copyRecs {ρ : List (SProg K)} {src acc mK c tmp : K}
    (hsa : src ≠ acc) (hsm : src ≠ mK) (hsc : src ≠ c) (ham : acc ≠ mK) (hac : acc ≠ c)
    (hmc : mK ≠ c) (hmt : mK ≠ tmp) (hct : c ≠ tmp)
    (blk rem pre : List (List Bool)) (w : ℕ) (hw : ∀ p ∈ blk, p.length = w)
    {T Y Tm : List Sym} (hTm : TermOK Tm) (S : K → List Sym)
    (hsrc : S src = arrSyms (blk ++ rem) ++ T) (hacc : S acc = (arrSyms pre).reverse ++ Y)
    (hmK : S mK = ublk blk.length ++ Tm) :
    RunsIn ρ (withCtr mK c tmp (copyRec src acc)) S
      (Function.update (Function.update S src (arrSyms rem ++ T)) acc
        ((arrSyms (pre ++ blk)).reverse ++ Y))
      (fun _ => True) (blk.length * (3 * w + 13) + 11) := by
  let F : ℕ → K → List Sym := fun i => Function.update (Function.update S src
    (arrSyms (blk.drop i ++ rem) ++ T)) acc ((arrSyms (pre ++ blk.take i)).reverse ++ Y)
  have hF0 : F 0 = S := by
    funext x
    simp only [F, List.drop_zero, List.take_zero, List.append_nil, Function.update_apply]
    split_ifs with h1 h2 <;> simp_all
  have hFn : F blk.length = Function.update (Function.update S src (arrSyms rem ++ T)) acc
      ((arrSyms (pre ++ blk)).reverse ++ Y) := by
    simp only [F, List.drop_length, List.nil_append, List.take_length]
  have hFc : ∀ i, F i c = S c := fun i => by
    simp only [F, Function.update_of_ne (Ne.symm hsc), Function.update_of_ne (Ne.symm hac)]
  have h := runsIn_withCtr (ρ := ρ) (body := copyRec src acc) hmc hmt hct blk.length hTm F
    (by rw [hF0]; exact hmK) (by rw [hFc, hFc]) (fun _ => 3 * w + 3)
    (fun i hi => by
      have hdrop : blk.drop i = blk[i] :: blk.drop (i + 1) := List.drop_eq_getElem_cons hi
      have h := runsIn_copyRec (ρ := ρ) hsa (blk[i]) (arrSyms (blk.drop (i + 1) ++ rem) ++ T)
        (Function.update (F i) c (ublk (blk.length - (i + 1)) ++ Sym.mark :: F 0 c))
        (by
          rw [Function.update_of_ne hsc]
          simp only [F, Function.update_of_ne hsa, Function.update_self, hdrop, List.cons_append,
            arrSyms_cons, List.append_assoc])
      rw [hw _ (List.getElem_mem hi)] at h
      refine RunsIn.congr h ?_ le_rfl
      have htake : blk.take (i + 1) = blk.take i ++ [blk[i]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hi]; rfl
      funext x
      simp only [F, Function.update_apply, htake, ← List.append_assoc, arrSyms_append,
        arrSyms_singleton, List.reverse_append]
      split_ifs with h1 h2 h3 h4 <;> simp_all)
  rw [hF0, hFn] at h
  refine RunsIn.mono h (fun _ _ => trivial) ?_
  rw [loopCost_const]
  apply le_of_eq
  ring

/-- Push `K2` reversed zero records of width `w` on the accumulator. -/
theorem runsIn_emitZeros {ρ : List (SProg K)} {acc mK c mw cw tmp : K}
    (ham : acc ≠ mK) (hac : acc ≠ c) (hamw : acc ≠ mw) (hacw : acc ≠ cw)
    (hmc : mK ≠ c) (hmt : mK ≠ tmp) (hct : c ≠ tmp) (hmwc : mw ≠ c) (hcwc : cw ≠ c)
    (hmwcw : mw ≠ cw) (hmwt : mw ≠ tmp) (hcwt : cw ≠ tmp)
    (K2 w : ℕ) (pre : List (List Bool)) {Y Tm Tw : List Sym} (hTm : TermOK Tm)
    (hTw : TermOK Tw) (S : K → List Sym) (hacc : S acc = (arrSyms pre).reverse ++ Y)
    (hmK : S mK = ublk K2 ++ Tm) (hmw : S mw = ublk w ++ Tw) :
    RunsIn ρ (withCtr mK c tmp (emitZero acc mw cw tmp)) S
      (Function.update S acc
        ((arrSyms (pre ++ List.replicate K2 (List.replicate w false))).reverse ++ Y))
      (fun _ => True) (K2 * (11 * w + 22) + 11) := by
  let F : ℕ → K → List Sym := fun i => Function.update S acc
    ((arrSyms (pre ++ List.replicate i (List.replicate w false))).reverse ++ Y)
  have hF0 : F 0 = S := by
    funext x
    simp only [F, List.replicate_zero, List.append_nil, Function.update_apply]
    split_ifs with h1 <;> simp_all
  have hFc : ∀ i, F i c = S c := fun i => by simp only [F, Function.update_of_ne (Ne.symm hac)]
  have h := runsIn_withCtr (ρ := ρ) (body := emitZero acc mw cw tmp) hmc hmt hct K2 hTm F
    (by rw [hF0]; exact hmK) (by rw [hFc, hFc]) (fun _ => 11 * w + 12)
    (fun i _ => by
      have h := runsIn_emitZero (ρ := ρ) hamw hacw hmwcw hmwt hcwt w hTw
        (Function.update (F i) c (ublk (K2 - (i + 1)) ++ Sym.mark :: F 0 c))
        (by
          rw [Function.update_of_ne hmwc]
          simp only [F, Function.update_of_ne (Ne.symm hamw)]
          exact hmw)
      refine RunsIn.congr h ?_ le_rfl
      funext x
      simp only [F, Function.update_apply, List.replicate_succ', ← List.append_assoc,
        arrSyms_append, arrSyms_singleton, List.reverse_append]
      split_ifs with h1 h2 h3 <;> simp_all)
  rw [hF0] at h
  refine RunsIn.mono h (fun _ _ => trivial) ?_
  rw [loopCost_const]
  apply le_of_eq
  ring

/-- Discard a block of records (all of width `w`), counting with a copy of the counter on `mK`. -/
theorem runsIn_skipRecs {ρ : List (SProg K)} {src mK c tmp : K}
    (hsm : src ≠ mK) (hsc : src ≠ c) (hmc : mK ≠ c) (hmt : mK ≠ tmp) (hct : c ≠ tmp)
    (blk rem : List (List Bool)) (w : ℕ) (hw : ∀ p ∈ blk, p.length = w)
    {T Tm : List Sym} (hTm : TermOK Tm) (S : K → List Sym)
    (hsrc : S src = arrSyms (blk ++ rem) ++ T) (hmK : S mK = ublk blk.length ++ Tm) :
    RunsIn ρ (withCtr mK c tmp (skipRec src)) S (Function.update S src (arrSyms rem ++ T))
      (fun _ => True) (blk.length * (4 * w + 13) + 11) := by
  let F : ℕ → K → List Sym := fun i => Function.update S src (arrSyms (blk.drop i ++ rem) ++ T)
  have hF0 : F 0 = S := by
    funext x
    simp only [F, List.drop_zero, Function.update_apply]
    split_ifs with h1 <;> simp_all
  have hFn : F blk.length = Function.update S src (arrSyms rem ++ T) := by
    simp only [F, List.drop_length, List.nil_append]
  have hFc : ∀ i, F i c = S c := fun i => by simp only [F, Function.update_of_ne (Ne.symm hsc)]
  have h := runsIn_withCtr (ρ := ρ) (body := skipRec src) hmc hmt hct blk.length hTm F
    (by rw [hF0]; exact hmK) (by rw [hFc, hFc]) (fun _ => 4 * w + 3)
    (fun i hi => by
      have hdrop : blk.drop i = blk[i] :: blk.drop (i + 1) := List.drop_eq_getElem_cons hi
      have h := runsIn_skipRec (ρ := ρ) src (blk[i]) (arrSyms (blk.drop (i + 1) ++ rem) ++ T)
        (Function.update (F i) c (ublk (blk.length - (i + 1)) ++ Sym.mark :: F 0 c))
        (by
          rw [Function.update_of_ne hsc]
          simp only [F, Function.update_self, hdrop, List.cons_append, arrSyms_cons,
            List.append_assoc])
      rw [hw _ (List.getElem_mem hi)] at h
      refine RunsIn.congr h ?_ le_rfl
      funext x
      simp only [F, Function.update_apply]
      split_ifs with h1 h2 <;> simp_all)
  rw [hF0, hFn] at h
  refine RunsIn.mono h (fun _ _ => trivial) ?_
  rw [loopCost_const]
  apply le_of_eq
  ring

/-! ## Row passes -/

/-- Row padding: blocks of `K1` records, each followed by `K2` zero records of width `w`. -/
def rowPadL (K1 K2 w M : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range M).flatMap fun i =>
    (v.drop (i * K1)).take K1 ++ List.replicate K2 (List.replicate w false)

/-- Row unpadding: blocks of `K1 + K2` records; keep the first `K1` records of each block. -/
def rowUnpadL (K1 K2 M : ℕ) (v : List (List Bool)) : List (List Bool) :=
  (List.range M).flatMap fun i => (v.drop (i * (K1 + K2))).take K1

theorem rowPadL_zero (K1 K2 w : ℕ) (v : List (List Bool)) : rowPadL K1 K2 w 0 v = [] := rfl

theorem rowPadL_succ (K1 K2 w M : ℕ) (v : List (List Bool)) :
    rowPadL K1 K2 w (M + 1) v = rowPadL K1 K2 w M v ++
      ((v.drop (M * K1)).take K1 ++ List.replicate K2 (List.replicate w false)) := by
  simp [rowPadL, List.range_succ, List.flatMap_append]

theorem rowUnpadL_zero (K1 K2 : ℕ) (v : List (List Bool)) : rowUnpadL K1 K2 0 v = [] := rfl

theorem rowUnpadL_succ (K1 K2 M : ℕ) (v : List (List Bool)) :
    rowUnpadL K1 K2 (M + 1) v = rowUnpadL K1 K2 M v ++ (v.drop (M * (K1 + K2))).take K1 := by
  simp [rowUnpadL, List.range_succ, List.flatMap_append]

/-- The loop test of a row pass: is there a record on top? -/
theorem isRecTop_arrSyms_drop {v : List (List Bool)} {T : List Sym} (hT : BlkTerm T) (k : ℕ) :
    isRecTop (arrSyms (v.drop k) ++ T).head? = decide (k < v.length) := by
  by_cases hk : k < v.length
  · rw [List.drop_eq_getElem_cons hk, isRecTop_cons]
    exact (decide_eq_true hk).symm
  · rw [List.drop_of_length_le (by omega), isRecTop_nil hT]
    exact (decide_eq_false hk).symm

theorem nodup9 {a b c d e f g h i : K} (hd : [a, b, c, d, e, f, g, h, i].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ a ≠ h ∧ a ≠ i ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧ b ≠ h ∧ b ≠ i ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ c ≠ g ∧ c ≠ h ∧ c ≠ i ∧
    d ≠ e ∧ d ≠ f ∧ d ≠ g ∧ d ≠ h ∧ d ≠ i ∧
    e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ e ≠ i ∧
    f ≠ g ∧ f ≠ h ∧ f ≠ i ∧ g ≠ h ∧ g ≠ i ∧ h ≠ i := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  tauto

/-- One block of the padding pass. -/
def padBody (src acc mK1 mK2 mw c1 c2 cw tmp : K) : SProg K :=
  .seq (withCtr mK1 c1 tmp (copyRec src acc)) (withCtr mK2 c2 tmp (emitZero acc mw cw tmp))

/-- The block loop of the padding pass. -/
def padLoop (src acc mK1 mK2 mw c1 c2 cw tmp : K) : SProg K :=
  .seq (peekR src) (.loop isRecTop (.seq (padBody src acc mK1 mK2 mw c1 c2 cw tmp) (peekR src)))

theorem runsIn_padLoop {ρ : List (SProg K)} {src acc mK1 mK2 mw c1 c2 cw tmp : K}
    (hd : [src, acc, mK1, mK2, mw, c1, c2, cw, tmp].Nodup)
    (K1 K2 w M : ℕ) (hK1 : 0 < K1) (v pre : List (List Bool)) (hv : v.length = M * K1)
    (hw : ∀ p ∈ v, p.length = w) {T Y T1 T2 Tw : List Sym} (hT : BlkTerm T)
    (hT1 : TermOK T1) (hT2 : TermOK T2) (hTw : TermOK Tw) (S : K → List Sym)
    (hsrc : S src = arrSyms v ++ T) (hacc : S acc = (arrSyms pre).reverse ++ Y)
    (hm1 : S mK1 = ublk K1 ++ T1) (hm2 : S mK2 = ublk K2 ++ T2) (hmw : S mw = ublk w ++ Tw) :
    RunsIn ρ (padLoop src acc mK1 mK2 mw c1 c2 cw tmp) S
      (Function.update (Function.update S src T) acc
        ((arrSyms (pre ++ rowPadL K1 K2 w M v)).reverse ++ Y))
      (fun _ => True) (M * (K1 * (3 * w + 13) + K2 * (11 * w + 22) + 24) + 2) := by
  obtain ⟨hsa, hs1, hs2, hsw, hsc1, hsc2, hscw, hst, ha1, ha2, haw, hac1, hac2, hacw, hat,
    h12, h1w, h1c1, h1c2, h1cw, h1t, h2w, h2c1, h2c2, h2cw, h2t, hwc1, hwc2, hwcw, hwt,
    hc1c2, hc1cw, hc1t, hc2cw, hc2t, hcwt⟩ := nodup9 hd
  let st : ℕ → K → List Sym := fun m => Function.update (Function.update S src
    (arrSyms (v.drop ((M - m) * K1)) ++ T)) acc
      ((arrSyms (pre ++ rowPadL K1 K2 w (M - m) v)).reverse ++ Y)
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := peekR src)
    (p := .seq (padBody src acc mK1 mK2 mw c1 c2 cw tmp) (peekR src)) (c := isRecTop) (S := S)
    (st := st) (B := fun _ => K1 * (3 * w + 13) + 11 + (K2 * (11 * w + 22) + 11) + 1) (N := M)
    (T₀ := 1) ?h0 ?hstep
  · refine RunsIn.mono (RunsIn.congr h ?_ le_rfl) (fun _ _ => trivial) ?_
    · simp only [st, Nat.sub_zero]
      rw [List.drop_of_length_le (by rw [hv]), arrSyms_nil, List.nil_append]
    · rw [loopCost_const]
      apply le_of_eq
      ring
  · have hp := runsIn_peekR ρ src S
    have e : S = st M := by
      funext x
      simp only [st, Nat.sub_self, Nat.zero_mul, List.drop_zero, rowPadL_zero, List.append_nil,
        Function.update_apply]
      split_ifs with h1 h2 <;> simp_all
    refine RunsIn.mono (RunsIn.congr hp e le_rfl) (fun r hr => ?_) le_rfl
    rw [hr, hsrc]
    have := isRecTop_arrSyms_drop (v := v) hT 0
    rw [List.drop_zero] at this
    rw [this, hv]
    simp only [decide_eq_decide]
    constructor
    · intro h0; exact Nat.pos_of_mul_pos_right h0
    · intro h0; exact Nat.mul_pos h0 hK1
  · intro m hm
    obtain ⟨i, hi⟩ : ∃ i, i = M - (m + 1) := ⟨_, rfl⟩
    have hMi : M - m = i + 1 := by omega
    have hiM : i + 1 ≤ M := by omega
    have hiK : i * K1 + K1 ≤ v.length := by
      rw [hv]
      calc i * K1 + K1 = (i + 1) * K1 := by ring
        _ ≤ M * K1 := Nat.mul_le_mul_right _ hiM
    obtain ⟨blk, hblk⟩ : ∃ blk, blk = (v.drop (i * K1)).take K1 := ⟨_, rfl⟩
    obtain ⟨rem, hrem⟩ : ∃ rem, rem = v.drop ((i + 1) * K1) := ⟨_, rfl⟩
    have hdd : (v.drop (i * K1)).drop K1 = rem := by
      rw [hrem, List.drop_drop]
      congr 1
      ring
    have hsplit : v.drop (i * K1) = blk ++ rem := by
      rw [hblk, ← hdd, List.take_append_drop]
    have hlen : blk.length = K1 := by
      rw [hblk, List.length_take, List.length_drop]
      omega
    have hwb : ∀ p ∈ blk, p.length = w := fun p hp => by
      rw [hblk] at hp
      exact hw p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
    have hst1 : st (m + 1) = Function.update (Function.update S src (arrSyms (blk ++ rem) ++ T))
        acc ((arrSyms (pre ++ rowPadL K1 K2 w i v)).reverse ++ Y) := by
      simp only [st]
      rw [← hi, hsplit]
    have h1 := runsIn_copyRecs (ρ := ρ) hsa hs1 hsc1 ha1 hac1 h1c1 h1t hc1t
      blk rem (pre ++ rowPadL K1 K2 w i v) w hwb hT1 (st (m + 1))
      (by rw [hst1, Function.update_of_ne hsa, Function.update_self])
      (by rw [hst1, Function.update_self])
      (by rw [hst1, Function.update_of_ne ha1.symm, Function.update_of_ne hs1.symm, hlen]; exact hm1)
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update (Function.update (st (m + 1)) src
        (arrSyms rem ++ T)) acc ((arrSyms (pre ++ rowPadL K1 K2 w i v ++ blk)).reverse ++ Y) :=
      ⟨_, rfl⟩
    rw [← hS1] at h1
    have h2 := runsIn_emitZeros (ρ := ρ) ha2 hac2 haw hacw h2c2 h2t hc2t hwc2 hc2cw.symm hwcw hwt
      hcwt K2 w (pre ++ rowPadL K1 K2 w i v ++ blk) hT2 hTw S1
      (by rw [hS1, Function.update_self])
      (by rw [hS1, Function.update_of_ne ha2.symm, Function.update_of_ne hs2.symm, hst1,
            Function.update_of_ne ha2.symm, Function.update_of_ne hs2.symm]; exact hm2)
      (by rw [hS1, Function.update_of_ne haw.symm, Function.update_of_ne hsw.symm, hst1,
            Function.update_of_ne haw.symm, Function.update_of_ne hsw.symm]; exact hmw)
    have hstm : st m = Function.update (Function.update S src (arrSyms rem ++ T)) acc
        ((arrSyms (pre ++ (rowPadL K1 K2 w i v ++ (blk ++
          List.replicate K2 (List.replicate w false))))).reverse ++ Y) := by
      simp only [st]
      rw [hMi, rowPadL_succ, ← hblk, ← hrem]
    have e2 : Function.update S1 acc ((arrSyms (pre ++ rowPadL K1 K2 w i v ++ blk ++
        List.replicate K2 (List.replicate w false))).reverse ++ Y) = st m := by
      rw [hstm, hS1, hst1, Function.update_idem, Function.update_comm hsa.symm,
        Function.update_idem, Function.update_idem]
      simp only [List.append_assoc]
    rw [e2] at h2
    have hpk := runsIn_peekR ρ src (st m)
    have hall := RunsIn.seq (RunsIn.seq h1 h2) hpk
    refine RunsIn.mono hall (fun r hr => ?_) (by rw [hlen])
    rw [hr]
    simp only [st, Function.update_of_ne hsa, Function.update_self]
    rw [isRecTop_arrSyms_drop hT, hv, decide_eq_decide]
    constructor
    · intro h0
      by_contra hm0
      have : M - m = M := by omega
      rw [this] at h0
      exact lt_irrefl _ h0
    · intro h0
      have : M - m < M := by omega
      exact Nat.mul_lt_mul_of_pos_right this hK1

theorem nodup7 {a b c d e f g : K} (hd : [a, b, c, d, e, f, g].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ a ≠ g ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ c ≠ g ∧ d ≠ e ∧ d ≠ f ∧ d ≠ g ∧ e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  tauto

/-- One block of the unpadding pass. -/
def unpadBody (src acc mK1 mK2 c1 c2 tmp : K) : SProg K :=
  .seq (withCtr mK1 c1 tmp (copyRec src acc)) (withCtr mK2 c2 tmp (skipRec src))

/-- The block loop of the unpadding pass. -/
def unpadLoop (src acc mK1 mK2 c1 c2 tmp : K) : SProg K :=
  .seq (peekR src) (.loop isRecTop (.seq (unpadBody src acc mK1 mK2 c1 c2 tmp) (peekR src)))

theorem runsIn_unpadLoop {ρ : List (SProg K)} {src acc mK1 mK2 c1 c2 tmp : K}
    (hd : [src, acc, mK1, mK2, c1, c2, tmp].Nodup)
    (K1 K2 w M : ℕ) (hK : 0 < K1 + K2) (v pre : List (List Bool))
    (hv : v.length = M * (K1 + K2)) (hw : ∀ p ∈ v, p.length = w) {T Y T1 T2 : List Sym}
    (hT : BlkTerm T) (hT1 : TermOK T1) (hT2 : TermOK T2) (S : K → List Sym)
    (hsrc : S src = arrSyms v ++ T) (hacc : S acc = (arrSyms pre).reverse ++ Y)
    (hm1 : S mK1 = ublk K1 ++ T1) (hm2 : S mK2 = ublk K2 ++ T2) :
    RunsIn ρ (unpadLoop src acc mK1 mK2 c1 c2 tmp) S
      (Function.update (Function.update S src T) acc
        ((arrSyms (pre ++ rowUnpadL K1 K2 M v)).reverse ++ Y))
      (fun _ => True) (M * (K1 * (3 * w + 13) + K2 * (4 * w + 13) + 24) + 2) := by
  obtain ⟨hsa, hs1, hs2, hsc1, hsc2, hst, ha1, ha2, hac1, hac2, hat, h12, h1c1, h1c2, h1t,
    h2c1, h2c2, h2t, hc1c2, hc1t, hc2t⟩ := nodup7 hd
  let st : ℕ → K → List Sym := fun m => Function.update (Function.update S src
    (arrSyms (v.drop ((M - m) * (K1 + K2))) ++ T)) acc
      ((arrSyms (pre ++ rowUnpadL K1 K2 (M - m) v)).reverse ++ Y)
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := peekR src)
    (p := .seq (unpadBody src acc mK1 mK2 c1 c2 tmp) (peekR src)) (c := isRecTop) (S := S)
    (st := st) (B := fun _ => K1 * (3 * w + 13) + 11 + (K2 * (4 * w + 13) + 11) + 1) (N := M)
    (T₀ := 1) ?h0 ?hstep
  · refine RunsIn.mono (RunsIn.congr h ?_ le_rfl) (fun _ _ => trivial) ?_
    · simp only [st, Nat.sub_zero]
      rw [List.drop_of_length_le (by rw [hv]), arrSyms_nil, List.nil_append]
    · rw [loopCost_const]
      apply le_of_eq
      ring
  · have hp := runsIn_peekR ρ src S
    have e : S = st M := by
      funext x
      simp only [st, Nat.sub_self, Nat.zero_mul, List.drop_zero, rowUnpadL_zero, List.append_nil,
        Function.update_apply]
      split_ifs with h1 h2 <;> simp_all
    refine RunsIn.mono (RunsIn.congr hp e le_rfl) (fun r hr => ?_) le_rfl
    rw [hr, hsrc]
    have := isRecTop_arrSyms_drop (v := v) hT 0
    rw [List.drop_zero] at this
    rw [this, hv]
    simp only [decide_eq_decide]
    constructor
    · intro h0; exact Nat.pos_of_mul_pos_right h0
    · intro h0; exact Nat.mul_pos h0 hK
  · intro m hm
    obtain ⟨i, hi⟩ : ∃ i, i = M - (m + 1) := ⟨_, rfl⟩
    have hMi : M - m = i + 1 := by omega
    have hiM : i + 1 ≤ M := by omega
    have hiK : i * (K1 + K2) + (K1 + K2) ≤ v.length := by
      rw [hv]
      calc i * (K1 + K2) + (K1 + K2) = (i + 1) * (K1 + K2) := by ring
        _ ≤ M * (K1 + K2) := Nat.mul_le_mul_right _ hiM
    obtain ⟨blk1, hb1⟩ : ∃ b, b = (v.drop (i * (K1 + K2))).take K1 := ⟨_, rfl⟩
    obtain ⟨blk2, hb2⟩ : ∃ b, b = ((v.drop (i * (K1 + K2))).drop K1).take K2 := ⟨_, rfl⟩
    obtain ⟨rem, hrem⟩ : ∃ rem, rem = v.drop ((i + 1) * (K1 + K2)) := ⟨_, rfl⟩
    have hdd : ((v.drop (i * (K1 + K2))).drop K1).drop K2 = rem := by
      rw [hrem, List.drop_drop, List.drop_drop]
      congr 1
      ring
    have hsplit : v.drop (i * (K1 + K2)) = blk1 ++ (blk2 ++ rem) := by
      rw [hb1, hb2, ← hdd, List.take_append_drop, List.take_append_drop]
    have hlen1 : blk1.length = K1 := by
      rw [hb1, List.length_take, List.length_drop]
      omega
    have hlen2 : blk2.length = K2 := by
      rw [hb2, List.length_take, List.length_drop, List.length_drop]
      omega
    have hwb1 : ∀ p ∈ blk1, p.length = w := fun p hp => by
      rw [hb1] at hp
      exact hw p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
    have hwb2 : ∀ p ∈ blk2, p.length = w := fun p hp => by
      rw [hb2] at hp
      exact hw p (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hp)))
    have hst1 : st (m + 1) = Function.update (Function.update S src
        (arrSyms (blk1 ++ (blk2 ++ rem)) ++ T)) acc
        ((arrSyms (pre ++ rowUnpadL K1 K2 i v)).reverse ++ Y) := by
      simp only [st]
      rw [← hi, hsplit]
    have h1 := runsIn_copyRecs (ρ := ρ) hsa hs1 hsc1 ha1 hac1 h1c1 h1t hc1t
      blk1 (blk2 ++ rem) (pre ++ rowUnpadL K1 K2 i v) w hwb1 hT1 (st (m + 1))
      (by rw [hst1, Function.update_of_ne hsa, Function.update_self])
      (by rw [hst1, Function.update_self])
      (by rw [hst1, Function.update_of_ne ha1.symm, Function.update_of_ne hs1.symm, hlen1]
          exact hm1)
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update (Function.update (st (m + 1)) src
        (arrSyms (blk2 ++ rem) ++ T)) acc
        ((arrSyms (pre ++ rowUnpadL K1 K2 i v ++ blk1)).reverse ++ Y) := ⟨_, rfl⟩
    rw [← hS1] at h1
    have h2 := runsIn_skipRecs (ρ := ρ) hs2 hsc2 h2c2 h2t hc2t blk2 rem w hwb2 hT2 S1
      (by rw [hS1, Function.update_of_ne hsa, Function.update_self])
      (by rw [hS1, Function.update_of_ne ha2.symm, Function.update_of_ne hs2.symm, hst1,
            Function.update_of_ne ha2.symm, Function.update_of_ne hs2.symm, hlen2]; exact hm2)
    have hstm : st m = Function.update (Function.update S src (arrSyms rem ++ T)) acc
        ((arrSyms (pre ++ (rowUnpadL K1 K2 i v ++ blk1))).reverse ++ Y) := by
      simp only [st]
      rw [hMi, rowUnpadL_succ, ← hb1, ← hrem]
    have e2 : Function.update S1 src (arrSyms rem ++ T) = st m := by
      rw [hstm, hS1, hst1]
      funext x
      by_cases hx : x = src
      · rw [hx]
        simp only [Function.update_self, Function.update_of_ne hsa]
      · by_cases hy : x = acc
        · rw [hy]
          simp only [Function.update_self, Function.update_of_ne hsa.symm, List.append_assoc]
        · simp only [Function.update_of_ne hx, Function.update_of_ne hy]
    rw [e2] at h2
    have hpk := runsIn_peekR ρ src (st m)
    have hall := RunsIn.seq (RunsIn.seq h1 h2) hpk
    refine RunsIn.mono hall (fun r hr => ?_) (by rw [hlen1, hlen2])
    rw [hr]
    simp only [st, Function.update_of_ne hsa, Function.update_self]
    rw [isRecTop_arrSyms_drop hT, hv, decide_eq_decide]
    constructor
    · intro h0
      by_contra hm0
      have : M - m = M := by omega
      rw [this] at h0
      exact lt_irrefl _ h0
    · intro h0
      have : M - m < M := by omega
      exact Nat.mul_lt_mul_of_pos_right this hK

/-! ## Whole passes -/

/-- The padding pass: install the accumulator delimiter, run the block loop, move the output back
(restoring the orientation), drop the delimiter. -/
def padPass (src acc mK1 mK2 mw c1 c2 cw tmp : K) : SProg K :=
  .seq (pushC acc .mark) (.seq (padLoop src acc mK1 mK2 mw c1 c2 cw tmp)
    (.seq (moveRecs acc src) (popR acc)))

theorem runsIn_padPass {ρ : List (SProg K)} {src acc mK1 mK2 mw c1 c2 cw tmp : K}
    (hd : [src, acc, mK1, mK2, mw, c1, c2, cw, tmp].Nodup)
    (K1 K2 w M : ℕ) (hK1 : 0 < K1) (v : List (List Bool)) (hv : v.length = M * K1)
    (hw : ∀ p ∈ v, p.length = w) {T T1 T2 Tw : List Sym} (hT : BlkTerm T)
    (hT1 : TermOK T1) (hT2 : TermOK T2) (hTw : TermOK Tw) (S : K → List Sym)
    (hsrc : S src = arrSyms v ++ T) (hm1 : S mK1 = ublk K1 ++ T1) (hm2 : S mK2 = ublk K2 ++ T2)
    (hmw : S mw = ublk w ++ Tw) :
    RunsIn ρ (padPass src acc mK1 mK2 mw c1 c2 cw tmp) S
      (Function.update S src (arrSyms (rowPadL K1 K2 w M v) ++ T)) (fun _ => True)
      (M * (K1 * (3 * w + 13) + K2 * (11 * w + 22) + 24) + 4 * vol (rowPadL K1 K2 w M v) + 6) := by
  have hsa : src ≠ acc := (nodup9 hd).1
  have ha1 : acc ≠ mK1 := (nodup9 hd).2.2.2.2.2.2.2.2.1
  have ha2 : acc ≠ mK2 := (nodup9 hd).2.2.2.2.2.2.2.2.2.1
  have haw : acc ≠ mw := (nodup9 hd).2.2.2.2.2.2.2.2.2.2.1
  have h1 := runsIn_pushC ρ acc Sym.mark S
  have h2 := runsIn_padLoop (ρ := ρ) hd K1 K2 w M hK1 v [] hv hw (Y := Sym.mark :: S acc) hT hT1
    hT2 hTw (Function.update S acc (Sym.mark :: S acc))
    (by rw [Function.update_of_ne hsa]; exact hsrc) (by rw [Function.update_self]; rfl)
    (by rw [Function.update_of_ne ha1.symm]; exact hm1)
    (by rw [Function.update_of_ne ha2.symm]; exact hm2)
    (by rw [Function.update_of_ne haw.symm]; exact hmw)
  rw [List.nil_append] at h2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update (Function.update (Function.update S acc
      (Sym.mark :: S acc)) src T) acc ((arrSyms (rowPadL K1 K2 w M v)).reverse ++ Sym.mark :: S acc) :=
    ⟨_, rfl⟩
  rw [← hS2] at h2
  have h3 := runsIn_moveRecs (ρ := ρ) hsa.symm (arrSyms (rowPadL K1 K2 w M v)).reverse
    (fun x hx => isRecTop_of_mem_arrSyms (List.mem_reverse.mp hx)) (rest := Sym.mark :: S acc)
    rfl S2 (by rw [hS2, Function.update_self])
  have h4 := runsIn_popR ρ acc (Function.update (Function.update S2 acc (Sym.mark :: S acc)) src
    ((arrSyms (rowPadL K1 K2 w M v)).reverse.reverse ++ S2 src)) Sym.mark (S acc) (by
    rw [Function.update_of_ne hsa.symm, Function.update_self])
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
  refine RunsIn.mono (RunsIn.congr hall ?_ le_rfl) (fun _ _ => trivial) ?_
  · rw [hS2]
    funext x
    by_cases hx : x = src
    · rw [hx]
      simp only [Function.update_self, Function.update_of_ne hsa, List.reverse_reverse]
    · by_cases hy : x = acc
      · rw [hy]
        simp only [Function.update_self, Function.update_of_ne hsa.symm]
      · simp only [Function.update_of_ne hx, Function.update_of_ne hy]
  · simp only [List.length_reverse, vol]
    omega

/-- The unpadding pass. -/
def unpadPass (src acc mK1 mK2 c1 c2 tmp : K) : SProg K :=
  .seq (pushC acc .mark) (.seq (unpadLoop src acc mK1 mK2 c1 c2 tmp)
    (.seq (moveRecs acc src) (popR acc)))

theorem runsIn_unpadPass {ρ : List (SProg K)} {src acc mK1 mK2 c1 c2 tmp : K}
    (hd : [src, acc, mK1, mK2, c1, c2, tmp].Nodup)
    (K1 K2 w M : ℕ) (hK : 0 < K1 + K2) (v : List (List Bool)) (hv : v.length = M * (K1 + K2))
    (hw : ∀ p ∈ v, p.length = w) {T T1 T2 : List Sym} (hT : BlkTerm T)
    (hT1 : TermOK T1) (hT2 : TermOK T2) (S : K → List Sym)
    (hsrc : S src = arrSyms v ++ T) (hm1 : S mK1 = ublk K1 ++ T1)
    (hm2 : S mK2 = ublk K2 ++ T2) :
    RunsIn ρ (unpadPass src acc mK1 mK2 c1 c2 tmp) S
      (Function.update S src (arrSyms (rowUnpadL K1 K2 M v) ++ T)) (fun _ => True)
      (M * (K1 * (3 * w + 13) + K2 * (4 * w + 13) + 24) + 4 * vol (rowUnpadL K1 K2 M v) + 6) := by
  have hsa : src ≠ acc := (nodup7 hd).1
  have ha1 : acc ≠ mK1 := (nodup7 hd).2.2.2.2.2.2.1
  have ha2 : acc ≠ mK2 := (nodup7 hd).2.2.2.2.2.2.2.1
  have h1 := runsIn_pushC ρ acc Sym.mark S
  have h2 := runsIn_unpadLoop (ρ := ρ) hd K1 K2 w M hK v [] hv hw (Y := Sym.mark :: S acc) hT hT1
    hT2 (Function.update S acc (Sym.mark :: S acc))
    (by rw [Function.update_of_ne hsa]; exact hsrc) (by rw [Function.update_self]; rfl)
    (by rw [Function.update_of_ne ha1.symm]; exact hm1)
    (by rw [Function.update_of_ne ha2.symm]; exact hm2)
  rw [List.nil_append] at h2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update (Function.update (Function.update S acc
      (Sym.mark :: S acc)) src T) acc ((arrSyms (rowUnpadL K1 K2 M v)).reverse ++ Sym.mark :: S acc) :=
    ⟨_, rfl⟩
  rw [← hS2] at h2
  have h3 := runsIn_moveRecs (ρ := ρ) hsa.symm (arrSyms (rowUnpadL K1 K2 M v)).reverse
    (fun x hx => isRecTop_of_mem_arrSyms (List.mem_reverse.mp hx)) (rest := Sym.mark :: S acc)
    rfl S2 (by rw [hS2, Function.update_self])
  have h4 := runsIn_popR ρ acc (Function.update (Function.update S2 acc (Sym.mark :: S acc)) src
    ((arrSyms (rowUnpadL K1 K2 M v)).reverse.reverse ++ S2 src)) Sym.mark (S acc) (by
    rw [Function.update_of_ne hsa.symm, Function.update_self])
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
  refine RunsIn.mono (RunsIn.congr hall ?_ le_rfl) (fun _ _ => trivial) ?_
  · rw [hS2]
    funext x
    by_cases hx : x = src
    · rw [hx]
      simp only [Function.update_self, Function.update_of_ne hsa, List.reverse_reverse]
    · by_cases hy : x = acc
      · rw [hy]
        simp only [Function.update_self, Function.update_of_ne hsa.symm]
      · simp only [Function.update_of_ne hx, Function.update_of_ne hy]
  · simp only [List.length_reverse, vol]
    omega


end SubNLogN.Machine.AppC.C6RadixAux
