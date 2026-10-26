/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Ruler

/-!
# AR array driver (`Arith/Driver.lean`): run a field program over every field of an array

**Scope (honest summary).** A record/array loop that is generic in the field program, and its
exact evaluation lemma. Everything is proved (no `sorry`).

* `FieldSpec fp src T w1 w2 f cf S0`: from any stacks that agree with `S0` outside `src` and `T`,
  with `src` holding the `w1`-bit field of `z` on top, `fp` pops that field and pushes the `w2`-bit
  field of `f z` onto `T` (in push order, so `T` shows it reversed), at exact cost `cf`.
* `fieldLoop_eval`: all fields of one record. `recBody_eval`: one record (then its `sep`).
  `recLoop_eval`: all records of an array, down to a `BlkTerm` rest.
* `carrSyms_eq_arrFields`, `carrSyms_mapC`: a complex record array is an array of
  records of components (`comps`), each component one field.

The output stream is accumulated on `T` in push order and is reversed onto the destination at the
end by `WP.W9comp.rewindTo` (in the kernels).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Components of complex records -/

/-- The components of a complex record, in storage order: `re₀, im₀, re₁, im₁, …`. -/
def comps (cs : List CInt) : List ℤ := cs.flatMap fun c => [c.1, c.2]

theorem crecBits_eq (w : ℕ) (cs : List CInt) :
    crecBits w cs = (comps cs).flatMap (twosBits w) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [crecBits, comps, List.flatMap_cons, coefBits] at ih ⊢
    rw [ih]
    simp

theorem comps_map (f : ℤ → ℤ) (cs : List CInt) :
    comps (cs.map fun c => (f c.1, f c.2)) = (comps cs).map f := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [comps, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    simp

/-- A record array whose records are lists of fields. -/
def arrFields (w : ℕ) (vs : List (List ℤ)) : List Sym :=
  arrSyms (vs.map fun zs => zs.flatMap (twosBits w))

theorem carrSyms_eq_arrFields (w : ℕ) (v : List (List CInt)) :
    carrSyms w v = arrFields w (v.map comps) := by
  simp only [carrSyms, arrFields, List.map_map]
  congr 2
  funext cs
  simp [crecBits_eq]

theorem carrSyms_mapC (w : ℕ) (f : ℤ → ℤ) (v : List (List CInt)) :
    carrSyms w (mapC (fun c => (f c.1, f c.2)) v) = arrFields w ((v.map comps).map (List.map f)) := by
  simp only [carrSyms, arrFields, mapC, List.map_map]
  congr 2
  funext cs
  simp [crecBits_eq, comps_map]

/-! ## Programs -/

variable {K : Type}

/-- The symbol starts a record: a bit or the record end `sep`. -/
def isRecO : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

/-- Run the field program `fp` while the source shows a bit. -/
def fieldLoop (fp : AProg K) (src : K) : AProg K :=
  .loop (fun v => isBitO v.o) (.seq fp (peekO src))

/-- One record: its fields, then its end `sep` (moved to `T`). -/
def recBody (fp : AProg K) (src T : K) : AProg K :=
  .seq (fieldLoop fp src) (.seq (drop1 src) (.seq (pushS T .sep) (peekO src)))

/-- All records of the array on `src`. -/
def recLoop (fp : AProg K) (src T : K) : AProg K :=
  .loop (fun v => isRecO v.o) (recBody fp src T)

variable [DecidableEq K]

/-- **Field-level contract** of a field program (see the module docstring). -/
def FieldSpec (fp : AProg K) (src T : K) (w1 w2 : ℕ) (f : ℤ → ℤ) (cf : ℕ)
    (S0 : K → List Sym) : Prop :=
  ∀ (z : ℤ) (L : List Sym) (v : AReg) (S : K → List Sym), FitsTwos w1 z →
    (∀ k, k ≠ src → k ≠ T → S k = S0 k) → S src = (twosBits w1 z).map Sym.bit ++ L →
    ∃ v' : AReg, Eval [] fp ⟨v, S⟩ ⟨v', Function.update (Function.update S src L) T
      ((twosBits w2 (f z)).reverse.map Sym.bit ++ S T)⟩ cf

theorem fieldLoop_eval {fp : AProg K} {src T : K} {w1 w2 : ℕ} {f : ℤ → ℤ} {cf : ℕ}
    {S0 : K → List Sym} (hsT : src ≠ T) (hw1 : 1 ≤ w1) (hfp : FieldSpec fp src T w1 w2 f cf S0) :
    ∀ (zs : List ℤ) (L : List Sym) (v : AReg) (S : K → List Sym), (∀ z ∈ zs, FitsTwos w1 z) →
      (∀ k, k ≠ src → k ≠ T → S k = S0 k) → isBitO L.head? = false →
      S src = (zs.flatMap (twosBits w1)).map Sym.bit ++ L → v.o = (S src).head? →
      ∃ v' : AReg, v'.o = L.head? ∧ Eval [] (fieldLoop fp src) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src L) T
          (((zs.map f).flatMap (twosBits w2)).reverse.map Sym.bit ++ S T)⟩
        (zs.length * (cf + 2) + 1)
  | [], L, v, S, _, _, hL, hsrc, hv => by
    simp only [List.flatMap_nil, List.map_nil, List.nil_append] at hsrc
    refine ⟨v, by rw [hv, hsrc], (Eval.loop_false (by rw [hv, hsrc]; exact hL)).of_eq ?_
      (by simp)⟩
    simp only [List.map_nil, List.flatMap_nil, List.reverse_nil, List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  | z :: zs, L, v, S, hzs, hS, hL, hsrc, hv => by
    have hz := hzs z List.mem_cons_self
    have hsrc' : S src = (twosBits w1 z).map Sym.bit ++
        ((zs.flatMap (twosBits w1)).map Sym.bit ++ L) := by
      rw [hsrc, List.flatMap_cons, List.map_append, List.append_assoc]
    obtain ⟨v1, e1⟩ := hfp z _ v S hz hS hsrc'
    set S1 := Function.update (Function.update S src ((zs.flatMap (twosBits w1)).map Sym.bit ++ L))
      T ((twosBits w2 (f z)).reverse.map Sym.bit ++ S T) with hS1
    have h1src : S1 src = (zs.flatMap (twosBits w1)).map Sym.bit ++ L := by
      rw [hS1, Function.update_of_ne hsT, Function.update_self]
    have e2 : Eval [] (peekO src) ⟨v1, S1⟩
        ⟨{ v1 with o := ((zs.flatMap (twosBits w1)).map Sym.bit ++ L).head? }, S1⟩ 1 := by
      refine (eval_peekO src v1 S1).of_eq ?_ rfl
      rw [h1src]
    obtain ⟨v', hv', e'⟩ := fieldLoop_eval hsT hw1 hfp zs L
      { v1 with o := ((zs.flatMap (twosBits w1)).map Sym.bit ++ L).head? } S1
      (fun z' hz' => hzs z' (List.mem_cons_of_mem _ hz'))
      (fun k hk1 hk2 => by
        rw [hS1, Function.update_of_ne hk2, Function.update_of_ne hk1]; exact hS k hk1 hk2)
      hL h1src (by rw [h1src])
    have hc : isBitO v.o = true := by
      rw [hv, hsrc']
      obtain ⟨k, rfl⟩ : ∃ k, w1 = k + 1 := ⟨w1 - 1, by omega⟩
      rw [K1.twosBits_succ]
      rfl
    refine ⟨v', hv', (Eval.loop_true hc (Eval.seq e1 e2) e').of_eq ?_
      (by simp only [List.length_cons]; ring)⟩
    congr 1
    funext k
    simp only [hS1, Function.update_apply, List.map_cons, List.flatMap_cons, List.reverse_append,
      List.map_append, List.append_assoc]
    split_ifs <;> simp_all

theorem recSyms_reverse_bits (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: p.reverse.map Sym.bit := by
  simp [recSyms, List.map_reverse]

theorem recBody_eval {fp : AProg K} {src T : K} {w1 w2 : ℕ} {f : ℤ → ℤ} {cf : ℕ}
    {S0 : K → List Sym} (hsT : src ≠ T) (hw1 : 1 ≤ w1) (hfp : FieldSpec fp src T w1 w2 f cf S0)
    (zs : List ℤ) (L : List Sym) (v : AReg) (S : K → List Sym) (hzs : ∀ z ∈ zs, FitsTwos w1 z)
    (hS : ∀ k, k ≠ src → k ≠ T → S k = S0 k)
    (hsrc : S src = (zs.flatMap (twosBits w1)).map Sym.bit ++ Sym.sep :: L)
    (hv : v.o = (S src).head?) :
    ∃ v' : AReg, v'.o = L.head? ∧ Eval [] (recBody fp src T) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src L) T
        ((recSyms ((zs.map f).flatMap (twosBits w2))).reverse ++ S T)⟩
      (zs.length * (cf + 2) + 4) := by
  obtain ⟨v1, -, e1⟩ := fieldLoop_eval hsT hw1 hfp zs (Sym.sep :: L) v S hzs hS rfl hsrc hv
  set S1 := Function.update (Function.update S src (Sym.sep :: L)) T
    (((zs.map f).flatMap (twosBits w2)).reverse.map Sym.bit ++ S T) with hS1
  have h1src : S1 src = Sym.sep :: L := by rw [hS1, Function.update_of_ne hsT, Function.update_self]
  have e2 := eval_drop1 src v1 S1 _ _ h1src
  have e3 := eval_pushS T .sep v1 (Function.update S1 src L)
  have e4 := eval_peekO src v1 (Function.update (Function.update S1 src L) T
    (Sym.sep :: Function.update S1 src L T))
  have h4 : (Function.update (Function.update S1 src L) T
      (Sym.sep :: Function.update S1 src L T) src).head? = L.head? := by
    rw [Function.update_of_ne hsT, Function.update_self]
  rw [h4] at e4
  refine ⟨{ v1 with o := L.head? }, rfl, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_
    (by ring)⟩
  congr 1
  funext k
  simp only [hS1, Function.update_apply, recSyms_reverse_bits]
  split_ifs <;> simp_all

theorem isRecO_false_of_blkTerm {rest : List Sym} (h : BlkTerm rest) : isRecO rest.head? = false := by
  rcases rest with _ | ⟨y, rest⟩
  · rfl
  · obtain ⟨h1, h2⟩ := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [isDataSym]

theorem arrFields_cons (w : ℕ) (zs : List ℤ) (vs : List (List ℤ)) :
    arrFields w (zs :: vs) = (zs.flatMap (twosBits w)).map Sym.bit ++ Sym.sep :: arrFields w vs := by
  simp [arrFields, arrSyms, blk, recSyms]

/-- The exact cost of `recLoop` on records with the given numbers of fields. -/
def recLoopCost (cf : ℕ) (vs : List (List ℤ)) : ℕ :=
  (vs.map fun zs => zs.length * (cf + 2) + 5).sum + 1

theorem recLoop_eval {fp : AProg K} {src T : K} {w1 w2 : ℕ} {f : ℤ → ℤ} {cf : ℕ}
    {S0 : K → List Sym} (hsT : src ≠ T) (hw1 : 1 ≤ w1) (hfp : FieldSpec fp src T w1 w2 f cf S0) :
    ∀ (vs : List (List ℤ)) (rest : List Sym) (v : AReg) (S : K → List Sym),
      (∀ zs ∈ vs, ∀ z ∈ zs, FitsTwos w1 z) → BlkTerm rest →
      (∀ k, k ≠ src → k ≠ T → S k = S0 k) → S src = arrFields w1 vs ++ rest →
      v.o = (S src).head? →
      ∃ v' : AReg, Eval [] (recLoop fp src T) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src rest) T
          ((arrFields w2 (vs.map (List.map f))).reverse ++ S T)⟩ (recLoopCost cf vs)
  | [], rest, v, S, _, hrest, _, hsrc, hv => by
    simp only [arrFields, List.map_nil, arrSyms, blk, List.flatten_nil, List.nil_append] at hsrc
    refine ⟨v, (Eval.loop_false (by rw [hv, hsrc]; exact isRecO_false_of_blkTerm hrest)).of_eq ?_
      (by simp [recLoopCost])⟩
    simp only [List.map_nil, arrFields, arrSyms, blk, List.flatten_nil, List.reverse_nil,
      List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  | zs :: vs, rest, v, S, hvs, hrest, hS, hsrc, hv => by
    have hsrc' : S src = (zs.flatMap (twosBits w1)).map Sym.bit ++ Sym.sep ::
        (arrFields w1 vs ++ rest) := by
      rw [hsrc, arrFields_cons, List.append_assoc, List.cons_append]
    obtain ⟨v1, hv1, e1⟩ := recBody_eval hsT hw1 hfp zs _ v S (hvs zs List.mem_cons_self) hS
      hsrc' (by rw [hv, hsrc'])
    set S1 := Function.update (Function.update S src (arrFields w1 vs ++ rest)) T
      ((recSyms ((zs.map f).flatMap (twosBits w2))).reverse ++ S T) with hS1
    have h1src : S1 src = arrFields w1 vs ++ rest := by
      rw [hS1, Function.update_of_ne hsT, Function.update_self]
    obtain ⟨v', e'⟩ := recLoop_eval hsT hw1 hfp vs rest v1 S1
      (fun zs' hzs' => hvs zs' (List.mem_cons_of_mem _ hzs')) hrest
      (fun k hk1 hk2 => by
        rw [hS1, Function.update_of_ne hk2, Function.update_of_ne hk1]; exact hS k hk1 hk2)
      h1src (by rw [hv1, h1src])
    have hc : isRecO v.o = true := by
      rw [hv, hsrc']
      rcases zs.flatMap (twosBits w1) with _ | ⟨b, l⟩ <;> rfl
    have hcost : zs.length * (cf + 2) + 4 + recLoopCost cf vs + 1 = recLoopCost cf (zs :: vs) := by
      simp only [recLoopCost, List.map_cons, List.sum_cons]
      ring
    refine ⟨v', (Eval.loop_true hc e1 e').of_eq ?_ hcost⟩
    congr 1
    funext k
    simp only [hS1, Function.update_apply, List.map_cons, arrFields, arrSyms, blk,
      List.flatten_cons, List.reverse_append, List.append_assoc]
    split_ifs <;> simp_all [arrFields, arrSyms, blk]
