/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepElem
import SubNLogN.Machine.Calculus.Basic

/-!
# K5-SOLVE (1f): data-driven loops and whole-stack passes of the sweep kernel

* `rec1s w l`: the stack content of the one-coefficient records `l` (first on top).
* `pk`, `whileP`, `runs_whileP`: `while (top of x is a bit) { body }`, driven by the data (no
  counter): the iteration count is the number of records left on `x`.
* `drP`, `runs_drP1`: move all records of `x` onto `y` (record order reversed).
* `erP`, `runs_erP1`: pop one record.
All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-! ## One-coefficient record lists -/

@[simp] theorem rec1s_nil (w : ℕ) : rec1s w [] = [] := rfl

theorem rec1s_cons (w : ℕ) (c : CInt) (l : List CInt) :
    rec1s w (c :: l) = carrSyms w [[c]] ++ rec1s w l := by
  simp [rec1s, carrSyms, arrSyms, blk]

theorem rec1s_append (w : ℕ) (l l' : List CInt) : rec1s w (l ++ l') = rec1s w l ++ rec1s w l' := by
  simp [rec1s, carrSyms, arrSyms, blk]

theorem rec1s_eq_recsOf (w : ℕ) (l : List CInt) :
    rec1s w l = recsOf (l.map fun c => crecBits w [c]) := by
  rw [rec1s, carrSyms_eq_recsOf, List.map_map]; rfl

theorem rec1s_ne_nil_payload (w : ℕ) (hw : 1 ≤ w) (l : List CInt) :
    ∀ bs ∈ l.map (fun c => crecBits w [c]), bs ≠ [] := by
  intro bs hbs
  simp only [List.mem_map] at hbs
  obtain ⟨c, -, rfl⟩ := hbs
  intro h
  have := crecBits_one_length w c
  rw [h] at this
  simp at this; omega

/-- The top of `rec1s w l ++ r` is a bit iff `l ≠ []` (for `w ≥ 1`, `TermOK r`). -/
theorem optIsBit_rec1s (w : ℕ) (hw : 1 ≤ w) (l : List CInt) (r : List Sym) (hr : TermOK r) :
    optIsBit (rec1s w l ++ r).head? = decide (0 < l.length) := by
  cases l with
  | nil => simpa using optIsBit_head?_of_termOK hr
  | cons c l =>
    rw [rec1s_cons, carrSyms_one, recSyms_eq]
    have hlen := crecBits_one_length w c
    cases h : crecBits w [c] with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons b bs => simp [optIsBit]

section Loop

variable {LE σ : Type} [DecidableEq LE]

/-- Peek the top of a data/work stack into the `Option Sym` register. -/
def pk (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) : Prog (KS LE) (fun _ => Sym) σ :=
  (peekR (loc x)).liftRegs l

theorem runs_pk (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) (S : KS LE → List Sym) :
    Runs (pk l x) S S (fun v => l.get v = (S (loc x)).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  have e := Eval.liftRegs l (Eval.peek [] (loc x) (fun _ o => o) (l.get v) stk) v rfl
  exact ⟨_, 1, e, ⟨rfl, by simp [l.get_set]⟩, le_rfl⟩

/-- `pk x ; while (top of x is a bit) { body ; pk x }`. -/
def whileP (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) (body : Prog (KS LE) (fun _ => Sym) σ) :
    Prog (KS LE) (fun _ => Sym) σ :=
  .seq (pk l x) (.loop (fun v => optIsBit (l.get v)) (.seq body (pk l x)))

theorem runs_whileP (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) (body : Prog (KS LE) (fun _ => Sym) σ)
    (B : ℕ → KS LE → List Sym) (N : ℕ) (T : ℕ → ℕ)
    (htop : ∀ n, n ≤ N → optIsBit (B n (loc x)).head? = decide (0 < n))
    (hstep : ∀ n, n < N → Runs body (B (n + 1)) (B n) (fun _ => True) (T n)) :
    Runs (whileP l x body) (B N) (B 0) (fun _ => True) (1 + loopCost (fun n => T n + 1) N) := by
  have h0 : Runs (pk l x) (B N) (B N) (fun v => optIsBit (l.get v) = decide (0 < N)) 1 :=
    WP.W9comp.runs_mono (runs_pk l x (B N)) (fun v hv => by rw [hv]; exact htop N le_rfl) le_rfl
  have hs : ∀ n, n < N → Runs (.seq body (pk l x)) (B (n + 1)) (B n)
      (fun v => optIsBit (l.get v) = decide (0 < n)) (T n + 1) := fun n hn =>
    WP.W9comp.runs_seq (hstep n hn) (WP.W9comp.runs_mono (runs_pk l x (B n))
      (fun v hv => by rw [hv]; exact htop n (by omega)) le_rfl)
  have h0' : Calculus.RunsIn [] (pk l x) (B N) (B N)
      (fun v => optIsBit (l.get v) = decide (0 < N)) 1 := h0
  have hs' : ∀ n, n < N → Calculus.RunsIn [] (.seq body (pk l x)) (B (n + 1)) (B n)
      (fun v => optIsBit (l.get v) = decide (0 < n)) (T n + 1) := hs
  have h : Calculus.RunsIn [] (.seq (pk l x) (.loop (fun v => optIsBit (l.get v))
      (.seq body (pk l x)))) (B N) (B 0) (fun v => optIsBit (l.get v) = false)
      (1 + loopCost (fun n => T n + 1) N) := Calculus.RunsIn.seq_loop h0' hs'
  have h' : Runs (whileP l x body) (B N) (B 0) (fun v => optIsBit (l.get v) = false)
      (1 + loopCost (fun n => T n + 1) N) := h
  exact WP.W9comp.runs_mono h' (fun _ _ => trivial) le_rfl

/-- Move all records of `x` onto `y` (record order reversed), through `tmp`. -/
def drP (l : Lens σ (Option Sym)) (x y : SwD ⊕ SwW) : Prog (KS LE) (fun _ => Sym) σ :=
  (drainRecs (loc x) (loc y) (loc xT)).liftRegs l

theorem runs_drP1 (l : Lens σ (Option Sym)) {x y : SwD ⊕ SwW} (hxy : x ≠ y) (hx : x ≠ xT)
    (hy : y ≠ xT) (base : KS LE → List Sym) (V : SwD ⊕ SwW → List Sym) {w : ℕ} (hw : 1 ≤ w)
    (lst : List CInt) {rx : List Sym} (hV : V x = rec1s w lst ++ rx) (hrx : TermOK rx)
    (hT : V xT = []) :
    Runs (drP l x y) (mk base V)
      (mk base (Function.update (Function.update V x rx) y (rec1s w lst.reverse ++ V y)))
      (fun _ => True) (lst.length * (12 * w + 12) + 2) := by
  apply runs_liftRegs_of_eval
  intro v
  have h1 : loc (LE := LE) x ≠ loc y := fun e => hxy (loc_injective e)
  have h2 : loc (LE := LE) x ≠ loc xT := fun e => hx (loc_injective e)
  have h3 : loc (LE := LE) y ≠ loc xT := fun e => hy (loc_injective e)
  have e := drainRecs_eval h1 h2 h3 v (lst.map fun c => crecBits w [c]) rx (mk base V)
    (rec1s_ne_nil_payload w hw lst) (by rw [mk_loc, hV, rec1s_eq_recsOf]) hrx
    (by rw [mk_loc, hT]; exact TermOK.nil)
  refine ⟨rx.head?, e.of_eq ?_ ?_⟩
  · simp only [update_mk, mk_loc, rec1s_eq_recsOf, List.map_reverse]
  · simp only [drainCost, List.map_map]
    have hf : (fun bs : List Bool => 6 * bs.length + 12) ∘ (fun c : CInt => crecBits w [c]) =
        fun _ => 12 * w + 12 := by
      funext c; simp only [Function.comp_apply, crecBits_one_length]; ring
    rw [hf, List.map_const', List.sum_replicate, smul_eq_mul]

/-- Pop one record of `x`. -/
def erP (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) : Prog (KS LE) (fun _ => Sym) σ :=
  (eraseRec (loc x)).liftRegs l

theorem runs_erP1 (l : Lens σ (Option Sym)) (x : SwD ⊕ SwW) (base : KS LE → List Sym)
    (V : SwD ⊕ SwW → List Sym) {w : ℕ} {c : CInt} {r : List Sym}
    (hV : V x = carrSyms w [[c]] ++ r) :
    Runs (erP l x) (mk base V) (mk base (Function.update V x r)) (fun _ => True) (4 * w + 2) := by
  apply runs_liftRegs_of_eval
  intro v
  have e := eraseRec_eval (loc x) v (crecBits w [c]) r (mk base V)
    (by rw [mk_loc, hV, carrSyms_one])
  refine ⟨some Sym.sep, e.of_eq ?_ ?_⟩
  · simp only [update_mk]
  · rw [crecBits_one_length]; ring

end Loop

end SubNLogN.Machine.Bridge.SolveAux
