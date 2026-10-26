/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitBuild

/-!
# K1 digit engine, part 3 (`K1/DigitPhase.lean`): distribute and merge phases

Paper: Lemma A.4(1) (`lem:transfer-streams`, proof: "split the array among `q²`
tapes according to the two digit values; within every stream the remaining address fields keep
their order, and merging with the permuted pair of labels gives the result").

**Scope (honest summary).** Programs and exact evaluation lemmas for the two phases; the
combinatorial merge lemma `filter_eq_map_filter`. No contract is proved in this file.

## Design
* **Leaf** `leafP srcOf dstOf`: a `cascade` over all `q²` keys selects, for the key `κ` in the
  register, the record move `moveRecP (srcOf κ) (dstOf κ)`: push `sep` on the destination, then move
  the payload bits (reversed). A stream holds records as `recRev p = p.reverse.map bit ++ [sep]`, so
  a second move restores `recSyms p`. Cost `≤ 3|p| + 3 + q²`.
* **Distribute** (`phase1_eval`): the walk in address order; record `x` goes to the stream
  `s1 x`. State after `t` records: `st1 … t` (source `arrSyms (v.drop t) ++ rest`, stream `s` holds
  the records `x < t` with `s1 x = s`, last on top).
* **Merge** (`phase2_eval`): the walk in reverse address order; the leaf for output address `y`
  pops stream `s2 y` and pushes the record onto the destination. State after `u` outputs:
  `st2 … u`.
* **Consistency** (`filter_eq_map_filter`): if `f` maps `[0, N)` into itself, `s1 (f y) = s2 y`, and
  `f` is strictly increasing on each fiber of `s2`, then stream `s` after the distribute phase is
  exactly what the merge phase expects: `(range N).filter (s1 · = s) = ((range N).filter
  (s2 · = s)).map f`. The output is then `permByInv f v`.
* **Cost**: potentials `3·(remaining volume) + q²·(remaining records)`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Moving one record -/

section Move

variable {K : Type} {q : ℕ}

/-- Move the top record of `src` onto `dst`: push `sep`, then the payload bits (reversed); the
record end of `src` is consumed. -/
def moveRecP (src dst : K) : SProg K := .seq (pushC dst .sep) (moveBits src dst)

/-- A record as stored on a stream: payload reversed, then `sep`. -/
def recRev (p : List Bool) : List Sym := p.reverse.map Sym.bit ++ [Sym.sep]

theorem moveRecP_closed (src dst : K) : (moveRecP src dst).Closed := by
  simp [moveRecP, moveBits, moveBitsBody, pushC, pushR, popR, Prog.Closed, Prog.FreeBelow]

/-- Select a program by the key register. -/
def cascade (f : Key q → DProg K q) : List (Key q) → DProg K q
  | [] => skip
  | κ :: ks => .ite (fun v => decide (v.2 = κ)) (f κ) (cascade f ks)

/-- All keys. -/
def allKeys (q : ℕ) : List (Key q) :=
  (List.finRange q).flatMap fun a => (List.finRange q).map fun b => (a, b)

theorem mem_allKeys (κ : Key q) : κ ∈ allKeys q := by
  simp [allKeys]

theorem cascade_closed (f : Key q → DProg K q) (hf : ∀ κ, (f κ).Closed) :
    ∀ ks, (cascade f ks).Closed
  | [] => by simp [cascade, skip, Prog.Closed, Prog.FreeBelow]
  | κ :: ks => ⟨hf κ, cascade_closed f hf ks⟩

/-- **The leaf**: move one record from `srcOf κ` to `dstOf κ`, `κ` the key register. -/
def leafP (srcOf dstOf : Key q → K) : DProg K q :=
  cascade (fun κ => liftS (moveRecP (srcOf κ) (dstOf κ))) (allKeys q)

theorem leafP_closed (srcOf dstOf : Key q → K) : (leafP srcOf dstOf).Closed :=
  cascade_closed _ (fun _ => liftS_closed (moveRecP_closed _ _)) _

variable [DecidableEq K]

theorem moveRecP_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (p : List Bool)
    (rest : List Sym) (S : K → List Sym) (hS : S src = p.map Sym.bit ++ Sym.sep :: rest) :
    Eval [] (moveRecP src dst) ⟨v, S⟩
      ⟨some Sym.sep, Function.update (Function.update S src rest) dst
        (p.reverse.map Sym.bit ++ Sym.sep :: S dst)⟩ (3 * p.length + 3) := by
  have e1 : Eval [] (pushC dst Sym.sep) ⟨v, S⟩ ⟨v, Function.update S dst (Sym.sep :: S dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  have hS' : Function.update S dst (Sym.sep :: S dst) src = p.map Sym.bit ++ (Sym.sep :: rest) := by
    rw [Function.update_of_ne hne]
    exact hS
  have e2 := moveBits_eval hne [] v p (Sym.sep :: rest) _ (TermOK.cons rfl _) hS'
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  congr 1
  funext x
  by_cases h1 : x = dst
  · subst h1
    simp [Function.update_apply]
  · by_cases h2 : x = src
    · subst h2
      simp [Function.update_apply, h1]
    · simp [Function.update_apply, h1, h2]

theorem cascade_eval (f : Key q → DProg K q) (ρ' : List (DProg K q)) {w : CReg} {κ : Key q}
    {S : K → List Sym} {s' : St K (fun _ => Sym) (Reg q)} {c : ℕ}
    (he : Eval ρ' (f κ) ⟨(w, κ), S⟩ s' c) :
    ∀ ks : List (Key q), κ ∈ ks → ∃ c', c' ≤ c + ks.length ∧
      Eval ρ' (cascade f ks) ⟨(w, κ), S⟩ s' c'
  | [], h => absurd h List.not_mem_nil
  | κ' :: ks, h => by
    by_cases hk : κ = κ'
    · subst hk
      exact ⟨c + 1, by simp, Eval.ite_true (by simp) he⟩
    · have hm : κ ∈ ks := by
        rcases List.mem_cons.1 h with h' | h'
        · exact absurd h' hk
        · exact h'
      obtain ⟨c', hc', e⟩ := cascade_eval f ρ' he ks hm
      exact ⟨c' + 1, by simp only [List.length_cons]; omega, Eval.ite_false (by simp [hk]) e⟩

/-- **The leaf, exact.** -/
theorem leafP_eval (srcOf dstOf : Key q → K) (κ : Key q) (hne : srcOf κ ≠ dstOf κ) (w : CReg)
    (p : List Bool) (rest : List Sym) (S : K → List Sym)
    (hS : S (srcOf κ) = p.map Sym.bit ++ Sym.sep :: rest) :
    ∃ c, c ≤ 3 * p.length + 3 + (allKeys q).length ∧
      Eval [] (leafP srcOf dstOf) ⟨(w, κ), S⟩
        ⟨((some Sym.sep, w.2), κ), Function.update (Function.update S (srcOf κ) rest) (dstOf κ)
          (p.reverse.map Sym.bit ++ Sym.sep :: S (dstOf κ))⟩ c := by
  have e := liftS_eval (q := q) (w, κ) (moveRecP_eval hne w.1 p rest S hS)
  exact cascade_eval _ [] e (allKeys q) (mem_allKeys κ)

end Move

/-! ## Volumes and list facts -/

theorem vol_cons (p : List Bool) (L : List (List Bool)) : vol (p :: L) = p.length + 1 + vol L := by
  simp [vol, arrSyms, blk, recSyms]
  omega

theorem vol_append (L L' : List (List Bool)) : vol (L ++ L') = vol L + vol L' := by
  simp [vol, arrSyms, blk]

theorem vol_eq_sum (L : List (List Bool)) : vol L = (L.map fun p => p.length + 1).sum := by
  induction L with
  | nil => rfl
  | cons p L ih => rw [vol_cons, ih, List.map_cons, List.sum_cons]

theorem vol_drop_succ (v : List (List Bool)) (t : ℕ) (ht : t < v.length) :
    vol (v.drop t) = (v.getD t []).length + 1 + vol (v.drop (t + 1)) := by
  rw [List.drop_eq_getElem_cons ht, vol_cons, List.getD_eq_getElem _ _ ht]

theorem arrSyms_drop_succ (v : List (List Bool)) (t : ℕ) (ht : t < v.length) :
    arrSyms (v.drop t) = (v.getD t []).map Sym.bit ++ Sym.sep :: arrSyms (v.drop (t + 1)) := by
  rw [List.getD_eq_getElem _ _ ht]
  conv_lhs => rw [List.drop_eq_getElem_cons ht]
  simp only [arrSyms, blk, recSyms, List.map_cons, List.flatten_cons, List.append_assoc,
    List.singleton_append]

theorem filter_range_succ (P : ℕ → Bool) (t : ℕ) :
    (List.range (t + 1)).filter P = (List.range t).filter P ++ (if P t then [t] else []) := by
  rw [List.range_succ, List.filter_append]
  cases h : P t <;> simp [List.filter, h]

theorem map_getD_range (v : List (List Bool)) :
    (List.range v.length).map (fun x => v.getD x []) = v := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- An injective self-map of `[0, N)` is onto. -/
theorem surj_of_inj_range {N : ℕ} {f : ℕ → ℕ} (hf : ∀ y < N, f y < N)
    (hinj : ∀ y y', y < N → y' < N → f y = f y' → y = y') : ∀ x < N, ∃ y < N, f y = x := by
  intro x hx
  obtain ⟨a, ha, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N)
    (t := Finset.range N) (fun a _ => f a) (fun a ha => Finset.mem_range.2 (hf a
      (Finset.mem_range.1 ha))) (fun a b ha hb h => hinj a b (Finset.mem_range.1 ha)
      (Finset.mem_range.1 hb) h) le_rfl x (Finset.mem_range.2 hx)
  exact ⟨a, Finset.mem_range.1 ha, e.symm⟩

/-- **The merge consistency lemma.** -/
theorem filter_eq_map_filter {α : Type} [DecidableEq α] (N : ℕ) (s1 s2 : ℕ → α) (f : ℕ → ℕ)
    (hf : ∀ y < N, f y < N) (hs : ∀ y < N, s1 (f y) = s2 y)
    (hmono : ∀ y y', y < N → y' < N → s2 y = s2 y' → y < y' → f y < f y') (s : α) :
    (List.range N).filter (fun x => s1 x = s) =
      ((List.range N).filter (fun y => s2 y = s)).map f := by
  have hinj : ∀ y y', y < N → y' < N → f y = f y' → y = y' := by
    intro y y' hy hy' h
    rcases Nat.lt_trichotomy y y' with hlt | heq | hgt
    · have e : s2 y = s2 y' := by rw [← hs y hy, ← hs y' hy', h]
      exact absurd h (Nat.ne_of_lt (hmono y y' hy hy' e hlt))
    · exact heq
    · have e : s2 y' = s2 y := by rw [← hs y hy, ← hs y' hy', h]
      exact absurd h.symm (Nat.ne_of_lt (hmono y' y hy' hy e hgt))
  have hsurj := surj_of_inj_range hf hinj
  have h1 : List.Pairwise (· < ·) ((List.range N).filter (fun x => s1 x = s)) :=
    List.pairwise_lt_range.filter _
  have h2 : List.Pairwise (· < ·) (((List.range N).filter (fun y => s2 y = s)).map f) := by
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range.filter _).imp_of_mem ?_
    intro a b ha hb hab
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at ha hb
    exact hmono a b ha.1 hb.1 (ha.2.trans hb.2.symm) hab
  refine h1.eq_of_mem_iff h2 ?_
  intro x
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨hx, hsx⟩
    obtain ⟨y, hy, rfl⟩ := hsurj x hx
    exact ⟨y, ⟨hy, (hs y hy).symm.trans hsx⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hsy⟩, rfl⟩
    exact ⟨hf y hy, (hs y hy).trans hsy⟩

/-- The output of a bijection of `[0, N)` has the volume of the input. -/
theorem vol_map_perm (v : List (List Bool)) (f : ℕ → ℕ) (hf : ∀ y < v.length, f y < v.length)
    (hinj : ∀ y y', y < v.length → y' < v.length → f y = f y' → y = y') :
    vol ((List.range v.length).map fun y => v.getD (f y) []) = vol v := by
  have hsurj := surj_of_inj_range hf hinj
  have hperm : List.Perm ((List.range v.length).map f) (List.range v.length) := by
    refine (List.perm_ext_iff_of_nodup ?_ (List.nodup_range)).2 ?_
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb h
      exact hinj a b (List.mem_range.1 ha) (List.mem_range.1 hb) h
    · intro x
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hf y hy
      · intro hx
        exact hsurj x hx
  have h := (hperm.map (fun x => (v.getD x []).length + 1)).sum_eq
  rw [vol_eq_sum, vol_eq_sum]
  conv_rhs => rw [← map_getD_range v]
  simpa [List.map_map, Function.comp_def] using h

/-! ## Stream contents and phase states -/

/-- Content of a stream holding the records `pay x`, `x ∈ xs`, pushed in the order of `xs`. -/
def streamC (xs : List ℕ) (pay : ℕ → List Bool) : List Sym :=
  (xs.reverse.map fun x => recRev (pay x)).flatten

theorem streamC_snoc (xs : List ℕ) (x : ℕ) (pay : ℕ → List Bool) :
    streamC (xs ++ [x]) pay = recRev (pay x) ++ streamC xs pay := by
  simp [streamC]

theorem streamC_map (xs : List ℕ) (f : ℕ → ℕ) (pay : ℕ → List Bool) :
    streamC (xs.map f) pay = streamC xs (fun y => pay (f y)) := by
  simp [streamC, List.map_reverse, List.map_map, Function.comp_def]

section Phases

variable {K : Type} [DecidableEq K] {q : ℕ}

/-- Stack facts of the phases: `strIdx` decodes the streams `STR s`. -/
structure PhaseOK (SRC DST : K) (STR : Key q → K) (strIdx : K → Option (Key q)) : Prop where
  idx_str : ∀ s, strIdx (STR s) = some s
  str_of_idx : ∀ loc s, strIdx loc = some s → loc = STR s
  idx_src : strIdx SRC = none
  idx_dst : strIdx DST = none
  src_dst : SRC ≠ DST

variable {SRC DST : K} {STR : Key q → K} {strIdx : K → Option (Key q)}

omit [DecidableEq K] in
theorem PhaseOK.str_ne_src (h : PhaseOK SRC DST STR strIdx) (s : Key q) : STR s ≠ SRC :=
  fun e => by have := h.idx_str s; rw [e, h.idx_src] at this; cases this

omit [DecidableEq K] in
theorem PhaseOK.str_ne_dst (h : PhaseOK SRC DST STR strIdx) (s : Key q) : STR s ≠ DST :=
  fun e => by have := h.idx_str s; rw [e, h.idx_dst] at this; cases this

/-- The stream part of a state: stream `s` carries `cont s`. -/
def streamPart (strIdx : K → Option (Key q)) (cont : Key q → List Sym) (loc : K) : List Sym :=
  match strIdx loc with
  | some s => cont s
  | none => []

/-- **Distribute state** after `t` records. -/
def st1 (B : K → List Sym) (SRC : K) (strIdx : K → Option (Key q)) (v : List (List Bool))
    (rest : List Sym) (s1 : ℕ → Key q) (t : ℕ) : K → List Sym := fun loc =>
  if loc = SRC then arrSyms (v.drop t) ++ rest
  else streamPart strIdx (fun s => streamC ((List.range t).filter (fun x => s1 x = s))
    (fun x => v.getD x [])) loc ++ B loc

/-- **Merge state** after `u` outputs (the outputs `N - u, …, N - 1` are on `DST`). -/
def st2 (B : K → List Sym) (DST : K) (strIdx : K → Option (Key q)) (N : ℕ)
    (pay : ℕ → List Bool) (s2 : ℕ → Key q) (u : ℕ) : K → List Sym := fun loc =>
  if loc = DST then arrSyms ((List.range' (N - u) u).map pay) ++ B DST
  else streamPart strIdx (fun s => streamC ((List.range (N - u)).filter (fun y => s2 y = s)) pay)
    loc ++ B loc

theorem st1_src (B : K → List Sym) (v : List (List Bool)) (rest : List Sym) (s1 : ℕ → Key q)
    (t : ℕ) : st1 B SRC strIdx v rest s1 t SRC = arrSyms (v.drop t) ++ rest := by
  simp [st1]

theorem st1_step (hP : PhaseOK SRC DST STR strIdx) (B : K → List Sym) (v : List (List Bool))
    (rest : List Sym) (s1 : ℕ → Key q) (t : ℕ) :
    Function.update (Function.update (st1 B SRC strIdx v rest s1 t) SRC
        (arrSyms (v.drop (t + 1)) ++ rest)) (STR (s1 t))
      ((v.getD t []).reverse.map Sym.bit ++ Sym.sep :: st1 B SRC strIdx v rest s1 t (STR (s1 t))) =
      st1 B SRC strIdx v rest s1 (t + 1) := by
  funext loc
  by_cases h1 : loc = STR (s1 t)
  · subst h1
    simp [st1, streamPart, Function.update_apply, hP.idx_str, hP.str_ne_src, filter_range_succ,
      streamC_snoc, recRev]
  · by_cases h2 : loc = SRC
    · subst h2
      simp [st1, Function.update_apply, h1]
    · simp only [st1, Function.update_apply, h1, h2, if_false]
      congr 1
      cases hl : strIdx loc with
      | none => simp [streamPart, hl]
      | some s =>
        have hs : s1 t ≠ s := fun e => h1 (by rw [hP.str_of_idx loc s hl, e])
        simp [streamPart, hl, filter_range_succ, hs]

theorem st2_stream (hP : PhaseOK SRC DST STR strIdx) (B : K → List Sym) (N : ℕ)
    (pay : ℕ → List Bool) (s2 : ℕ → Key q) (u : ℕ) (hu : u < N) :
    st2 B DST strIdx N pay s2 u (STR (s2 (N - 1 - u))) =
      (pay (N - 1 - u)).reverse.map Sym.bit ++ Sym.sep ::
        (streamC ((List.range (N - 1 - u)).filter (fun y => s2 y = s2 (N - 1 - u))) pay ++
          B (STR (s2 (N - 1 - u)))) := by
  have hNu : N - u = (N - 1 - u) + 1 := by omega
  simp only [st2, hP.str_ne_dst, if_false, streamPart, hP.idx_str]
  rw [hNu, filter_range_succ]
  simp [streamC_snoc, recRev]

theorem st2_step (hP : PhaseOK SRC DST STR strIdx) (B : K → List Sym) (N : ℕ)
    (pay : ℕ → List Bool) (s2 : ℕ → Key q) (u : ℕ) (hu : u < N) :
    Function.update (Function.update (st2 B DST strIdx N pay s2 u) (STR (s2 (N - 1 - u)))
        (streamC ((List.range (N - 1 - u)).filter (fun y => s2 y = s2 (N - 1 - u))) pay ++
          B (STR (s2 (N - 1 - u))))) DST
      ((pay (N - 1 - u)).reverse.reverse.map Sym.bit ++ Sym.sep ::
        st2 B DST strIdx N pay s2 u DST) =
      st2 B DST strIdx N pay s2 (u + 1) := by
  have hNu : N - u = (N - 1 - u) + 1 := by omega
  have hNu' : N - (u + 1) = N - 1 - u := by omega
  funext loc
  by_cases h1 : loc = DST
  · subst h1
    simp only [st2, Function.update_apply, if_true, List.reverse_reverse]
    rw [hNu', hNu, List.range'_succ]
    simp [arrSyms, blk, recSyms]
  · by_cases h2 : loc = STR (s2 (N - 1 - u))
    · subst h2
      simp only [Function.update_apply, h1, if_true, if_false, st2, hP.str_ne_dst, streamPart,
        hP.idx_str, hNu']
    · simp only [st2, Function.update_apply, h1, h2, if_false]
      congr 1
      cases hl : strIdx loc with
      | none => simp [streamPart, hl]
      | some s =>
        have hs : s2 (N - 1 - u) ≠ s := fun e => h2 (by rw [hP.str_of_idx loc s hl, e])
        simp only [streamPart, hl]
        rw [hNu, filter_range_succ, hNu']
        simp [hs]

theorem st1_zero (B : K → List Sym) (v : List (List Bool)) (rest : List Sym) (s1 : ℕ → Key q)
    (hB : B SRC = arrSyms v ++ rest) : st1 B SRC strIdx v rest s1 0 = B := by
  funext loc
  by_cases h : loc = SRC
  · subst h
    simp [st1, hB]
  · simp only [st1, h, if_false, List.range_zero, List.filter_nil]
    cases hl : strIdx loc <;> simp [streamPart, hl, streamC]

theorem st1_last (hP : PhaseOK SRC DST STR strIdx) (B : K → List Sym) (v : List (List Bool))
    (rest : List Sym) (s1 s2 : ℕ → Key q) (f : ℕ → ℕ)
    (hL : ∀ s, (List.range v.length).filter (fun x => s1 x = s) =
      ((List.range v.length).filter (fun y => s2 y = s)).map f) :
    st1 B SRC strIdx v rest s1 v.length =
      st2 (Function.update B SRC rest) DST strIdx v.length (fun y => v.getD (f y) []) s2 0 := by
  funext loc
  by_cases h1 : loc = DST
  · subst h1
    simp [st1, st2, hP.src_dst.symm, streamPart, hP.idx_dst, arrSyms, blk]
  · by_cases h2 : loc = SRC
    · subst h2
      simp [st1, st2, h1, streamPart, hP.idx_src, arrSyms, blk]
    · simp only [st1, st2, h1, h2, if_false, Function.update_apply, Nat.sub_zero]
      congr 1
      cases hl : strIdx loc with
      | none => simp [streamPart, hl]
      | some s => simp only [streamPart, hl, hL s, streamC_map]

theorem st2_last (B : K → List Sym) (N : ℕ) (pay : ℕ → List Bool) (s2 : ℕ → Key q) :
    st2 B DST strIdx N pay s2 N =
      Function.update B DST (arrSyms ((List.range N).map pay) ++ B DST) := by
  funext loc
  by_cases h1 : loc = DST
  · subst h1
    simp [st2, List.range_eq_range']
  · simp only [st2, h1, if_false, Function.update_apply, Nat.sub_self, List.range_zero,
      List.filter_nil]
    cases hl : strIdx loc <;> simp [streamPart, hl, streamC]

end Phases

end SubNLogN.Machine.K1Digit
