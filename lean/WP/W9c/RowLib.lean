import WP.W9c.RowMacros2

/-!
# WP.W9c.RowLib — helpers for the row-level data-movement kernels (`Iface2`)

* `whileP k c body = peekR k ; loop c (body ; peekR k)`: a loop driven by the top symbol of `k`,
  with a `Runs` rule over a fixed list (`whileP_runs`).
* `mvNumR src dst = moveBits src dst ; pushR dst`: move a bit block (reversing it) and then the
  non-bit symbol under it (`rs_mvNumR`).
* `listSyms`, `blkE` facts.

Everything is in namespace `WP.W9c.RowLib`. Generic `Runs` combinators and macro lemmas are in
`WP.W9c.RowMacros` / `WP.W9c.RowMacros2` (self-contained copies of the W9b ones).
-/

namespace WP.W9c.RowLib

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- The register holds a sign symbol (the start of a number). -/
def isSgnR (r : Option Sym) : Bool := decide (r = some Sym.pos) || decide (r = some Sym.neg)

/-- The register holds `sep`. -/
def isSepR (r : Option Sym) : Bool := decide (r = some Sym.sep)

section Gen

variable {K : Type} [DecidableEq K]

/-- Loop driven by the top of `k`. -/
def whileP (k : K) (c : Option Sym → Bool) (body : SProg K) : SProg K :=
  .seq (peekR k) (.loop c (.seq body (peekR k)))

/-- Move a bit block (reversed) and then the non-bit symbol below it. -/
def mvNumR (src dst : K) : SProg K := .seq (moveBits src dst) (pushR dst)

theorem rs_peekR (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun r => r = (S k).head?) 1 :=
  Runs.of_eval fun v => ⟨(S k).head?, 1, eval_peek' [] k (fun _ o => o) v S _ rfl, rfl, le_rfl⟩

theorem whileP_loop (k : K) (c : Option Sym → Bool) (body : SProg K) {α : Type}
    (F : List α → List α → K → List Sym) (L : List α) (B : α → ℕ)
    (hgo : ∀ done a todo, done ++ a :: todo = L → c (F done (a :: todo) k).head? = true)
    (hstop : c (F L [] k).head? = false)
    (hbody : ∀ done a todo, done ++ a :: todo = L →
      Runs body (F done (a :: todo)) (F (done ++ [a]) todo) (fun _ => True) (B a)) :
    ∀ (todo done : List α) (s : TMFw.St K (fun _ => Sym) (Option Sym)), done ++ todo = L →
      s.stk = F done todo → s.var = (F done todo k).head? →
      ∃ s' t, Eval [] (.loop c (.seq body (peekR k))) s s' t ∧ s'.stk = F L [] ∧
        t ≤ (todo.map B).sum + 2 * todo.length + 1
  | [], done, s, hL, hs, hv => by
    rw [List.append_nil] at hL
    subst hL
    refine ⟨s, 1, Eval.loop_false ?_, hs, by simp⟩
    rw [hv, ← hs]
    rw [hs]
    exact hstop
  | a :: todo, done, s, hL, hs, hv => by
    obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ :=
      runs_seq (hbody done a todo hL) (rs_peekR k _) s hs
    obtain ⟨s2, t2, e2, hs2, ht2⟩ :=
      whileP_loop k c body F L B hgo hstop hbody todo (done ++ [a]) s1
        (by rw [List.append_assoc, List.singleton_append]; exact hL) hs1 hv1
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true ?_ e1 e2, hs2, ?_⟩
    · rw [hv]
      exact hgo done a todo hL
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- **Top-driven loop over a fixed list `L`, `Runs` form.** -/
theorem whileP_runs (k : K) (c : Option Sym → Bool) (body : SProg K) {α : Type}
    (F : List α → List α → K → List Sym) (L : List α) (B : α → ℕ)
    (hgo : ∀ done a todo, done ++ a :: todo = L → c (F done (a :: todo) k).head? = true)
    (hstop : c (F L [] k).head? = false)
    (hbody : ∀ done a todo, done ++ a :: todo = L →
      Runs body (F done (a :: todo)) (F (done ++ [a]) todo) (fun _ => True) (B a)) :
    Runs (whileP k c body) (F [] L) (F L []) (fun _ => True)
      ((L.map B).sum + 2 * L.length + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := rs_peekR k (F [] L) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := whileP_loop k c body F L B hgo hstop hbody L [] s1 rfl hs1 hv1
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

theorem rs_mvNumR {src dst : K} (hne : src ≠ dst) (es : List Bool) (x : Sym)
    (hx : x.isBit = false) (tl : List Sym) (S : K → List Sym)
    (hS : S src = es.map Sym.bit ++ x :: tl) :
    Runs (mvNumR src dst) S
      (Function.update (Function.update S src tl) dst (x :: (es.reverse.map Sym.bit ++ S dst)))
      (fun _ => True) (3 * es.length + 3) := by
  refine Runs.of_eval fun v => ⟨some x, 3 * es.length + 3, ?_, trivial, le_rfl⟩
  have e1 := moveBits_eval hne [] v es (x :: tl) S (TermOK.cons hx _) hS
  have e2 : Eval [] (pushR dst) ⟨some x, Function.update (Function.update S src tl) dst
      (es.reverse.map Sym.bit ++ S dst)⟩ ⟨some x, Function.update (Function.update
        (Function.update S src tl) dst (es.reverse.map Sym.bit ++ S dst)) dst
        (x :: Function.update (Function.update S src tl) dst (es.reverse.map Sym.bit ++ S dst)
          dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  rw [Function.update_self, Function.update_idem]

omit [DecidableEq K] in
theorem closed_whileP (k : K) (c : Option Sym → Bool) {body : SProg K} (h : body.Closed) :
    (whileP k c body).Closed :=
  ⟨by simp [Prog.FreeBelow, peekR], h, by simp [Prog.FreeBelow, peekR]⟩

omit [DecidableEq K] in
theorem closed_mvNumR (src dst : K) : (mvNumR src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, mvNumR, moveBits, moveBitsBody, popR, pushR]

end Gen

/-! ## Encodings -/

theorem listSyms_nil : listSyms [] = [] := rfl

theorem listSyms_cons (v : ℤ) (vs : List ℤ) :
    listSyms (v :: vs) = intSyms v ++ Sym.sep :: listSyms vs := by
  simp [listSyms]

theorem listSyms_append (us vs : List ℤ) : listSyms (us ++ vs) = listSyms us ++ listSyms vs := by
  simp [listSyms]

theorem sgnSym_isBit (z : ℤ) : (sgnSym z).isBit = false := by
  unfold sgnSym
  split <;> rfl

theorem isSgnR_sgnSym (z : ℤ) : isSgnR (some (sgnSym z)) = true := by
  unfold sgnSym isSgnR
  split <;> simp

theorem isSgnR_of_endOK {rest : List Sym} (h : EndOK rest) : isSgnR rest.head? = false := by
  cases hr : rest.head? with
  | none => rfl
  | some x =>
    obtain ⟨h1, h2⟩ := h x hr
    simp [isSgnR, h1, h2]

theorem natSyms_reverse (n : ℕ) : (natSyms n).reverse = (encodeNat n).reverse.map Sym.bit := by
  simp [natSyms, List.map_reverse]

theorem reverse_blkE (v : List (ℤ × ℤ)) :
    (blkE v).reverse = v.reverse.flatMap fun e => (entrySyms e).reverse := by
  induction v with
  | nil => simp [blkE, blk]
  | cons e v ih => simp [blkE_cons, ih, List.reverse_append]

theorem four_le_length_blkE : ∀ v : List (ℤ × ℤ), 4 * v.length ≤ (blkE v).length
  | [] => by simp
  | e :: v => by
    rw [blkE_cons, List.length_append, length_entrySyms, List.length_cons]
    have := four_le_length_blkE v
    omega

#assert_std_axioms rs_peekR whileP_loop whileP_runs rs_mvNumR closed_whileP closed_mvNumR
  listSyms_nil listSyms_cons listSyms_append sgnSym_isBit isSgnR_sgnSym isSgnR_of_endOK
  natSyms_reverse reverse_blkE four_le_length_blkE

end WP.W9c.RowLib
