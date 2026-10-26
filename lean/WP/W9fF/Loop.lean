import WP.W9fF.MacrosH
import WP.W9f.Spec

/-!
# WP.W9fF.Loop — "while the top of `src` is an entry" (generic in the host stacks)

* `isEnt r`: the register holds `pos` or `neg` (the first symbol of an entry).
* `whileEnt I src body = peek src; loop (isEnt reg) (body; peek src)`.
* `whileEnt_triple`: for an invariant `P n` on the stacks (`n` = remaining iterations) with
  `isEnt (top src) = decide (0 < n)` and a body triple `P (n+1) → P n` of cost `Bc`, the loop goes
  from `P N` to `P 0` within `N·(Bc + 2) + 2` steps.
* `triple_of_runsS`: exact-stacks body lemmas (`RunsS`) give the body triple.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL

/-- The register holds the first symbol of an entry. -/
def isEnt : Option Sym → Bool
  | some .pos => true
  | some .neg => true
  | _ => false

theorem isEnt_entry (y : ℤ × ℤ) (l : List Sym) : isEnt (entrySyms y ++ l).head? = true := by
  simp only [entrySyms, intSyms, sgnSym, List.cons_append, List.head?_cons]
  split_ifs <;> rfl

theorem isEnt_blkE_cons (y : ℤ × ℤ) (ys : List (ℤ × ℤ)) (l : List Sym) :
    isEnt (blkE (y :: ys) ++ l).head? = true := by
  have e : blkE (y :: ys) ++ l = entrySyms y ++ (blkE ys ++ l) := by simp [blkE, blk]
  rw [e]
  exact isEnt_entry y _

theorem isEnt_notEntry {r : List Sym} (h : WP.W9f.NotEntry r) : isEnt r.head? = false := by
  cases hr : r.head? with
  | none => rfl
  | some s =>
    obtain ⟨h1, h2⟩ := h s hr
    cases s <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem isEnt_blkE (ys : List (ℤ × ℤ)) (l : List Sym) (h : WP.W9f.NotEntry l) :
    isEnt (blkE ys ++ l).head? = decide (0 < ys.length) := by
  cases ys with
  | nil =>
    simp only [blkE, blk, List.map_nil, List.flatten_nil, List.nil_append, List.length_nil,
      Nat.lt_irrefl, decide_false]
    exact isEnt_notEntry h
  | cons y ys =>
    rw [isEnt_blkE_cons]
    simp

section Loop

variable {K : Type} [DecidableEq K] {O : Type} [DecidableEq O] (I : O → OpImpl)

/-- `peek src; while top(src) is an entry do (body; peek src)`. -/
def whileEnt (src : K) (body : Prog K (fun _ => Sym) (GReg I)) : Prog K (fun _ => Sym) (GReg I) :=
  .seq (hM I (peekR src))
    (.loop (fun v => isEnt ((macroLens I).get v)) (.seq body (hM I (peekR src))))

theorem peek_triple (src : K) (P : (K → List Sym) → Prop) :
    Triple [] (fun s => P s.stk) (hM I (peekR src))
      (fun s => P s.stk ∧ (macroLens I).get s.var = (s.stk src).head?) 1 := by
  rintro ⟨w, S⟩ hs
  refine ⟨⟨(macroLens I).set w (S src).head?, S⟩, 1, ?_, ⟨hs, ?_⟩, le_rfl⟩
  · have e : Eval [] (peekR src) ⟨(macroLens I).get w, S⟩ ⟨(S src).head?, S⟩ 1 :=
      (Eval.peek (Γ := fun _ => Sym) [] src (fun _ o => o) _ S).of_eq rfl rfl
    exact Eval.liftRegs (macroLens I) e w rfl
  · exact (macroLens I).get_set w _

/-- **The entry loop.** -/
theorem whileEnt_triple (src : K) (body : Prog K (fun _ => Sym) (GReg I))
    (P : ℕ → (K → List Sym) → Prop) (Bc : ℕ)
    (hent : ∀ n S, P n S → isEnt (S src).head? = decide (0 < n))
    (hbody : ∀ n, Triple [] (fun s => P (n + 1) s.stk) body (fun s => P n s.stk) Bc) (N : ℕ) :
    Triple [] (fun s => P N s.stk) (whileEnt I src body) (fun s => P 0 s.stk)
      (N * (Bc + 2) + 2) := by
  have hloop := Triple.loop (ρ := []) (c := fun v => isEnt ((macroLens I).get v))
    (I := fun n s => P n s.stk ∧ (macroLens I).get s.var = (s.stk src).head?)
    (B := fun _ => Bc + 1) (p := .seq body (hM I (peekR src)))
    (fun n => Triple.seq ((hbody n).pre (fun s hs => hs.1)) (peek_triple I src (P n)))
    (fun n s hs => by
      show isEnt ((macroLens I).get s.var) = true
      rw [hs.2, hent (n + 1) s.stk hs.1]
      simp)
    (fun s hs => by
      show isEnt ((macroLens I).get s.var) = false
      rw [hs.2, hent 0 s.stk hs.1]
      simp) N
  have h := Triple.seq (peek_triple I src (P N)) hloop
  refine (Triple.post h (fun s hs => hs.1)).cost_mono ?_
  rw [loopCost_const]
  have h2 : N * (Bc + 1 + 1) = N * (Bc + 2) := by ring
  omega

/-- Exact-stacks lemmas give a triple between stack predicates. -/
theorem triple_of_runsS {body : Prog K (fun _ => Sym) (GReg I)} {P Q : (K → List Sym) → Prop}
    {Bc : ℕ} (h : ∀ S, P S → ∃ S', Q S' ∧ RunsS body S S' Bc) :
    Triple [] (fun s => P s.stk) body (fun s => Q s.stk) Bc := by
  intro s hs
  obtain ⟨S', hQ, hr⟩ := h s.stk hs
  obtain ⟨s', t, e, hs', ht⟩ := hr s rfl
  have hs'' : s'.stk = S' := hs'
  exact ⟨s', t, e, show Q s'.stk by rw [hs'']; exact hQ, ht⟩

theorem whileEnt_closed (src : K) (body : Prog K (fun _ => Sym) (GReg I)) (hb : body.Closed) :
    (whileEnt I src body).Closed :=
  ⟨hM_closed I _ trivial, ⟨hb, hM_closed I _ trivial⟩⟩

end Loop

#assert_std_axioms isEnt_entry isEnt_blkE_cons isEnt_notEntry isEnt_blkE peek_triple
  whileEnt_triple triple_of_runsS whileEnt_closed

end WP.W9fF
