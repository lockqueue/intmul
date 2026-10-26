import WP.W9c.BlockPackBody

/-!
# WP.W9c.BlockPackLoop — the main loop over the numbers of the block

`mainLoopP`: `test; while cond do (stepP; test)`, where `test` peeks the counter and the number
list and `cond` holds iff the counter is nonzero and a number (a sign symbol) follows. On
`stMain … i` the condition is `i < min W |v|` (`EndOK rx` stops it at the list end), so the loop
runs exactly `(v.take W).length` times (`ht_mainLoop`, via `HT.loopFwd`).
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- A sign symbol (the start of a number). -/
def isSgn (x : Sym) : Bool := decide (x = Sym.pos) || decide (x = Sym.neg)

section

variable (K : Kit)

/-- Loop test: peek the counter and the number list. -/
def testP : BProg 6 8 K.Reg := (peekR K.lS1 kCW).seq (peekR K.lS2 kX)

/-- Continue while the counter is nonzero and a number follows. -/
def condP (v : K.Reg) : Bool := optIsBit (K.lS1.get v) && optP isSgn (K.lS2.get v)

/-- The main loop over the numbers of the block. -/
def mainLoopP : BProg 6 8 K.Reg := (testP K).seq (.loop (condP K) ((stepP K).seq (testP K)))

theorem mainLoopP_closed : (mainLoopP K).Closed :=
  ⟨⟨trivial, trivial⟩, stepP_closed K, trivial, trivial⟩

end

theorem optIsBit_natSyms_head (m : ℕ) (l : List Sym) (hl : TermOK l) :
    optIsBit (natSyms m ++ l).head? = decide (0 < m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [natSyms, encodeNat_zero, optIsBit_head?_of_termOK hl]
  · cases h : encodeNat m with
    | nil => exact absurd ((encodeNat_eq_nil_iff m).mp h) (by omega)
    | cons b bs => simp [natSyms, h, optIsBit, hm]

theorem optP_isSgn_listSyms_head (vs : List ℤ) (rx : List Sym) (hrx : EndOK rx) :
    optP isSgn (listSyms vs ++ rx).head? = decide (vs ≠ []) := by
  cases vs with
  | nil =>
    simp only [listSyms_nil, List.nil_append]
    cases h : rx.head? with
    | none => rfl
    | some x =>
      obtain ⟨h1, h2⟩ := hrx x h
      simp [optP, isSgn, h1, h2]
  | cons e vs =>
    rw [listSyms_cons]
    unfold intSyms sgnSym
    split_ifs <;> simp [optP, isSgn]

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

theorem tr_test (r : HS) :
    Triple ρ (fun s => s.stk = r.f) (testP K)
      (fun s => s.stk = r.f ∧
        condP K s.var = (optIsBit (r.f kCW).head? && optP isSgn (r.f kX).head?)) 2 := by
  rintro ⟨v, S⟩ hS
  change S = r.f at hS
  subst hS
  exact ⟨_, 2, Eval.seq (Eval.peek _ kCW _ v _) (Eval.peek _ kX _ _ _), ⟨rfl, rfl⟩, le_rfl⟩

/-- **The main loop.** -/
theorem ht_mainLoop (hK : K.OK C) (r0 : HS) (k p_in q W B : ℕ) (v : List ℤ)
    (rx rk ra rb : List Sym) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ B) (hk1 : 1 ≤ k)
    (hrx : EndOK rx) (hrk : TermOK rk) (hra : TermOK ra) (hrb : TermOK rb)
    (hk : r0.k = natSyms k ++ rk) (hp : r0.p = natSyms p_in ++ ra)
    (hq : r0.q = natSyms q ++ rb) :
    HT ρ (stMain r0 k p_in q W v rx 0).f (mainLoopP K)
      (stMain r0 k p_in q W v rx (v.take W).length).f
      (2 + (((List.range (v.take W).length).map fun i =>
        40 * (C * (2 * (B + k + p_in + q + 2))) + 40 + C * (zerosLead (encodeNat (W - i)) + 1) +
          2 + 1).sum + 1)) := by
  have hn : (v.take W).length = min W v.length := List.length_take
  refine HT.loopFwd (testP K) (stepP K) (condP K) (fun i => (stMain r0 k p_in q W v rx i).f) _ 2
    _ ?_ ?_
  · intro i _
    refine Triple.post (tr_test (stMain r0 k p_in q W v rx i)) (fun s hs => ⟨hs.1, ?_⟩)
    rw [hs.2]
    show (optIsBit (natSyms (W - i) ++ Sym.mark :: r0.cw).head? &&
      optP isSgn (listSyms (v.drop i) ++ rx).head?) = decide (i < (v.take W).length)
    rw [optIsBit_natSyms_head _ _ (termOK_mark _), optP_isSgn_listSyms_head _ _ hrx, hn]
    have e1 : decide (0 < W - i) = decide (i < W) := by
      by_cases h : i < W <;> simp [h]
    have e2 : decide (v.drop i ≠ []) = decide (i < v.length) := by
      by_cases h : i < v.length <;> simp [h, List.drop_eq_nil_iff]
    rw [e1, e2]
    by_cases h1 : i < W <;> by_cases h2 : i < v.length <;> simp [h1, h2]
  · intro i hi
    rw [hn] at hi
    exact ht_step hK r0 k p_in q W B v rx rk ra rb hvB hk1 hrk hra hrb hk hp hq i
      (lt_of_lt_of_le hi (min_le_left _ _)) (lt_of_lt_of_le hi (min_le_right _ _))

#assert_std_axioms mainLoopP_closed optIsBit_natSyms_head optP_isSgn_listSyms_head tr_test
  ht_mainLoop

end WP.W9c.BlockPack
