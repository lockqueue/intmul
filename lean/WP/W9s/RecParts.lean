import WP.W9s.Rec

/-!
# WP.W9s.RecParts — specifications of the pieces of the recursive body
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

section Generic

variable {a b : ℕ} {σ : Type}

theorem HT.peekIte_true (lS : Lens σ (Option Sym)) (k : Loc a b) (f : Option Sym → Bool)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (B B' : Loc a b → List Sym) {T₁ : ℕ}
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (h : f (B k).head? = true)
    (hp : HT ρ B p B' T₁) :
    HT ρ B (.seq (peekL lS k) (.ite (fun v => f (lS.get v)) p q)) B' (T₁ + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, hq, ht⟩ := hp ⟨lS.set v (S k).head?, S⟩ rfl
  refine ⟨s', 1 + (t + 1), Eval.seq (Eval.peek ρ k _ v S) (Eval.ite_true ?_ e), hq, by omega⟩
  show f (lS.get (lS.set v (S k).head?)) = true
  rw [lS.get_set]
  exact h

theorem HT.peekIte_false (lS : Lens σ (Option Sym)) (k : Loc a b) (f : Option Sym → Bool)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (B B' : Loc a b → List Sym) {T₂ : ℕ}
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (h : f (B k).head? = false)
    (hq : HT ρ B q B' T₂) :
    HT ρ B (.seq (peekL lS k) (.ite (fun v => f (lS.get v)) p q)) B' (T₂ + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, hq', ht⟩ := hq ⟨lS.set v (S k).head?, S⟩ rfl
  refine ⟨s', 1 + (t + 1), Eval.seq (Eval.peek ρ k _ v S) (Eval.ite_false ?_ e), hq', by omega⟩
  show f (lS.get (lS.set v (S k).head?)) = false
  rw [lS.get_set]
  exact h

end Generic

theorem LoopHT.deal (K : Kit) (rA : List Sym) (ρ : List (MProg K)) :
    ∀ (l : List (List (ℤ × ℤ))) (B : Host → List Sym), l.length % 2 = 0 →
      B sA = blkR l ++ symBlk :: rA →
      LoopHT ρ (lS K) sA (notS symBlk) (.seq (mvRow (lS K) sA sE) (mvRow (lS K) sA sO)) B
        (Function.update (Function.update (Function.update B sA (symBlk :: rA)) sE
          ((blkR (evensL l)).reverse ++ B sE)) sO ((blkR (oddsL l)).reverse ++ B sO))
        (3 * (blkR l).length + l.length + 1)
  | [], B, _, hA => by
    have hA' : B sA = symBlk :: rA := by simpa [blkR] using hA
    refine Triple.post ((LoopHT.stop (by simp [notS, hA'])).mono (by simp [blkR])) (fun s hs => ?_)
    rw [hs]
    funext k
    by_cases h1 : k = sA
    · subst h1
      simp [hA']
    by_cases h2 : k = sE
    · subst h2
      simp [evensL, blkR]
    by_cases h3 : k = sO
    · subst h3
      simp [oddsL, blkR]
    simp [h1, h2, h3]
  | [_], _, h, _ => by simp at h
  | x :: y :: l, B, h, hA => by
    have h' : l.length % 2 = 0 := by simp at h; omega
    have hstep := LoopHT.step (by rw [hA, blkR_cons, List.append_assoc]; exact head_rowE_ne x _)
      ((HT.mvRow (lS K) (src := sA) (dst := sE) (by decide) x (blkR (y :: l) ++ symBlk :: rA) B
          (by rw [hA, blkR_cons, List.append_assoc]) ρ).seq
        (HT.mvRow (lS K) (src := sA) (dst := sO) (by decide) y (blkR l ++ symBlk :: rA) _
          (by simp [blkR_cons]) ρ))
      (LoopHT.deal K rA ρ l _ h' (by simp))
    refine Triple.post (hstep.mono ?_) (fun s hs => ?_)
    · simp only [blkR_cons, List.length_append, List.length_cons, rowE]
      omega
    · rw [hs]
      funext k
      by_cases h1 : k = sA
      · subst h1
        simp
      by_cases h2 : k = sE
      · subst h2
        simp [evensL_cons_cons, blkR_cons]
      by_cases h3 : k = sO
      · subst h3
        simp [oddsL_cons_cons, blkR_cons]
      simp [h1, h2, h3]

theorem HT.dealLoop (K : Kit) (rA : List Sym) (l : List (List (ℤ × ℤ))) (B : Host → List Sym)
    (h : l.length % 2 = 0) (hA : B sA = blkR l ++ symBlk :: rA) (ρ : List (MProg K)) :
    HT ρ B (dealLoop K)
      (Function.update (Function.update (Function.update B sA (symBlk :: rA)) sE
        ((blkR (evensL l)).reverse ++ B sE)) sO ((blkR (oddsL l)).reverse ++ B sO))
      (3 * (blkR l).length + l.length + 2) :=
  HT.whileTop (LoopHT.deal K rA ρ l B h hA)

theorem HT.dsDouble (K : Kit) (B : Host → List Sym) (Δ : ℕ) (rDS : List Sym)
    (hDS : B sDS = units Δ ++ symG :: rDS) (ρ : List (MProg K)) :
    HT ρ B (dsDouble K)
      (Function.update B sDS (units (2 * Δ) ++ symG :: (units Δ ++ symG :: rDS))) (18 * Δ + 11) := by
  have chain :=
    (HT.pushS sT symG B ρ).seq <|
    (HT.pushS sT2 symG _ ρ).seq <|
    (HT.uMove (lS K) (src := sDS) (dst := sT) (by decide) Δ (symG :: rDS) (by simp [symG, symU])
      _ (by simp [hDS]) ρ).seq <|
    (HT.uDup (lS K) (src := sT) (dst := sDS) (dst2 := sT2) (by decide) (by decide) (by decide) Δ
      (symG :: B sT) (by simp [symG, symU]) _ (by simp) ρ).seq <|
    (HT.popS sT _ symG (B sT) (by simp) ρ).seq <|
    (HT.pushS sDS symG _ ρ).seq <|
    (HT.uMove (lS K) (src := sT2) (dst := sDS) (by decide) (2 * Δ) (symG :: B sT2)
      (by simp [symG, symU]) _ (by simp) ρ).seq <|
    HT.popS sT2 _ symG (B sT2) (by simp) ρ
  refine chain.of_eq ?_ (by omega)
  funext k
  by_cases h1 : k = sDS
  · subst h1
    simp
  by_cases h2 : k = sT
  · subst h2
    simp
  by_cases h3 : k = sT2
  · subst h3
    simp
  simp [h1, h2, h3]

theorem HT.dsPop (K : Kit) (B : Host → List Sym) (n : ℕ) (rDS : List Sym)
    (hDS : B sDS = units n ++ symG :: rDS) (ρ : List (MProg K)) :
    HT ρ B (dsPop K) (Function.update B sDS rDS) (3 * n + 3) := by
  have h := HT.dropTo (lS K) sDS symG (units n) rDS B
    (by simp [units, symG, symU]) hDS ρ
  rw [length_units] at h
  exact h

#assert_std_axioms HT.peekIte_true HT.peekIte_false LoopHT.deal HT.dealLoop HT.dsDouble HT.dsPop

end WP.W9s
