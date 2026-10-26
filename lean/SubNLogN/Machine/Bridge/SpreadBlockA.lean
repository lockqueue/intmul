/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadLayout
import SubNLogN.Machine.Bridge.SpreadMath3
import SubNLogN.Machine.Bridge.SpreadPrim2

/-!
# K5 spreading: AR-level block step, part A (`Bridge/SpreadBlockA.lean`)

* `eval_loop_bounded`, `walk_eval_bounded`: AR loops with per-iteration cost bounds;
* `SlotSpecOf` (the specification part of `SlotPassStmt`) and `slot_apply` (its use with an
  explicit final state);
* `BF`, `bst`: the stacks of the block step as fields over a base state, with update lemmas;
* `slot_re_step`, `slot_im_step`: one slot pass on the real / imaginary partial products.

Everything is proved; the slot pass enters through `SlotSpecOf`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-! ## Bounded loops -/

theorem eval_loop_bounded {K : Type} [DecidableEq K] {c : AReg → Bool} {body : AProg K} (b : ℕ) :
    ∀ (n : ℕ) (S : ℕ → K → List Sym) (v : AReg), c v = decide (0 < n) →
      (∀ j < n, ∀ u : AReg, ∃ w t, Eval [] body ⟨u, S j⟩ ⟨w, S (j + 1)⟩ t ∧ t ≤ b ∧
        c w = decide (j + 1 < n)) →
      ∃ w t, Eval [] (.loop c body) ⟨v, S 0⟩ ⟨w, S n⟩ t ∧ t ≤ n * (b + 1) + 1
  | 0, S, v, hv, _ => ⟨v, 1, Eval.loop_false (by simpa using hv), by simp⟩
  | n + 1, S, v, hv, hb => by
    obtain ⟨w, t, e, ht, hw⟩ := hb 0 (by omega) v
    obtain ⟨w', t', e', ht'⟩ := eval_loop_bounded b n (fun j => S (j + 1)) w
      (by simpa using hw) (fun j hj u => by
        obtain ⟨w2, t2, e2, h2, hc2⟩ := hb (j + 1) (by omega) u
        exact ⟨w2, t2, e2, h2, by simpa using hc2⟩)
    refine ⟨w', t + t' + 1, Eval.loop_true (by simpa using hv) e e', ?_⟩
    have h1 : (n + 1) * (b + 1) = n * (b + 1) + (b + 1) := by ring
    omega

theorem walk_eval_bounded {K : Type} [DecidableEq K] {R X : K} (hRX : R ≠ X) (body : AProg K)
    (n : ℕ) (D : List Sym) (hD : D.head? ≠ some .mark)
    (S : ℕ → K → List Sym) (hSR : ∀ j ≤ n, S j R = List.replicate (n - j) .mark ++ D)
    (b : ℕ)
    (hb : ∀ j < n, ∀ u : AReg, ∃ w t, Eval [] body ⟨u, Function.update (Function.update (S j)
      R (List.replicate (n - j - 1) .mark ++ D)) X (.mark :: S j X)⟩ ⟨w, S (j + 1)⟩ t ∧ t ≤ b)
    (v0 : AReg) :
    ∃ v' t, Eval [] (walk R X body) ⟨v0, S 0⟩ ⟨v', S n⟩ t ∧ t ≤ n * (b + 4) + 2 := by
  have e0 := eval_peekR R v0 (S 0)
  obtain ⟨w, t, e, ht⟩ := eval_loop_bounded (c := fun v => isMarkO v.r)
    (body := walkStep R X body) (b + 3) n S { v0 with r := (S 0 R).head? }
    (by
      show isMarkO (S 0 R).head? = decide (0 < n)
      rw [hSR 0 (Nat.zero_le _), Nat.sub_zero]
      rcases n with _ | n
      · simp only [List.replicate_zero, List.nil_append, lt_irrefl, decide_false]
        cases hDh : D.head? with
        | none => rfl
        | some y => cases y <;> simp_all [isMarkO]
      · simp [List.replicate_succ, isMarkO])
    (fun j hj u => by
      obtain ⟨w2, t2, e2, h2⟩ := hb j hj u
      have hR : S j R = List.replicate (n - j - 1 + 1) .mark ++ D := by
        rw [hSR j hj.le]; congr 2; omega
      have hS2R : S (j + 1) R = List.replicate (n - j - 1) .mark ++ D := by
        rw [hSR (j + 1) hj]; congr 2
      refine ⟨_, t2 + 3, walkStep_eval hRX body (n - j - 1) D u (S j) hR e2 hS2R, by omega, ?_⟩
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · show isMarkO (List.replicate (n - j - 1) Sym.mark ++ D).head? = decide (j + 1 < n)
        rw [show n - j - 1 = (n - j - 2) + 1 by omega, List.replicate_succ]
        simp [isMarkO, h]
      · show isMarkO (List.replicate (n - j - 1) Sym.mark ++ D).head? = decide (j + 1 < n)
        rw [show n - j - 1 = 0 by omega, decide_eq_false (by omega : ¬ (j + 1 < n))]
        simp only [List.replicate_zero, List.nil_append]
        cases hDh : D.head? with
        | none => rfl
        | some y => cases y <;> simp_all [isMarkO])
  refine ⟨w, 1 + t, Eval.seq e0 e, ?_⟩
  have := Nat.mul_le_mul_left n (show b + 3 + 1 ≤ b + 4 by omega)
  omega

/-! ## The slot pass with an explicit final state -/

/-- The specification part of `SlotPassStmt` for a program `prog` and a constant `C`. -/
def SlotSpecOf (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) (C : ℕ) : Prop :=
  ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), Function.Injective ι →
  ∀ (s : ℕ) (L : Fin 9 → List Bool) (rest : Fin 9 → List Sym) (D : List Sym)
    (S : K → List Sym) (v : AReg),
    (∀ j, TermOK (rest j)) → D.head? ≠ some .mark → (S (ι .X)).head? ≠ some .mark →
    S (ι .R) = List.replicate s .mark ++ D →
    (∀ j, S (ι (.src j)) = (L j).map Sym.bit ++ rest j) →
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (prog K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ C * (s + 1) ∧
      (∀ j, S' (ι (.src j)) = ((L j).drop s).map Sym.bit ++ rest j) ∧
      S' (ι .out) = (serialRun s 0 (slotSrcs L)).reverse.map Sym.bit ++ S (ι .out) ∧
      ∀ k, (∀ j, k ≠ ι (.src j)) → k ≠ ι .out → S' k = S k

variable {Esu : Type} [DecidableEq Esu]

theorem slot_apply {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {C : ℕ}
    (hsp : SlotSpecOf prog C) {ι : SlotRole → SK Esu} (hι : Function.Injective ι)
    (s : ℕ) (L : Fin 9 → List Bool) (S T : SK Esu → List Sym) (v : AReg)
    (hR : S (ι .R) = List.replicate s .mark) (hX : S (ι .X) = [])
    (hsrc : ∀ j, S (ι (.src j)) = (L j).map Sym.bit)
    (hTsrc : ∀ j, T (ι (.src j)) = ((L j).drop s).map Sym.bit)
    (hTout : T (ι .out) = (serialRun s 0 (slotSrcs L)).reverse.map Sym.bit ++ S (ι .out))
    (hTfr : ∀ k, (∀ j, k ≠ ι (.src j)) → k ≠ ι .out → T k = S k) :
    ∃ v' c, Eval [] (prog (SK Esu) ι) ⟨v, S⟩ ⟨v', T⟩ c ∧ c ≤ C * (s + 1) := by
  obtain ⟨v', S', c, e, hc, h1, h2, h3⟩ := hsp (SK Esu) ι hι s L (fun _ => []) [] S v
    (fun _ => TermOK.nil) (by simp) (by rw [hX]; simp) (by rw [hR, List.append_nil])
    (fun j => by rw [hsrc, List.append_nil])
  have hST : S' = T := by
    funext k
    by_cases hk : ∃ j, k = ι (.src j)
    · obtain ⟨j, rfl⟩ := hk
      rw [h1, hTsrc, List.append_nil]
    · push_neg at hk
      by_cases ho : k = ι .out
      · subst ho; rw [h2, hTout]
      · rw [h3 k hk ho, hTfr k hk ho]
  exact ⟨v', c, hST ▸ e, hc⟩

/-! ## Block-step stacks as fields -/

/-- The stacks that vary during a block step. -/
structure BF where
  zr : Fin 8 → List Sym
  zi : Fin 8 → List Sym
  tre : List Sym
  tim : List Sym
  mm : ℕ
  q : List Sym
  vre : List Sym
  vim : List Sym
  ntre : List Sym
  ntim : List Sym
  d : Fin 4 → List Sym
  es : List Sym

/-- The block-step stacks `f` over a base state `S0`. -/
def bst (S0 : SK Esu → List Sym) (f : BF) : SK Esu → List Sym
  | .inr (.inl (.Zr j)) => f.zr j
  | .inr (.inl (.Zi j)) => f.zi j
  | .inr (.inl .Tre) => f.tre
  | .inr (.inl .Tim) => f.tim
  | .inr (.inl .M) => List.replicate f.mm .mark
  | .inr (.inl .Q) => f.q
  | .inr (.inl .Vre) => f.vre
  | .inr (.inl .Vim) => f.vim
  | .inr (.inl .NTre) => f.ntre
  | .inr (.inl .NTim) => f.ntim
  | .inr (.inl (.D k)) => f.d k
  | .inr (.inl .Es) => f.es
  | k => S0 k

section Upd

variable (S0 : SK Esu → List Sym) (f : BF) (y : List Sym)

theorem bst_upd_tre : Function.update (bst S0 f) (sp .Tre) y = bst S0 { f with tre := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_tim : Function.update (bst S0 f) (sp .Tim) y = bst S0 { f with tim := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_q : Function.update (bst S0 f) (sp .Q) y = bst S0 { f with q := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_vre : Function.update (bst S0 f) (sp .Vre) y = bst S0 { f with vre := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_vim : Function.update (bst S0 f) (sp .Vim) y = bst S0 { f with vim := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_ntre : Function.update (bst S0 f) (sp .NTre) y = bst S0 { f with ntre := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_ntim : Function.update (bst S0 f) (sp .NTim) y = bst S0 { f with ntim := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_es : Function.update (bst S0 f) (sp .Es) y = bst S0 { f with es := y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_M (n : ℕ) :
    Function.update (bst S0 f) (sp .M) (List.replicate n .mark) = bst S0 { f with mm := n } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply]
  · rfl

theorem bst_upd_zr (j : Fin 8) :
    Function.update (bst S0 f) (sp (.Zr j)) y = bst S0 { f with zr := Function.update f.zr j y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply, eq_comm]
  · rfl

theorem bst_upd_zi (j : Fin 8) :
    Function.update (bst S0 f) (sp (.Zi j)) y = bst S0 { f with zi := Function.update f.zi j y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply, eq_comm]
  · rfl

theorem bst_upd_d (j : Fin 4) :
    Function.update (bst S0 f) (sp (.D j)) y = bst S0 { f with d := Function.update f.d j y } := by
  funext k; rcases k with k | (x | e)
  · rfl
  · cases x <;> simp [bst, Function.update_apply, eq_comm]
  · rfl

end Upd

/-- Advance the real streams. -/
def BF.advR (f : BF) (zr' : Fin 8 → List Sym) (tre' : List Sym) : BF :=
  { f with zr := zr', tre := tre' }

/-- Advance the imaginary streams. -/
def BF.advI (f : BF) (zi' : Fin 8 → List Sym) (tim' : List Sym) : BF :=
  { f with zi := zi', tim := tim' }

/-! ## One slot pass on the block stacks -/

theorem fin9_cases (j : Fin 9) : (j : ℕ) < 8 ∨ j = Fin.last 8 := by
  rcases Nat.lt_or_ge (j : ℕ) 8 with h | h
  · exact Or.inl h
  · exact Or.inr (Fin.ext (by simp; omega))

/-- **Real slot pass** on the block stacks (output `o = Vre` or `NTre`). -/
theorem slot_re_step {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {C : ℕ}
    (hsp : SlotSpecOf prog C) (s : ℕ) (S0 : SK Esu → List Sym) (f : BF) (L : Fin 9 → List Bool)
    (v : AReg) (o : SpS) (ho : o = .Vre ∨ o = .NTre)
    (hRs : S0 (sp (.ru .s)) = List.replicate s .mark) (hX5 : S0 (sp (.X 5)) = [])
    (hzr : ∀ i, f.zr i = (L i.castSucc).map Sym.bit) (htre : f.tre = (L (Fin.last 8)).map Sym.bit) :
    ∃ v' c, Eval [] (prog (SK Esu) (ιSP .Zr .Tre o)) ⟨v, bst S0 f⟩
      ⟨v', Function.update (bst S0 (f.advR (fun i => ((L i.castSucc).drop s).map Sym.bit)
          (((L (Fin.last 8)).drop s).map Sym.bit))) (sp o)
        ((serialRun s 0 (slotSrcs L)).reverse.map Sym.bit ++ bst S0 f (sp o))⟩ c ∧
      c ≤ C * (s + 1) := by
  have hoZ : ∀ j, o ≠ .Zr j := by rcases ho with rfl | rfl <;> simp
  have hoT : o ≠ .Tre := by rcases ho with rfl | rfl <;> simp
  have hι : Function.Injective (ιSP (Esu := Esu) .Zr .Tre o) :=
    ιSP_injective (fun a b h => by simpa using h) (fun j => by simp) hoZ (Ne.symm hoT) (by simp)
      (by rcases ho with rfl | rfl <;> simp) (by simp) (by rcases ho with rfl | rfl <;> simp)
      (fun j => by simp) (fun j => by simp)
  refine slot_apply hsp hι s L _ _ v hRs hX5 (fun j => ?_) (fun j => ?_) ?_ (fun k hk hk2 => ?_)
  · rcases fin9_cases j with h | rfl
    · simp only [ιSP, dif_pos h]
      show f.zr _ = _
      rw [hzr]; rfl
    · simp only [ιSP, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
      exact htre
  · rcases fin9_cases j with h | rfl
    · simp only [ιSP, dif_pos h]
      rw [Function.update_of_ne (by simpa using hoZ _ |>.symm)]
      rfl
    · simp only [ιSP, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
      rw [Function.update_of_ne (by simpa using hoT.symm)]
      rfl
  · simp only [ιSP, Function.update_self]
  · simp only [ιSP] at hk2
    rw [Function.update_of_ne hk2]
    rcases k with k | (x | e)
    · rfl
    · cases x with
      | Zr i => exact absurd (by simp [ιSP]) (hk i.castSucc)
      | Tre => exact absurd (by simp [ιSP]) (hk (Fin.last 8))
      | _ => rfl
    · rfl

/-- **Imaginary slot pass** on the block stacks (output `o = Vim` or `NTim`). -/
theorem slot_im_step {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {C : ℕ}
    (hsp : SlotSpecOf prog C) (s : ℕ) (S0 : SK Esu → List Sym) (f : BF) (L : Fin 9 → List Bool)
    (v : AReg) (o : SpS) (ho : o = .Vim ∨ o = .NTim)
    (hRs : S0 (sp (.ru .s)) = List.replicate s .mark) (hX5 : S0 (sp (.X 5)) = [])
    (hzi : ∀ i, f.zi i = (L i.castSucc).map Sym.bit) (htim : f.tim = (L (Fin.last 8)).map Sym.bit) :
    ∃ v' c, Eval [] (prog (SK Esu) (ιSP .Zi .Tim o)) ⟨v, bst S0 f⟩
      ⟨v', Function.update (bst S0 (f.advI (fun i => ((L i.castSucc).drop s).map Sym.bit)
          (((L (Fin.last 8)).drop s).map Sym.bit))) (sp o)
        ((serialRun s 0 (slotSrcs L)).reverse.map Sym.bit ++ bst S0 f (sp o))⟩ c ∧
      c ≤ C * (s + 1) := by
  have hoZ : ∀ j, o ≠ .Zi j := by rcases ho with rfl | rfl <;> simp
  have hoT : o ≠ .Tim := by rcases ho with rfl | rfl <;> simp
  have hι : Function.Injective (ιSP (Esu := Esu) .Zi .Tim o) :=
    ιSP_injective (fun a b h => by simpa using h) (fun j => by simp) hoZ (Ne.symm hoT) (by simp)
      (by rcases ho with rfl | rfl <;> simp) (by simp) (by rcases ho with rfl | rfl <;> simp)
      (fun j => by simp) (fun j => by simp)
  refine slot_apply hsp hι s L _ _ v hRs hX5 (fun j => ?_) (fun j => ?_) ?_ (fun k hk hk2 => ?_)
  · rcases fin9_cases j with h | rfl
    · simp only [ιSP, dif_pos h]
      show f.zi _ = _
      rw [hzi]; rfl
    · simp only [ιSP, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
      exact htim
  · rcases fin9_cases j with h | rfl
    · simp only [ιSP, dif_pos h]
      rw [Function.update_of_ne (by simpa using hoZ _ |>.symm)]
      rfl
    · simp only [ιSP, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
      rw [Function.update_of_ne (by simpa using hoT.symm)]
      rfl
  · simp only [ιSP, Function.update_self]
  · simp only [ιSP] at hk2
    rw [Function.update_of_ne hk2]
    rcases k with k | (x | e)
    · rfl
    · cases x with
      | Zi i => exact absurd (by simp [ιSP]) (hk i.castSucc)
      | Tim => exact absurd (by simp [ιSP]) (hk (Fin.last 8))
      | _ => rfl
    · rfl

end SubNLogN.Machine.Bridge.SpreadAux
