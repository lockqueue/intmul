/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesAddr
import SubNLogN.Machine.K1.RotateParSpec

/-!
# Lemma A.9 lines, one line kernel (`Machine/AppC/C7LinesLine.lean`)

One packed line of Lemma A.9 (`lem:transfer13`,
Appendix A.4 (`sec:transfer-packed`)) as a kernel on twelve named stacks, built from a Lemma A.8
interchange kernel (`C6Body`, the body of `C6InterchangeStmt`) and a parameterized controlled
rotation kernel (`RotBody`, the body of `K4RotateCtlParStmt 2 1 J off` for `off = lineOffOp σ op`):
exchange the target slot `j = σ⁻¹ tn` with slot `2` (if `j ≠ 2`), rotate slot `2` by the line
offset from the source stack onto the destination stack, exchange back on the destination. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Named stacks of the line kernel (`Fin 12`): `0` source array (consumed), `1` destination (the result
is pushed on its content), `2, 3, 4` three copies of `L = f·K`, `5` the Lemma A.8 counter
`N1·2^L·N2`, `6` `K`, `7` `ρ`, `8` `N1`, `9` `N2`, `10` `N3`, `11` `R` (all restored). Private
scratch: the Lemma A.8 kernel's and the rotation kernel's.

**Result (0 `sorry`).** `line_runs`: the line kernel moves the array `v` from the source to the
destination as `permByInv (linePull σ op …) v` (`C7LinesAddr.lean`), at cost
`(2·C₆ + C_r)·(⌈V·(L^τ + 1)⌉₊ + 1)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks AppC.Corr AppC.C7Aux

namespace AppC.C7LinesAux

/-! ## Kernel bodies -/

/-- The body of `C6InterchangeStmt τ` for a kernel `P` with cost constant `C`. -/
def C6Body (τ : ℝ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R) : Prop :=
  ∀ (A u1 u2 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) E → List Sym),
    1 ≤ u1 → 1 ≤ u2 → u1 ≤ u2 + 1 → u2 ≤ u1 + 1 → 1 ≤ A → 1 ≤ G → 1 ≤ B →
    v.length = A * 2 ^ u1 * G * 2 ^ u2 * B → (∀ p ∈ v, p.length = w) →
    BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
    S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u1 ++ r1 →
    S (.inl 2) = natSyms u2 ++ r2 → S (.inl 3) = natSyms G ++ r3 →
    S (.inl 4) = natSyms B ++ r4 → S (.inl 5) = natSyms w ++ r5 →
    Runs P S
      (Function.update S (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B) v) ++ rest))
      (fun _ => True) (C * (⌈(vol v : ℝ) * ((max u1 u2 : ℕ) : ℝ) ^ τ⌉₊ + 1))

/-- The body of `K4RotateCtlParStmt 2 1 J off` for a kernel `P` with cost constant `C`. -/
def RotBody (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 10) E) (fun _ => Sym) R) : Prop :=
  ∀ (np b1 n1 b2 n2 b s k1 k2 : ℕ) (v : List (List Bool))
    (rest r2 r3 r4 r5 r6 r7 r8 r9 : List Sym) (S : KLoc (Fin 10) E → List Sym),
    v.length = np * 2 ^ b1 * n1 * 2 ^ b2 * n2 * 2 ^ b * s → b1 ≤ 1 * b → b2 ≤ 1 * b →
    k1 ≤ 1 * b → k2 ≤ 1 * b →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
    TermOK r8 → TermOK r9 →
    S (.inl 0) = arrSyms v ++ rest →
    S (.inl 2) = natSyms b1 ++ r2 → S (.inl 3) = natSyms n1 ++ r3 →
    S (.inl 4) = natSyms b2 ++ r4 → S (.inl 5) = natSyms n2 ++ r5 →
    S (.inl 6) = natSyms b ++ r6 → S (.inl 7) = natSyms s ++ r7 →
    S (.inl 8) = natSyms k1 ++ r8 → S (.inl 9) = natSyms k2 ++ r9 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (rotCtlInvAddr (2 ^ b1) n1 (2 ^ b2) n2 (2 ^ b) s (off k1 k2 b)) v)
          ++ S (.inl 1)))
      (fun _ => True) (C * (vol v + 1))

/-! ## Embeddings and the line program -/

/-- Stack map of the Lemma A.8 call: array on stack `0` (`src`) or `1`, counters `L, L, G, N3, R`
(`G` on stack `5` if `useG`, else `N2` on stack `9`). -/
def emb6 {E₆ Er : Type} (src useG : Bool) : KLoc (Fin 6) E₆ → KLoc (Fin 12) (E₆ ⊕ Er)
  | .inl i => .inl (![if src then 0 else 1, 2, 3, if useG then 5 else 9, 10, 11] i)
  | .inr e => .inr (.inl e)

/-- Stack map of the rotation call: source `0`, destination `1`, counters
`b1 = L, n1 = N1, b2 = L, n2 = N2, b = L, s = N3, k1 = K, k2 = ρ`. -/
def embR {E₆ Er : Type} : KLoc (Fin 10) Er → KLoc (Fin 12) (E₆ ⊕ Er)
  | .inl i => .inl (![0, 1, 2, 8, 3, 9, 4, 10, 6, 7] i)
  | .inr e => .inr (.inr e)

theorem emb6_injective {E₆ Er : Type} (src useG : Bool) :
    Function.Injective (emb6 (E₆ := E₆) (Er := Er) src useG) := by
  have hfin : Function.Injective
      (fun i : Fin 6 => (![if src then 0 else 1, 2, 3, if useG then 5 else 9, 10, 11] i : Fin 12)) := by
    cases src <;> cases useG <;> decide
  rintro (i | e) (j | e') h
  · simp only [emb6, Sum.inl.injEq] at h
    rw [hfin h]
  · simp [emb6] at h
  · simp [emb6] at h
  · simp only [emb6, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embR_injective {E₆ Er : Type} : Function.Injective (embR (E₆ := E₆) (Er := Er)) := by
  have hfin : Function.Injective (fun i : Fin 10 => (![0, 1, 2, 8, 3, 9, 4, 10, 6, 7] i : Fin 12)) := by
    decide
  rintro (i | e) (j | e') h
  · simp only [embR, Sum.inl.injEq] at h
    rw [hfin h]
  · simp [embR] at h
  · simp [embR] at h
  · simp only [embR, Sum.inr.injEq] at h
    rw [h]

/-- **The line program** for target slot `j`. -/
def lineProg {E₆ Er R₆ Rr : Type} (j : Fin 3) (P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆)
    (Pr : Prog (KLoc (Fin 10) Er) (fun _ => Sym) Rr) :
    Prog (KLoc (Fin 12) (E₆ ⊕ Er)) (fun _ => Sym) (R₆ × Rr) :=
  if j = 2 then callInj embR (Lens.snd R₆ Rr) Pr
  else .seq (callInj (emb6 true (decide (j = 0))) (Lens.fst R₆ Rr) P₆)
    (.seq (callInj embR (Lens.snd R₆ Rr) Pr)
      (callInj (emb6 false (decide (j = 0))) (Lens.fst R₆ Rr) P₆))

theorem closed_lineProg {E₆ Er R₆ Rr : Type} (j : Fin 3)
    {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆} {Pr : Prog (KLoc (Fin 10) Er) (fun _ => Sym) Rr}
    (h6 : P₆.Closed) (hr : Pr.Closed) : (lineProg j P₆ Pr).Closed := by
  unfold lineProg
  split_ifs
  · exact closed_callInj _ _ hr
  · exact ⟨closed_callInj _ _ h6, closed_callInj _ _ hr, closed_callInj _ _ h6⟩

/-! ## Index ranges -/

theorem swapPull_lt {L N0 N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3) (j : Fin 3)
    {y : ℕ} (hy : y < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3) :
    swapPull L N1 N2 N3 j y < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3 := by
  obtain ⟨h0, hc, h1, h2, h3⟩ := c7_coords hN1 hN2 hN3 hy
  rw [← c7_decode L N1 N2 N3 y, swapPull_rank j hc h1 h2 h3]
  exact c7Rank_lt h0 (fun i => hc _) h1 h2 h3

theorem rot_lt {L N0 N1 N2 N3 : ℕ} (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (off : ℕ → ℕ → ℕ) {y : ℕ} (hy : y < N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3) :
    rotCtlInvAddr (2 ^ L) N1 (2 ^ L) N2 (2 ^ L) N3 off y <
      N0 * 2 ^ L * N1 * 2 ^ L * N2 * 2 ^ L * N3 := by
  obtain ⟨h0, hc, h1, h2, h3⟩ := c7_coords hN1 hN2 hN3 hy
  rw [← c7_decode L N1 N2 N3 y, rot_rank hc h1 h2 h3]
  refine c7Rank_lt h0 (fun i => ?_) h1 h2 h3
  rcases eq_or_ne i 2 with rfl | hi
  · rw [Function.update_self]; exact Nat.mod_lt _ (by positivity)
  · rw [Function.update_of_ne hi]; exact hc i

/-! ## Calls through injective embeddings -/

section Calls

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

theorem runs_call_upd1 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} (x : L) (w : List Sym) {Q : R → Prop}
    {T : ℕ} (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x w) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) w) (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => Function.update_of_ne (fun h => hk x h.symm) _ _)
  rw [Function.update_comp_eq_of_injective B hι x w]
  exact h

theorem runs_call_upd2 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} (x0 x1 : L) (w0 w1 : List Sym)
    {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 w0) x1 w1) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x0) w0) (ι x1) w1)
      (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => ?_)
  · rw [Function.update_comp_eq_of_injective _ hι x1 w1,
      Function.update_comp_eq_of_injective B hι x0 w0]
    exact h
  · rw [Function.update_of_ne (fun h => hk x1 h.symm), Function.update_of_ne (fun h => hk x0 h.symm)]

end Calls

/-- The cost of a line is at most `(2·C₆ + C_r)·(⌈V·(L^τ + 1)⌉₊ + 1)`. -/
theorem line_cost_le (τ : ℝ) (V L C₆ Cr : ℕ) :
    C₆ * (⌈(V : ℝ) * ((max L L : ℕ) : ℝ) ^ τ⌉₊ + 1) + (Cr * (V + 1) +
      C₆ * (⌈(V : ℝ) * ((max L L : ℕ) : ℝ) ^ τ⌉₊ + 1)) ≤
      (2 * C₆ + Cr) * (⌈(V : ℝ) * ((L : ℝ) ^ τ + 1)⌉₊ + 1) := by
  rw [max_self]
  have hpow : (0 : ℝ) ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  have h1 : ⌈(V : ℝ) * (L : ℝ) ^ τ⌉₊ ≤ ⌈(V : ℝ) * ((L : ℝ) ^ τ + 1)⌉₊ :=
    Nat.ceil_mono (by nlinarith)
  have h2 : V ≤ ⌈(V : ℝ) * ((L : ℝ) ^ τ + 1)⌉₊ := by
    have h3 : (V : ℝ) ≤ (V : ℝ) * ((L : ℝ) ^ τ + 1) := by nlinarith
    exact_mod_cast h3.trans (Nat.le_ceil _)
  nlinarith

/-! ## One line -/

/-- **One line kernel.** From the source array `v` on stack `0` and the counters, the line kernel
pushes `permByInv (linePull σ op K ρ f N1 N2 N3) v` onto the destination (stack `1`), consumes the
source and restores everything else. -/
theorem line_runs (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (op : Bool × ℤ × ℕ)
    {E₆ Er R₆ Rr : Type} [DecidableEq E₆] [DecidableEq Er] {C₆ Cr : ℕ}
    {P₆ : Prog (KLoc (Fin 6) E₆) (fun _ => Sym) R₆}
    {Pr : Prog (KLoc (Fin 10) Er) (fun _ => Sym) Rr}
    (h6 : C6Body τ C₆ P₆) (hr : RotBody (lineOffOp σ op) Cr Pr)
    {K ρ f N0 N1 N2 N3 R : ℕ} {v : List (List Bool)}
    {rest r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : List Sym}
    {S : KLoc (Fin 12) (E₆ ⊕ Er) → List Sym}
    (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3)
    (hlen : v.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3)
    (hrec : ∀ p ∈ v, p.length = R) (hrest : BlkTerm rest) (hdst : BlkTerm (S (.inl 1)))
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hr7 : TermOK r7) (hr8 : TermOK r8) (hr9 : TermOK r9) (hr10 : TermOK r10) (hr11 : TermOK r11)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hS2 : S (.inl 2) = natSyms (f * K) ++ r2)
    (hS3 : S (.inl 3) = natSyms (f * K) ++ r3) (hS4 : S (.inl 4) = natSyms (f * K) ++ r4)
    (hS5 : S (.inl 5) = natSyms (N1 * 2 ^ (f * K) * N2) ++ r5)
    (hS6 : S (.inl 6) = natSyms K ++ r6) (hS7 : S (.inl 7) = natSyms ρ ++ r7)
    (hS8 : S (.inl 8) = natSyms N1 ++ r8) (hS9 : S (.inl 9) = natSyms N2 ++ r9)
    (hS10 : S (.inl 10) = natSyms N3 ++ r10) (hS11 : S (.inl 11) = natSyms R ++ r11) :
    Runs (lineProg (σ.symm (tgtName op)) P₆ Pr) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (linePull σ op K ρ f N1 N2 N3) v) ++ S (.inl 1)))
      (fun _ => True) ((2 * C₆ + Cr) * (⌈(vol v : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ + 1)) := by
  have hL1 : 1 ≤ f * K := by nlinarith
  have hKL : K ≤ 1 * (f * K) := by nlinarith
  have hρL : ρ ≤ 1 * (f * K) := by nlinarith
  have hLL : f * K ≤ 1 * (f * K) := by omega
  have hN1' : 0 < N1 := hN1
  have hN2' : 0 < N2 := hN2
  have hN3' : 0 < N3 := hN3
  -- the rotation call, for any array of the right shape
  have rotStep : ∀ (w : List (List Bool)) (B : KLoc (Fin 12) (E₆ ⊕ Er) → List Sym),
      w.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 →
      B (.inl 0) = arrSyms w ++ rest → B (.inl 2) = S (.inl 2) → B (.inl 3) = S (.inl 3) →
      B (.inl 4) = S (.inl 4) → B (.inl 6) = S (.inl 6) → B (.inl 7) = S (.inl 7) →
      B (.inl 8) = S (.inl 8) → B (.inl 9) = S (.inl 9) → B (.inl 10) = S (.inl 10) →
      Runs (callInj embR (Lens.snd R₆ Rr) Pr) B
        (Function.update (Function.update B (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (rotCtlInvAddr (2 ^ (f * K)) N1 (2 ^ (f * K)) N2 (2 ^ (f * K)) N3
            (lineOffOp σ op K ρ (f * K))) w) ++ B (.inl 1)))
        (fun _ => True) (Cr * (vol w + 1)) := by
    intro w B hw hB0 hB2 hB3 hB4 hB6 hB7 hB8 hB9 hB10
    have e := hr N0 (f * K) N1 (f * K) N2 (f * K) N3 K ρ w rest r2 r8 r3 r9 r4 r10 r6 r7
      (B ∘ embR) hw hLL hLL hKL hρL hrest hr2 hr8 hr3 hr9 hr4 hr10 hr6 hr7
      hB0 (hB2.trans hS2) (hB8.trans hS8) (hB3.trans hS3) (hB9.trans hS9) (hB4.trans hS4)
      (hB10.trans hS10) (hB6.trans hS6) (hB7.trans hS7)
    exact runs_call_upd2 embR_injective (Lens.snd R₆ Rr) (.inl 0) (.inl 1) _ _ e
  by_cases hj2 : σ.symm (tgtName op) = 2
  · -- target already in slot 2: one rotation
    rw [lineProg, if_pos hj2]
    have hsw : swapPull (f * K) N1 N2 N3 (σ.symm (tgtName op)) = fun y => y := by
      rw [hj2]; funext y; simp [swapPull]
    have X := rotStep v S hlen hS0 rfl rfl rfl rfl rfl rfl rfl rfl
    have hpl : permByInv (rotCtlInvAddr (2 ^ (f * K)) N1 (2 ^ (f * K)) N2 (2 ^ (f * K)) N3
        (lineOffOp σ op K ρ (f * K))) v = permByInv (linePull σ op K ρ f N1 N2 N3) v := by
      apply permByInv_congr
      intro y _
      simp only [linePull, hsw]
    rw [hpl] at X
    refine WP.W9comp.runs_mono X (fun _ _ => trivial) ?_
    have := line_cost_le τ (vol v) (f * K) C₆ Cr
    omega
  · -- exchange, rotation, exchange
    rw [lineProg, if_neg hj2]
    obtain ⟨G', A', rG, hG', hA', hlenA, hSG, hrG, hswp⟩ : ∃ G' A' rG, 1 ≤ G' ∧ 1 ≤ A' ∧
        v.length = A' * 2 ^ (f * K) * G' * 2 ^ (f * K) * N3 ∧
        S (.inl (if decide (σ.symm (tgtName op) = 0) then 5 else 9)) = natSyms G' ++ rG ∧
        TermOK rG ∧
        swapPull (f * K) N1 N2 N3 (σ.symm (tgtName op)) =
          swapFieldsInv (2 ^ (f * K)) G' (2 ^ (f * K)) N3 := by
      rcases fin3_cases (σ.symm (tgtName op)) with h | h | h
      · refine ⟨N1 * 2 ^ (f * K) * N2, N0, r5, Nat.mul_pos (Nat.mul_pos hN1 (by positivity)) hN2,
          hN0, by rw [hlen]; ring, by rw [h]; simpa using hS5, hr5, by rw [h]; simp [swapPull]⟩
      · refine ⟨N2, N0 * 2 ^ (f * K) * N1, r9, hN2,
          Nat.mul_pos (Nat.mul_pos hN0 (by positivity)) hN1, by rw [hlen]; try ring,
          by rw [h]; simpa using hS9, hr9, by rw [h]; simp [swapPull]⟩
      · exact absurd h hj2
    set sw := swapFieldsInv (2 ^ (f * K)) G' (2 ^ (f * K)) N3 with hsw
    set rot := rotCtlInvAddr (2 ^ (f * K)) N1 (2 ^ (f * K)) N2 (2 ^ (f * K)) N3
      (lineOffOp σ op K ρ (f * K)) with hrot
    have hswlt : ∀ y < v.length, sw y < v.length := by
      intro y hy
      rw [hlen] at hy ⊢
      have := swapPull_lt hN1' hN2' hN3' (σ.symm (tgtName op)) hy
      rwa [hswp] at this
    have hrotlt : ∀ y < v.length, rot y < v.length := by
      intro y hy
      rw [hlen] at hy ⊢
      exact rot_lt hN1' hN2' hN3' _ hy
    -- step 1: exchange on the source
    set useG := decide (σ.symm (tgtName op) = 0) with huseG
    have e1 := h6 A' (f * K) (f * K) G' N3 R v rest r2 r3 rG r10 r11
      (S ∘ emb6 (Er := Er) true useG) hL1 hL1 (by omega) (by omega) hA' hG' hN3 hlenA hrec hrest
      hr2 hr3 hrG hr10 hr11 hS0 hS2 hS3 hSG hS10 hS11
    have X1 : Runs (callInj (emb6 true useG) (Lens.fst R₆ Rr) P₆) S
        (Function.update S (.inl 0) (arrSyms (permByInv sw v) ++ rest)) (fun _ => True)
        (C₆ * (⌈(vol v : ℝ) * ((max (f * K) (f * K) : ℕ) : ℝ) ^ τ⌉₊ + 1)) :=
      runs_call_upd1 (emb6_injective true useG) (Lens.fst R₆ Rr) (.inl 0) _ e1
    -- step 2: rotation from the source onto the destination
    set v1 := permByInv sw v with hv1
    have hl1 : v1.length = v.length := permByInv_length _ _
    have hrec1 : ∀ p ∈ v1, p.length = R := fun p hp => hrec p (permByInv_mem hswlt hp)
    have hne : ∀ i : Fin 12, i ≠ 0 →
        Function.update S (.inl 0) (arrSyms v1 ++ rest) (.inl i) = S (.inl i) :=
      fun i hi => Function.update_of_ne (by simpa using hi) _ _
    have X2 := rotStep v1 (Function.update S (.inl 0) (arrSyms v1 ++ rest)) (hl1.trans hlen)
      (Function.update_self _ _ _) (hne 2 (by decide)) (hne 3 (by decide)) (hne 4 (by decide))
      (hne 6 (by decide)) (hne 7 (by decide)) (hne 8 (by decide)) (hne 9 (by decide))
      (hne 10 (by decide))
    rw [hne 1 (by decide)] at X2
    -- step 3: exchange on the destination
    set v2 := permByInv rot v1 with hv2
    have hl2 : v2.length = v.length := (permByInv_length _ _).trans hl1
    have hrotlt1 : ∀ y < v1.length, rot y < v1.length := fun y hy => by
      rw [hl1] at hy ⊢; exact hrotlt y hy
    have hrec2 : ∀ p ∈ v2, p.length = R := fun p hp => hrec1 p (permByInv_mem hrotlt1 hp)
    set S2 := Function.update (Function.update (Function.update S (.inl 0) (arrSyms v1 ++ rest))
      (.inl 0) rest) (.inl 1) (arrSyms v2 ++ S (.inl 1)) with hS2def
    have hne2 : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → S2 (.inl i) = S (.inl i) := fun i hi0 hi1 => by
      rw [hS2def, Function.update_of_ne (by simpa using hi1), Function.update_of_ne (by simpa using hi0),
        Function.update_of_ne (by simpa using hi0)]
    have hS2_1 : S2 (.inl 1) = arrSyms v2 ++ S (.inl 1) := Function.update_self _ _ _
    have hSG2 : S2 (.inl (if useG then 5 else 9)) = natSyms G' ++ rG := by
      rw [hne2 _ (by cases useG <;> decide) (by cases useG <;> decide)]; exact hSG
    have e3 := h6 A' (f * K) (f * K) G' N3 R v2 (S (.inl 1)) r2 r3 rG r10 r11
      (S2 ∘ emb6 (Er := Er) false useG) hL1 hL1 (by omega) (by omega) hA' hG' hN3
      (hl2.trans hlenA) hrec2 hdst hr2 hr3 hrG hr10 hr11 hS2_1
      ((hne2 2 (by decide) (by decide)).trans hS2) ((hne2 3 (by decide) (by decide)).trans hS3)
      hSG2 ((hne2 10 (by decide) (by decide)).trans hS10)
      ((hne2 11 (by decide) (by decide)).trans hS11)
    have X3 : Runs (callInj (emb6 false useG) (Lens.fst R₆ Rr) P₆) S2
        (Function.update S2 (.inl 1) (arrSyms (permByInv sw v2) ++ S (.inl 1))) (fun _ => True)
        (C₆ * (⌈(vol v2 : ℝ) * ((max (f * K) (f * K) : ℕ) : ℝ) ^ τ⌉₊ + 1)) :=
      runs_call_upd1 (emb6_injective false useG) (Lens.fst R₆ Rr) (.inl 0) _ e3
    have X := WP.W9comp.runs_seq X1 (WP.W9comp.runs_seq X2 X3)
    -- the final array and the final stacks
    have hv3 : permByInv sw v2 = permByInv (linePull σ op K ρ f N1 N2 N3) v := by
      have hswlt1 : ∀ y < v1.length, sw y < v1.length := fun y hy => by
        rw [hl1] at hy ⊢; exact hswlt y hy
      rw [hv2, permByInv_permByInv hswlt1, hv1, permByInv_permByInv]
      · apply permByInv_congr
        intro y _
        simp only [linePull, hswp, hsw, hrot]
      · intro y hy
        exact hrotlt _ (hswlt y hy)
    have hvol1 : vol v1 = vol v := by rw [vol_of_len hrec1, vol_of_len hrec, hl1]
    have hvol2 : vol v2 = vol v := by rw [vol_of_len hrec2, vol_of_len hrec, hl2]
    rw [hv3, hvol1, hvol2] at X
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial)
      (line_cost_le τ (vol v) (f * K) C₆ Cr)
    rw [hS2def, Function.update_idem, Function.update_idem]

end AppC.C7LinesAux

end SubNLogN.Machine
