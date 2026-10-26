import Contracts.Machine.W3
import Contracts.Machine.W4

/-!
# WP.W9e.Kit — composing components in `Runs` form

Every step of the POST phases is a `Runs P S S' Q T` statement (`Contracts.Machine.Common`): exact
stacks before and after, any register value on entry, a register property `Q` afterwards, cost at
most `T`. The combinators follow `WP.W0m.Kit` (copied, not imported, so that the packages stay
independent):

* `runs_seq`, `runs_mono`, `runs_post`, `runs_ite_true`, `runs_ite_false`;
* `runs_liftMacro` (a library macro with an exact `Eval` lemma, through a register lens) and
  `runs_liftRegs` (a `Runs` component through a register lens);
* `runs_embed`, `runs_embed_upd`, … (a contract instance over local stacks, renamed along an
  injective map), with `embL` / `embL_inj` for call sites;
* **`peekLoop`** and `runs_peekLoop`: every loop of the POST phases has the shape
  `peek k; while cond(reg) do (core; peek k)`, and its correctness is proved once here from a
  `Runs` triple for `core` per iteration;
* closedness: `freeBelow_liftRegs`, `freeBelow_mapStk`.
-/

namespace WP.W9e

open TMFw TMFw.Lib TMFw.Contracts

section Kit

variable {K σ : Type} [DecidableEq K]

theorem runs_seq {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 Q2 (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

theorem runs_mono {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q Q' : σ → Prop}
    {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

theorem runs_post {P : Prog K (fun _ => Sym) σ} {S S1 S2 : K → List Sym} {Q : σ → Prop}
    {T T' : ℕ} (h : Runs P S S1 Q T) (e : S1 = S2) (hT : T ≤ T') : Runs P S S2 Q T' := by
  subst e
  exact runs_mono h (fun _ h => h) hT

theorem runs_weak {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : Runs P S S' Q T) : Runs P S S' (fun _ => True) T :=
  runs_mono h (fun _ _ => trivial) le_rfl

theorem runs_ite_true {P Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun v => c v = true) T1) (h2 : Runs Pt S2 S3 Q T2) :
    Runs (.seq P (.ite c Pt Pf)) S1 S3 Q (T1 + (T2 + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := h1 s hs
  obtain ⟨s2, t2, e2, hq, ht2⟩ := h2 s1 hs1
  exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true hc e2), hq, by omega⟩

theorem runs_ite_false {P Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun v => c v = false) T1) (h2 : Runs Pf S2 S3 Q T2) :
    Runs (.seq P (.ite c Pt Pf)) S1 S3 Q (T1 + (T2 + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := h1 s hs
  obtain ⟨s2, t2, e2, hq, ht2⟩ := h2 s1 hs1
  exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false hc e2), hq, by omega⟩

/-- A library macro (exact `Eval` for every register value) through a register lens. -/
theorem runs_liftMacro {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Qr : τ → Prop} {T : ℕ}
    (h : ∀ r : τ, ∃ r' t, Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t ∧ Qr r' ∧ t ≤ T) :
    Runs (p.liftRegs l) S S' (fun v => Qr (l.get v)) T := by
  intro s hs
  obtain ⟨r', t, e, hq, ht⟩ := h (l.get s.var)
  refine ⟨⟨l.set s.var r', S'⟩, t, ?_, ⟨rfl, ?_⟩, ht⟩
  · obtain ⟨v, stk⟩ := s
    change stk = S at hs
    subst hs
    exact Eval.liftRegs l e v rfl
  · show Qr (l.get (l.set s.var r'))
    rw [l.get_set]
    exact hq

/-- A `Runs` component through a register lens. -/
theorem runs_liftRegs {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs p S S' Q T) :
    Runs (p.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  have h2 := Triple.liftRegs l h (fun _ => True) (fun _ _ _ => trivial)
  intro s hs
  obtain ⟨s', t, e, ⟨⟨hs1, hq⟩, -⟩, ht⟩ := h2 s ⟨hs, trivial⟩
  exact ⟨s', t, e, ⟨hs1, hq⟩, ht⟩

/-- A local component renamed along an injective `ι`, with the big post-state given exactly. -/
theorem runs_embed {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {S S' : L → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P S S' Q T) (B B' : K → List Sym) (hB : ∀ x, B (ι x) = S x)
    (hB' : ∀ x, B' (ι x) = S' x) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (P.mapStk ι) B B' Q T := by
  have h2 := Runs.embed hι h B hB
  intro s hs
  obtain ⟨s', t, e, ⟨hin, hfr, hq⟩, ht⟩ := h2 s hs
  refine ⟨s', t, e, ⟨?_, hq⟩, ht⟩
  funext k
  by_cases hk : ∃ x, ι x = k
  · obtain ⟨x, rfl⟩ := hk
    rw [hin x, hB' x]
  · simp only [not_exists] at hk
    rw [hfr k hk, hout k hk]

theorem runs_embed_upd {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x0 : L)
    (v : List Sym)
    (h : Runs P (fun x => B (ι x)) (Function.update (fun x => B (ι x)) x0 v) Q T) :
    Runs (P.mapStk ι) B (Function.update B (ι x0) v) Q T := by
  refine runs_embed hι h B _ (fun _ => rfl) (fun x => ?_) (fun k hk => ?_)
  · by_cases hx : x = x0
    · subst hx
      simp
    · rw [Function.update_of_ne (hι.ne hx), Function.update_of_ne hx]
  · exact Function.update_of_ne (Ne.symm (hk x0)) _ _

theorem runs_embed_upd2 {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x0 x1 : L)
    (v0 v1 : List Sym)
    (h : Runs P (fun x => B (ι x))
      (Function.update (Function.update (fun x => B (ι x)) x0 v0) x1 v1) Q T) :
    Runs (P.mapStk ι) B (Function.update (Function.update B (ι x0) v0) (ι x1) v1) Q T := by
  refine runs_embed hι h B _ (fun _ => rfl) (fun x => ?_) (fun k hk => ?_)
  · by_cases hx1 : x = x1
    · subst hx1
      simp
    · rw [Function.update_of_ne (hι.ne hx1), Function.update_of_ne hx1]
      by_cases hx0 : x = x0
      · subst hx0
        simp
      · rw [Function.update_of_ne (hι.ne hx0), Function.update_of_ne hx0]
  · rw [Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

theorem runs_embed_same {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (h : Runs P (fun x => B (ι x)) (fun x => B (ι x)) Q T) : Runs (P.mapStk ι) B B Q T :=
  runs_embed hι h B B (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

end Kit

/-! ## Call sites of contract programs -/

/-- Call-site stack map: named stacks via `named`, scratch stacks via `scr`. -/
def embL {K : Type} {n m : ℕ} (named : Fin n → K) (scr : Fin m → K) : Loc n m → K :=
  Sum.elim named scr

theorem embL_inj {K : Type} {n m : ℕ} {named : Fin n → K} {scr : Fin m → K}
    (h1 : Function.Injective named) (h2 : Function.Injective scr) (h3 : ∀ i j, named i ≠ scr j) :
    Function.Injective (embL named scr) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (h1 h)
  · exact absurd h (h3 i j)
  · exact absurd h.symm (h3 j i)
  · exact congrArg Sum.inr (h2 h)

/-! ## Peek-guarded loops -/

/-- Peek stack `k` into the symbol register (through the lens `l`). -/
def peekL {K σ : Type} (l : Lens σ (Option Sym)) (k : K) : Prog K (fun _ => Sym) σ :=
  (peekR k).liftRegs l

/-- `peek k; while cond reg do (core; peek k)`. -/
def peekLoop {K σ : Type} (l : Lens σ (Option Sym)) (k : K) (cond : Option Sym → Bool)
    (core : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (peekL l k) (.loop (fun v => cond (l.get v)) (.seq core (peekL l k)))

section Loop

variable {K σ : Type} [DecidableEq K]

theorem eval_peekL (l : Lens σ (Option Sym)) (k : K) (v : σ) (S : K → List Sym) :
    Eval [] (peekL l k) ⟨v, S⟩ ⟨l.set v (S k).head?, S⟩ 1 :=
  Eval.peek [] k _ v S

theorem peekLoop_body (l : Lens σ (Option Sym)) (k : K) (cond : Option Sym → Bool)
    (core : Prog K (fun _ => Sym) σ) (B : ℕ) :
    ∀ (n : ℕ) (S : ℕ → K → List Sym), (∀ i < n, Runs core (S i) (S (i + 1)) (fun _ => True) B) →
      (∀ i < n, cond (S i k).head? = true) → cond (S n k).head? = false →
      Triple [] (fun s => s.stk = S 0 ∧ l.get s.var = (S 0 k).head?)
        (.loop (fun v => cond (l.get v)) (.seq core (peekL l k)))
        (fun s => s.stk = S n ∧ True) (n * (B + 2) + 1)
  | 0, S, _, _, hstop => by
    rintro ⟨v, stk⟩ ⟨hs, hv⟩
    refine ⟨⟨v, stk⟩, 1, Eval.loop_false ?_, ⟨hs, trivial⟩, by omega⟩
    show cond (l.get v) = false
    rw [hv]
    exact hstop
  | n + 1, S, hcore, hcont, hstop => by
    rintro ⟨v, stk⟩ ⟨hs, hv⟩
    have hc : cond (l.get v) = true := by
      rw [hv]
      exact hcont 0 (by omega)
    obtain ⟨⟨v1, stk1⟩, t1, e1, ⟨hs1, -⟩, ht1⟩ := hcore 0 (by omega) ⟨v, stk⟩ hs
    have e2 := eval_peekL l k v1 stk1
    have ih := peekLoop_body l k cond core B n (fun i => S (i + 1))
      (fun i hi => hcore (i + 1) (by omega)) (fun i hi => hcont (i + 1) (by omega)) hstop
    obtain ⟨s2, t2, e3, ⟨hs2, -⟩, ht2⟩ := ih ⟨l.set v1 (stk1 k).head?, stk1⟩
      ⟨hs1, by rw [l.get_set]; simp only at hs1; rw [hs1]⟩
    refine ⟨s2, (t1 + 1) + t2 + 1, Eval.loop_true hc (Eval.seq e1 e2) e3, ⟨hs2, trivial⟩, ?_⟩
    rw [Nat.succ_mul]
    omega

/-- **Peek-guarded loop rule.** If `core` maps `S i` to `S (i+1)` within `B` for `i < n`, `cond`
holds on the top of `k` at `S i` for `i < n` and fails at `S n`, then the loop maps `S 0` to `S n`
within `n·(B + 2) + 2`. -/
theorem runs_peekLoop (l : Lens σ (Option Sym)) (k : K) (cond : Option Sym → Bool)
    (core : Prog K (fun _ => Sym) σ) (B n : ℕ) (S : ℕ → K → List Sym)
    (hcore : ∀ i < n, Runs core (S i) (S (i + 1)) (fun _ => True) B)
    (hcont : ∀ i < n, cond (S i k).head? = true) (hstop : cond (S n k).head? = false) :
    Runs (peekLoop l k cond core) (S 0) (S n) (fun _ => True) (n * (B + 2) + 2) := by
  rintro ⟨v, stk⟩ hs
  simp only at hs
  subst hs
  have e1 := eval_peekL l k v (S 0)
  obtain ⟨s2, t2, e2, hq, ht2⟩ := peekLoop_body l k cond core B n S hcore hcont hstop
    ⟨l.set v (S 0 k).head?, S 0⟩ ⟨rfl, l.get_set _ _⟩
  exact ⟨s2, 1 + t2, Eval.seq e1 e2, hq, by omega⟩

end Loop

/-! ## Closedness -/

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .loop _ p, d => freeBelow_liftRegs l p d
  | .fix b, d => freeBelow_liftRegs l b (d + 1)
  | .recur _, _ => Iff.rfl

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .ite _ p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .loop _ p, d => freeBelow_mapStk ι p d
  | .fix b, d => freeBelow_mapStk ι b (d + 1)
  | .recur _, _ => Iff.rfl

#assert_std_axioms runs_seq runs_mono runs_post runs_weak runs_ite_true runs_ite_false
  runs_liftMacro runs_liftRegs runs_embed runs_embed_upd runs_embed_upd2 runs_embed_same embL_inj
  eval_peekL peekLoop_body runs_peekLoop freeBelow_liftRegs freeBelow_mapStk

end WP.W9e
