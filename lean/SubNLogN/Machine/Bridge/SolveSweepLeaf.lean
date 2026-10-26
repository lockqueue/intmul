/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepLayout
import SubNLogN.Machine.Arith.Value

/-!
# K5-SOLVE (1d): leaf-kernel calls of the sweep kernel

The three arithmetic leaves (`Contracts/Arith.lean`, taken as hypotheses by the solver theorem) as
predicates on a program (`CMSpec`, `RHSpec`, `CASpec`: the bodies of `CMulTruncStmt`,
`RoundHalfUpShiftStmt`, `CAddStmt`), their embeddings into the sweep layout (fixed temporary stacks
and counter stacks), and their effect on single-record operands in `mk` states:
* `runs_cm`: `xa = [y]`, `xb = [(m,0)]` ↦ `xc = [y·m]` (exact product at width `wI + wT + 1`);
* `runs_rhD`, `runs_rhF`: `xc = [p]` ↦ `xd = [Quant_q p]` (width `wI`), resp. `xf` (width `wI + 1`);
* `runs_ca`: `xd = [b]`, `xf = [r]` ↦ `xg = [b + r]` (width `wI`).
All proved (from the leaf specs).
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-! ## The leaf specifications -/

/-- Body of `CMulTruncStmt` for a program `P` with scratch `E`, registers `R`, constant `C`. -/
def CMSpec (E : Type) [Fintype E] [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 7) E) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 s : ℕ) (z θ : List (List CInt)) (rz rθ r3 r4 r5 r6 : List Sym)
      (S : KLoc (Fin 7) E → List Sym),
      KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 θ → CAligned z θ →
      CArrFits w3 (zipC (cmulTruncC s) z θ) →
      BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 θ ++ rθ →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2)))
        (fun _ => True)
        (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 θ + cvol w3 z +
          (ncoef z + 1) * (bitLen s + 1) + w1 + w2 + w3))

/-- Body of `RoundHalfUpShiftStmt`. -/
def RHSpec (E : Type) [Fintype E] [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 5) E) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (roundHalfUpShiftC s) v) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
      S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w2 (mapC (roundHalfUpShiftC s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- Body of `CAddStmt`. -/
def CASpec (E : Type) [Fintype E] [DecidableEq E] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 6) E) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
      CArrFits w3 (zipC caddC u v) →
      BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
          (carrSyms w3 (zipC caddC u v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

/-! ## Single-record facts -/

theorem blkTerm_nil' : BlkTerm [] := fun _ h => by simp at h

theorem cvol_one (w : ℕ) (c : CInt) : cvol w [[c]] = 2 * w + 1 := by
  rw [cvol_eq]; simp [ncoef]; ring

theorem cArrFits_one {w : ℕ} {c : CInt} (h : FitsTwos w c.1 ∧ FitsTwos w c.2) : CArrFits w [[c]] := by
  intro cs hcs d hd
  rw [List.mem_singleton] at hcs
  subst hcs
  rw [List.mem_singleton] at hd
  subst hd
  exact h

theorem cAligned_one (a b : CInt) : CAligned [[a]] [[b]] := by
  simp [CAligned]

/-- A product of a `wI`-bit and a `wT`-bit integer fits `wI + wT + 1` bits. -/
theorem fitsTwos_mul {wI wT : ℕ} (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) {a b : ℤ} (ha : FitsTwos wI a)
    (hb : FitsTwos wT b) : FitsTwos (wI + wT + 1) (a * b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hA : |a| ≤ 2 ^ (wI - 1) := abs_le.mpr ⟨ha1, ha2.le⟩
  have hB : |b| ≤ 2 ^ (wT - 1) := abs_le.mpr ⟨hb1, hb2.le⟩
  have hAB : |a * b| ≤ 2 ^ (wI - 1) * 2 ^ (wT - 1) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
  have hpow : (2 : ℤ) ^ (wI - 1) * 2 ^ (wT - 1) < 2 ^ (wI + wT + 1 - 1) := by
    rw [← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  constructor
  · have := neg_abs_le (a * b); linarith
  · have := le_abs_self (a * b); linarith

theorem fits_cmul {wI wT : ℕ} (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) {y : CInt} {m : ℤ}
    (hy : FitsTwos wI y.1 ∧ FitsTwos wI y.2) (hm : FitsTwos wT m) :
    FitsTwos (wI + wT + 1) (cmulTruncC 0 y (m, 0)).1 ∧
      FitsTwos (wI + wT + 1) (cmulTruncC 0 y (m, 0)).2 := by
  rw [cmulTruncC_zero_real]
  exact ⟨fitsTwos_mul hwI hwT hy.1 hm, fitsTwos_mul hwI hwT hy.2 hm⟩

theorem fitsTwos_zero {w : ℕ} : FitsTwos w 0 := by
  constructor
  · have : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
    linarith
  · positivity

/-! ## Embeddings of the leaves -/

section Calls

variable {LE σ : Type} [DecidableEq LE]

/-- Embedding of a leaf's named stacks (`tab`) and scratch (`inj`) into the sweep layout. -/
def ιtab {n : ℕ} {E : Type} (tab : Fin n → KS LE) (inj : E → LE) : KLoc (Fin n) E → KS LE
  | .inl i => tab i
  | .inr e => .inr (.inr (inj e))

theorem ιtab_injective {n : ℕ} {E : Type} {tab : Fin n → KS LE} {inj : E → LE}
    (htab : Function.Injective tab) (hne : ∀ i e, tab i ≠ .inr (.inr e))
    (hinj : Function.Injective inj) : Function.Injective (ιtab tab inj) := by
  rintro (i | e) (j | e') h
  · exact congrArg Sum.inl (htab h)
  · exact absurd h (hne i (inj e'))
  · exact absurd h.symm (hne j (inj e))
  · simp only [ιtab, Sum.inr.injEq] at h
    rw [hinj h]

/-- If the new state differs from the old one only on stacks in the image of `ι`, then `hout`. -/
theorem upd_out {n : ℕ} {E : Type} {ι : KLoc (Fin n) E → KS LE} (B : KS LE → List Sym)
    (a b c : Fin n) (va vb vc : List Sym) (k : KS LE) (hk : ∀ x, ι x ≠ k) :
    Function.update (Function.update (Function.update B (ι (.inl a)) va) (ι (.inl b)) vb)
      (ι (.inl c)) vc k = B k := by
  rw [Function.update_of_ne (fun h => hk _ h.symm), Function.update_of_ne (fun h => hk _ h.symm),
    Function.update_of_ne (fun h => hk _ h.symm)]

/-- The CMul table: `xa`, `xb` → `xc`; counters `wI`, `wT`, `wP`, `0`. -/
def cmTab : Fin 7 → KS LE :=
  ![loc (.inr .xa), loc (.inr .xb), loc (.inr .xc), .inl .cwI, .inl .cwT, .inl .cwP, .inl .c0]

theorem cmTab_injective : Function.Injective (cmTab (LE := LE)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cmTab, loc, dN]

theorem cmTab_ne (i : Fin 7) (e : LE) : cmTab i ≠ .inr (.inr e) := by
  fin_cases i <;> simp [cmTab, loc]

/-- Cost of one single-record CMul call (closed form). -/
def cmCost (wI wT : ℕ) : ℕ :=
  mulW (wI + wT + 1) + (2 * wI + 1) + (2 * wT + 1) + (2 * (wI + wT + 1) + 1) + 2 + wI + wT +
    (wI + wT + 1)

theorem runs_cm {Ecm Rcm : Type} [Fintype Ecm] [DecidableEq Ecm] {icm : Ecm → LE}
    (hicm : Function.Injective icm) (lcm : Lens σ Rcm) {Ccm : ℕ}
    {Pcm : Prog (KLoc (Fin 7) Ecm) (fun _ => Sym) Rcm} (scm : CMSpec Ecm Rcm Ccm Pcm)
    {base : KS LE → List Sym} (hclean : ∀ e, base (.inr (.inr (icm e))) = [])
    {wI wT : ℕ} (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) {r3 r4 r5 r6 : List Sym}
    (h3 : base (.inl .cwI) = natSyms wI ++ r3) (h4 : base (.inl .cwT) = natSyms wT ++ r4)
    (h5 : base (.inl .cwP) = natSyms (wI + wT + 1) ++ r5) (h6 : base (.inl .c0) = natSyms 0 ++ r6)
    (t3 : TermOK r3) (t4 : TermOK r4) (t5 : TermOK r5) (t6 : TermOK r6)
    (V : SwD ⊕ SwW → List Sym) {y : CInt} {m : ℤ}
    (hxa : V (.inr .xa) = carrSyms wI [[y]]) (hxb : V (.inr .xb) = carrSyms wT [[(m, 0)]])
    (hy : FitsTwos wI y.1 ∧ FitsTwos wI y.2) (hm : FitsTwos wT m) :
    Runs (callInj (ιtab cmTab icm) lcm Pcm) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inr .xa) []) (.inr .xb) [])
        (.inr .xc) (carrSyms (wI + wT + 1) [[cmulTruncC 0 y (m, 0)]] ++ V (.inr .xc))))
      (fun _ => True) (Ccm * cmCost wI wT) := by
  have hι := ιtab_injective (cmTab_injective (LE := LE)) cmTab_ne hicm
  have key := scm wI wT (wI + wT + 1) 0 [[y]] [[(m, 0)]] [] [] r3 r4 r5 r6
    (mk base V ∘ ιtab cmTab icm) (fun e => by simp [ιtab, hclean]) hwI hwT (by omega)
    (cArrFits_one hy) (cArrFits_one ⟨hm, fitsTwos_zero⟩) (cAligned_one _ _)
    (by simpa [zipC] using cArrFits_one (fits_cmul hwI hwT hy hm))
    blkTerm_nil' blkTerm_nil' t3 t4 t5 t6
    (by simp [ιtab, cmTab, hxa]) (by simp [ιtab, cmTab, hxb])
    (by simp [ιtab, cmTab, h3]) (by simp [ιtab, cmTab, h4]) (by simp [ιtab, cmTab, h5])
    (by simp [ιtab, cmTab, h6])
  rw [← Function.update_comp_eq_of_injective _ hι, ← Function.update_comp_eq_of_injective _ hι,
    ← Function.update_comp_eq_of_injective _ hι] at key
  have hrun := runs_callInj hι lcm key (fun k hk => upd_out _ 0 1 2 _ _ _ k hk)
  have hcost : Ccm * (ncoef [[y]] * mulW (wI + wT + 1) + cvol wI [[y]] + cvol wT [[(m, 0)]] +
      cvol (wI + wT + 1) [[y]] + (ncoef [[y]] + 1) * (bitLen 0 + 1) + wI + wT + (wI + wT + 1)) =
      Ccm * cmCost wI wT := by
    simp [cmCost, cvol_one, ncoef, bitLen, TMFw.encodeNat_zero]
  refine WP.W9comp.runs_congr (hcost ▸ hrun) ?_
  simp [ιtab, cmTab, update_mk, zipC]

/-- Two-update variant of `upd_out`. -/
theorem upd_out2 {n : ℕ} {E : Type} {ι : KLoc (Fin n) E → KS LE} (B : KS LE → List Sym)
    (a b : Fin n) (va vb : List Sym) (k : KS LE) (hk : ∀ x, ι x ≠ k) :
    Function.update (Function.update B (ι (.inl a)) va) (ι (.inl b)) vb k = B k := by
  rw [Function.update_of_ne (fun h => hk _ h.symm), Function.update_of_ne (fun h => hk _ h.symm)]

/-- The rounding table with output `xd` (width `wI`, counter `cwI`). -/
def rhDTab : Fin 5 → KS LE := ![loc (.inr .xc), loc (.inr .xd), .inl .cwP, .inl .cwI, .inl .cq]

/-- The rounding table with output `xf` (width `wI + 1`, counter `cwI1`). -/
def rhFTab : Fin 5 → KS LE := ![loc (.inr .xc), loc (.inr .xf), .inl .cwP, .inl .cwI1, .inl .cq]

theorem rhDTab_injective : Function.Injective (rhDTab (LE := LE)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rhDTab, loc, dN]

theorem rhFTab_injective : Function.Injective (rhFTab (LE := LE)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rhFTab, loc, dN]

theorem rhDTab_ne (i : Fin 5) (e : LE) : rhDTab i ≠ .inr (.inr e) := by
  fin_cases i <;> simp [rhDTab, loc]

theorem rhFTab_ne (i : Fin 5) (e : LE) : rhFTab i ≠ .inr (.inr e) := by
  fin_cases i <;> simp [rhFTab, loc]

/-- Cost of one single-record rounding call (closed form). -/
def rhCost (wP w2 q : ℕ) : ℕ := (2 * wP + 1) + (2 * w2 + 1) + wP + w2 + bitLen q + 1

/-- A rounding call through a table `tab` (`xc` ↦ `out`, counters `cwP`, `cw`, `cq`). -/
theorem runs_rh_gen {Erh Rrh : Type} [Fintype Erh] [DecidableEq Erh] {irh : Erh → LE}
    (hirh : Function.Injective irh) (lrh : Lens σ Rrh) {Crh : ℕ}
    {Prh : Prog (KLoc (Fin 5) Erh) (fun _ => Sym) Rrh} (srh : RHSpec Erh Rrh Crh Prh)
    {tab : Fin 5 → KS LE} (htab : Function.Injective tab) (hne : ∀ i e, tab i ≠ .inr (.inr e))
    {out : SwW} {cw : SwN} (h0 : tab 0 = loc (.inr .xc)) (h1 : tab 1 = loc (.inr out))
    (h2 : tab 2 = .inl .cwP) (h3 : tab 3 = .inl cw) (h4 : tab 4 = .inl .cq)
    {base : KS LE → List Sym} {wP w2 q : ℕ} (hwP : 1 ≤ wP) (hw2 : 1 ≤ w2) {r2 r3 r4 : List Sym}
    (hb2 : base (.inl .cwP) = natSyms wP ++ r2) (hb3 : base (.inl cw) = natSyms w2 ++ r3)
    (hb4 : base (.inl .cq) = natSyms q ++ r4) (hcw : nD cw = none)
    (t2 : TermOK r2) (t3 : TermOK r3) (t4 : TermOK r4)
    (V : SwD ⊕ SwW → List Sym) {p : CInt} (hxc : V (.inr .xc) = carrSyms wP [[p]])
    (hp : FitsTwos wP p.1 ∧ FitsTwos wP p.2)
    (hr : FitsTwos w2 (roundHalfUpShiftC q p).1 ∧ FitsTwos w2 (roundHalfUpShiftC q p).2) :
    Runs (callInj (ιtab tab irh) lrh Prh) (mk base V)
      (mk base (Function.update (Function.update V (.inr .xc) []) (.inr out)
        (carrSyms w2 [[roundHalfUpShiftC q p]] ++ V (.inr out))))
      (fun _ => True) (Crh * rhCost wP w2 q) := by
  have hι := ιtab_injective htab hne hirh
  have key := srh wP w2 q [[p]] [] r2 r3 r4 (mk base V ∘ ιtab tab irh) hwP hw2
    (cArrFits_one hp) (by simpa [mapC] using cArrFits_one hr) blkTerm_nil' t2 t3 t4
    (by simp [ιtab, h0, hxc]) (by simp [ιtab, h2, hb2]) (by simp [ιtab, h3, hb3, hcw])
    (by simp [ιtab, h4, hb4])
  rw [← Function.update_comp_eq_of_injective _ hι, ← Function.update_comp_eq_of_injective _ hι]
    at key
  have hrun := runs_callInj hι lrh key (fun k hk => upd_out2 _ 0 1 _ _ k hk)
  have hcost : Crh * (cvol wP [[p]] + cvol w2 [[p]] + wP + w2 + bitLen q + 1) =
      Crh * rhCost wP w2 q := by
    simp [rhCost, cvol_one]
  refine WP.W9comp.runs_congr (hcost ▸ hrun) ?_
  simp [ιtab, h0, h1, update_mk, mapC]

theorem runs_rhD {Erh Rrh : Type} [Fintype Erh] [DecidableEq Erh] {irh : Erh → LE}
    (hirh : Function.Injective irh) (lrh : Lens σ Rrh) {Crh : ℕ}
    {Prh : Prog (KLoc (Fin 5) Erh) (fun _ => Sym) Rrh} (srh : RHSpec Erh Rrh Crh Prh)
    {base : KS LE → List Sym} {wP wI q : ℕ} (hwP : 1 ≤ wP) (hwI : 1 ≤ wI) {r2 r3 r4 : List Sym}
    (hb2 : base (.inl .cwP) = natSyms wP ++ r2) (hb3 : base (.inl .cwI) = natSyms wI ++ r3)
    (hb4 : base (.inl .cq) = natSyms q ++ r4) (t2 : TermOK r2) (t3 : TermOK r3) (t4 : TermOK r4)
    (V : SwD ⊕ SwW → List Sym) {p : CInt} (hxc : V (.inr .xc) = carrSyms wP [[p]])
    (hp : FitsTwos wP p.1 ∧ FitsTwos wP p.2)
    (hr : FitsTwos wI (roundHalfUpShiftC q p).1 ∧ FitsTwos wI (roundHalfUpShiftC q p).2) :
    Runs (callInj (ιtab rhDTab irh) lrh Prh) (mk base V)
      (mk base (Function.update (Function.update V (.inr .xc) []) (.inr .xd)
        (carrSyms wI [[roundHalfUpShiftC q p]] ++ V (.inr .xd))))
      (fun _ => True) (Crh * rhCost wP wI q) :=
  runs_rh_gen hirh lrh srh rhDTab_injective rhDTab_ne rfl rfl rfl rfl rfl hwP hwI hb2 hb3 hb4 rfl
    t2 t3 t4 V hxc hp hr

theorem runs_rhF {Erh Rrh : Type} [Fintype Erh] [DecidableEq Erh] {irh : Erh → LE}
    (hirh : Function.Injective irh) (lrh : Lens σ Rrh) {Crh : ℕ}
    {Prh : Prog (KLoc (Fin 5) Erh) (fun _ => Sym) Rrh} (srh : RHSpec Erh Rrh Crh Prh)
    {base : KS LE → List Sym} {wP wI q : ℕ} (hwP : 1 ≤ wP) {r2 r3 r4 : List Sym}
    (hb2 : base (.inl .cwP) = natSyms wP ++ r2) (hb3 : base (.inl .cwI1) = natSyms (wI + 1) ++ r3)
    (hb4 : base (.inl .cq) = natSyms q ++ r4) (t2 : TermOK r2) (t3 : TermOK r3) (t4 : TermOK r4)
    (V : SwD ⊕ SwW → List Sym) {p : CInt} (hxc : V (.inr .xc) = carrSyms wP [[p]])
    (hp : FitsTwos wP p.1 ∧ FitsTwos wP p.2)
    (hr : FitsTwos (wI + 1) (roundHalfUpShiftC q p).1 ∧
      FitsTwos (wI + 1) (roundHalfUpShiftC q p).2) :
    Runs (callInj (ιtab rhFTab irh) lrh Prh) (mk base V)
      (mk base (Function.update (Function.update V (.inr .xc) []) (.inr .xf)
        (carrSyms (wI + 1) [[roundHalfUpShiftC q p]] ++ V (.inr .xf))))
      (fun _ => True) (Crh * rhCost wP (wI + 1) q) :=
  runs_rh_gen hirh lrh srh rhFTab_injective rhFTab_ne rfl rfl rfl rfl rfl hwP (by omega) hb2 hb3
    hb4 rfl t2 t3 t4 V hxc hp hr

/-- The addition table: `xd` (width `wI`), `xf` (width `wI + 1`) → `xg` (width `wI`). -/
def caTab : Fin 6 → KS LE :=
  ![loc (.inr .xd), loc (.inr .xf), loc (.inr .xg), .inl .cwI, .inl .cwI1, .inl .cwI2]

theorem caTab_injective : Function.Injective (caTab (LE := LE)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [caTab, loc, dN]

theorem caTab_ne (i : Fin 6) (e : LE) : caTab i ≠ .inr (.inr e) := by
  fin_cases i <;> simp [caTab, loc]

/-- Cost of one single-record addition call (closed form). -/
def caCost (wI : ℕ) : ℕ := (2 * wI + 1) + (2 * (wI + 1) + 1) + (2 * wI + 1) + wI + (wI + 1) + wI + 1

theorem runs_ca {Eca Rca : Type} [Fintype Eca] [DecidableEq Eca] {ica : Eca → LE}
    (hica : Function.Injective ica) (lca : Lens σ Rca) {Cca : ℕ}
    {Pca : Prog (KLoc (Fin 6) Eca) (fun _ => Sym) Rca} (sca : CASpec Eca Rca Cca Pca)
    {base : KS LE → List Sym} {wI : ℕ} (hwI : 1 ≤ wI) {r3 r4 r5 : List Sym}
    (hb3 : base (.inl .cwI) = natSyms wI ++ r3) (hb4 : base (.inl .cwI1) = natSyms (wI + 1) ++ r4)
    (hb5 : base (.inl .cwI2) = natSyms wI ++ r5) (t3 : TermOK r3) (t4 : TermOK r4) (t5 : TermOK r5)
    (V : SwD ⊕ SwW → List Sym) {b r : CInt} (hxd : V (.inr .xd) = carrSyms wI [[b]])
    (hxf : V (.inr .xf) = carrSyms (wI + 1) [[r]]) (hb : FitsTwos wI b.1 ∧ FitsTwos wI b.2)
    (hr : FitsTwos (wI + 1) r.1 ∧ FitsTwos (wI + 1) r.2)
    (hs : FitsTwos wI (caddC b r).1 ∧ FitsTwos wI (caddC b r).2) :
    Runs (callInj (ιtab caTab ica) lca Pca) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inr .xd) []) (.inr .xf) [])
        (.inr .xg) (carrSyms wI [[caddC b r]] ++ V (.inr .xg))))
      (fun _ => True) (Cca * caCost wI) := by
  have hι := ιtab_injective (caTab_injective (LE := LE)) caTab_ne hica
  have key := sca wI (wI + 1) wI [[b]] [[r]] [] [] r3 r4 r5 (mk base V ∘ ιtab caTab ica) hwI
    (by omega) hwI (cArrFits_one hb) (cArrFits_one hr) (cAligned_one _ _)
    (by simpa [zipC] using cArrFits_one hs) blkTerm_nil' blkTerm_nil' t3 t4 t5
    (by simp [ιtab, caTab, hxd]) (by simp [ιtab, caTab, hxf]) (by simp [ιtab, caTab, hb3])
    (by simp [ιtab, caTab, hb4]) (by simp [ιtab, caTab, hb5])
  rw [← Function.update_comp_eq_of_injective _ hι, ← Function.update_comp_eq_of_injective _ hι,
    ← Function.update_comp_eq_of_injective _ hι] at key
  have hrun := runs_callInj hι lca key (fun k hk => upd_out _ 0 1 2 _ _ _ k hk)
  have hcost : Cca * (cvol wI [[b]] + cvol (wI + 1) [[r]] + cvol wI [[b]] + wI + (wI + 1) + wI + 1) =
      Cca * caCost wI := by
    simp [caCost, cvol_one]
  refine WP.W9comp.runs_congr (hcost ▸ hrun) ?_
  simp [ιtab, caTab, update_mk, zipC]

end Calls

end SubNLogN.Machine.Bridge.SolveAux
