/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockE
import SubNLogN.Machine.Calculus.Adapters

/-!
# K5 spreading: the block step with `mulBig` (`Bridge/SpreadRunsBlk.lean`)

The block step as a `Runs` fact in any register type `σ` with lenses to the AR registers and to
`mulBig`'s registers: pack the block (`PackDataStmt`'s program), the sixteen partial products
(`mulBig`), then `postBlk`. `block_runs` gives the exact final stacks (`fOut`) and the loop flag
(the next record of the extended line). Everything is proved; the packer, the slot pass and
`mulBig` enter through their specifications.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith SubNLogN.Machine.Calculus
  Computability

/-- `Runs` of a lifted AR program from bounded evaluations from every register. -/
theorem runs_liftA {K σ : Type} [DecidableEq K] (l : Lens σ AReg) {p : AProg K} (hp : p.Closed)
    {S S' : K → List Sym} {T : ℕ} {Q : AReg → Prop}
    (h : ∀ v, ∃ w t, Eval [] p ⟨v, S⟩ ⟨w, S'⟩ t ∧ t ≤ T ∧ Q w) :
    Runs (p.liftRegs l) S S' (fun x => Q (l.get x)) T := by
  have hr : Runs p S S' Q T := by
    intro st hst
    obtain ⟨v, stk⟩ := st
    change stk = S at hst
    subst hst
    obtain ⟨w, t, e, ht, hq⟩ := h v
    exact ⟨_, t, e, ⟨rfl, hq⟩, ht⟩
  exact RunsIn.iff_runs.mp (RunsIn.of_runs_liftRegs l hr hp [])

/-- The specification part of `PackDataStmt` for a program and a constant. -/
def PackSpecOf (prog : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K) (C : ℕ) : Prop :=
  ∀ (K : Type) [DecidableEq K] (ι : PackRole → K), Function.Injective ι →
  ∀ (W w s : ℕ) (B : List CInt) (rest DW Dlo Dpad : List Sym) (S : K → List Sym) (v : AReg),
    1 ≤ w → w ≤ s → B.length ≤ W → (B.length < W → TermOK rest) →
    (∀ x ∈ B, FitsTwos w x.1 ∧ FitsTwos w x.2) →
    DW.head? ≠ some .mark → Dlo.head? ≠ some .mark → Dpad.head? ≠ some .mark →
    S (ι .src) = carrSyms w (B.map fun x => [x]) ++ rest →
    S (ι .RW) = List.replicate W .mark ++ DW →
    S (ι .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
    S (ι .Rpad) = List.replicate (s - w) .mark ++ Dpad →
    (∀ j, S (ι (.tmp j)) = []) →
    ∃ (v' : AReg) (S' : K → List Sym) (c : ℕ), Eval [] (prog K ι) ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ C * (W * (s + 1) + 1) ∧
      S' (ι .src) = rest ∧
      (∀ k, S' (ι (.out k)) = natSyms (pack s (B.map (cpart w k))) ++ S (ι (.out k))) ∧
      S' (ι .M) = List.replicate B.length .mark ++ S (ι .M) ∧
      ∀ k, k ≠ ι .src → (∀ j, k ≠ ι (.out j)) → k ≠ ι .M → S' k = S k

/-- The block fields after packing. -/
def BF.packed (f : BF) (es' : List Sym) (d' : Fin 4 → List Sym) (mm' : ℕ) : BF :=
  { f with es := es', d := d', mm := mm' }

/-- Replace the real product streams. -/
def BF.setZr (f : BF) (z : Fin 8 → List Sym) : BF := { f with zr := z }

/-- Replace the imaginary product streams. -/
def BF.setZi (f : BF) (z : Fin 8 → List Sym) : BF := { f with zi := z }

/-- The block fields at rest (between block steps). -/
def fRest (es tre tim q : List Sym) : BF where
  zr := fun _ => []
  zi := fun _ => []
  tre := tre
  tim := tim
  mm := 0
  q := q
  vre := []
  vim := []
  ntre := []
  ntim := []
  d := fun _ => []
  es := es

variable {Esu : Type} [DecidableEq Esu]

theorem packData_eval {pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K} {Cpd : ℕ}
    (hpd : PackSpecOf pdp Cpd) (W wI s : ℕ) (B : List CInt) (Erest : List Sym)
    (S0 : SK Esu → List Sym) (f : BF) (v : AReg) (h1 : 1 ≤ wI) (h2 : wI ≤ s)
    (hBW : B.length ≤ W) (hrest : B.length < W → TermOK Erest)
    (hfit : ∀ x ∈ B, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hes : f.es = carrSyms wI (B.map fun x => [x]) ++ Erest) (hd : f.d = fun _ => [])
    (hmm : f.mm = 0) (hRW : S0 (sp (.ru .W)) = List.replicate W .mark)
    (hRlo : S0 (sp (.ru .wI1)) = List.replicate (wI - 1) .mark)
    (hRpad : S0 (sp (.ru .sWI)) = List.replicate (s - wI) .mark)
    (htmp : ∀ j, S0 (sp (.tmp j)) = []) :
    ∃ w t, Eval [] (pdp (SK Esu) ιPD) ⟨v, bst S0 f⟩
      ⟨w, bst S0 (f.packed Erest (fun k => natSyms (pack s (B.map (cpart wI k)))) B.length)⟩ t ∧
      t ≤ Cpd * (W * (s + 1) + 1) ∧ True := by
  obtain ⟨v', S', c, e, hc, hsrc, hout, hM, hfr⟩ := hpd (SK Esu) ιPD ιPD_injective W wI s B
    Erest [] [] [] (bst S0 f) v h1 h2 hBW hrest hfit (by simp) (by simp) (by simp)
    (by show f.es = _; exact hes) (by show S0 _ = _; rw [hRW, List.append_nil])
    (by show S0 _ = _; rw [hRlo, List.append_nil]) (by show S0 _ = _; rw [hRpad, List.append_nil])
    (fun j => htmp j)
  have hS' : S' = bst S0 (f.packed Erest (fun k => natSyms (pack s (B.map (cpart wI k))))
      B.length) := by
    funext k
    by_cases hk1 : k = sp .Es
    · subst hk1; exact hsrc
    by_cases hk2 : ∃ j, k = sp (.D j)
    · obtain ⟨j, rfl⟩ := hk2
      rw [show sp (Esu := Esu) (.D j) = ιPD (.out j) from rfl, hout]
      show _ ++ f.d j = _
      rw [hd, List.append_nil]; rfl
    by_cases hk3 : k = sp .M
    · subst hk3
      rw [show sp (Esu := Esu) .M = ιPD .M from rfl, hM]
      show _ ++ List.replicate f.mm _ = _
      rw [hmm, List.replicate_zero, List.append_nil]; rfl
    push_neg at hk2
    rw [hfr k hk1 (fun j h => hk2 j h) hk3]
    rcases k with k | (x | e)
    · rfl
    · cases x <;> first | rfl | exact absurd rfl hk1 | exact absurd rfl hk3 | exact absurd rfl (hk2 _)
    · rfl
  exact ⟨v', c, hS' ▸ e, hc, trivial⟩

/-! ## The sixteen partial products -/

variable {σ Rm : Type}

/-- The real partial products `Zr j := D a · F b` (`(a, b) = rePairs j`) for `j ∈ l`. -/
def mulRe (lM : Lens σ Rm) (Pm : Prog MBLoc (fun _ => Sym) Rm) :
    List (Fin 8) → Prog (SK Esu) (fun _ => Sym) σ
  | [] => .load id
  | j :: l => .seq (callInj (ιMB (rePairs j).1 (rePairs j).2 (.Zr j)) lM Pm) (mulRe lM Pm l)

/-- The imaginary partial products `Zi j := D a · F b` (`(a, b) = imPairs j`) for `j ∈ l`. -/
def mulIm (lM : Lens σ Rm) (Pm : Prog MBLoc (fun _ => Sym) Rm) :
    List (Fin 8) → Prog (SK Esu) (fun _ => Sym) σ
  | [] => .load id
  | j :: l => .seq (callInj (ιMB (imPairs j).1 (imPairs j).2 (.Zi j)) lM Pm) (mulIm lM Pm l)

theorem runs_loadId (S : SK Esu → List Sym) :
    Runs (Prog.load (K := SK Esu) (Γ := fun _ => Sym) (σ := σ) id) S S (fun _ => True) 1 := by
  intro st hst
  exact ⟨⟨id st.var, st.stk⟩, 1, Eval.load [] id st.var st.stk, ⟨hst, trivial⟩, le_rfl⟩

theorem mulRe_runs {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ} (hcl : Pm.Closed)
    (hspec : SpecMulBig Pm Cm) (lM : Lens σ Rm) (dv gv : Fin 4 → ℕ) (MB : ℕ)
    (hMB : ∀ a b, mulBigBound (dv a) (gv b) ≤ MB) (S0 : SK Esu → List Sym)
    (hF : ∀ b, S0 (sp (.F b)) = natSyms (gv b)) (hmb : ∀ g, S0 (sp (.mb g)) = []) :
    ∀ (l : List (Fin 8)) (f : BF), l.Nodup → (∀ a, f.d a = natSyms (dv a)) →
      (∀ j ∈ l, f.zr j = []) →
      Runs (mulRe lM Pm l) (bst S0 f)
        (bst S0 (f.setZr (fun j => if j ∈ l then natSyms (dv (rePairs j).1 * gv (rePairs j).2)
          else f.zr j))) (fun _ => True) (l.length * (Cm * MB) + 1)
  | [], f, _, _, _ => by
    have hf : f.setZr (fun j => if j ∈ ([] : List (Fin 8)) then
        natSyms (dv (rePairs j).1 * gv (rePairs j).2) else f.zr j) = f := by
      cases f; simp [BF.setZr]
    rw [hf]
    simpa [mulRe, mulIm] using runs_loadId (σ := σ) (bst S0 f)
  | j :: l, f, hnd, hd, hz => by
    have h1 := RunsIn.mulBig hcl hspec (ιMB_injective (Esu := Esu) (rePairs j).1 (rePairs j).2
      (z := .Zr j) (by simp) (by simp) (by simp)) lM (dv (rePairs j).1) (gv (rePairs j).2) [] [] []
      (bst S0 f) TermOK.nil TermOK.nil
      (by show f.d _ = _; rw [hd, List.append_nil])
      (by show S0 (sp (.F _)) = _; rw [hF, List.append_nil])
      (by show f.zr j = _; exact hz j (List.mem_cons_self ..))
      (fun g => by show S0 _ = _; exact hmb g) []
    have hι2 : ιMB (Esu := Esu) (rePairs j).1 (rePairs j).2 (.Zr j) (.inl 2) = sp (.Zr j) := rfl
    rw [hι2, List.append_nil, bst_upd_zr] at h1
    have hnd' := List.nodup_cons.mp hnd
    have h2 := mulRe_runs hcl hspec lM dv gv MB hMB S0 hF hmb l
      { f with zr := Function.update f.zr j (natSyms (dv (rePairs j).1 * gv (rePairs j).2)) }
      hnd'.2 hd (fun j' hj' => by
        have hne : j' ≠ j := fun h => hnd'.1 (h ▸ hj')
        show Function.update f.zr j _ j' = _
        rw [Function.update_of_ne hne]
        exact hz j' (List.mem_cons_of_mem _ hj'))
    have h12 := RunsIn.seq h1 (RunsIn.iff_runs.mpr h2)
    refine RunsIn.iff_runs.mp (RunsIn.congr h12 ?_ ?_)
    · congr 1
      simp only [BF.setZr]
      congr 1
      funext j'
      by_cases hj : j' = j
      · subst hj; simp [hnd'.1]
      · simp [hj, Function.update_of_ne hj]
    · have := hMB (rePairs j).1 (rePairs j).2
      rw [List.length_cons, Nat.add_mul, one_mul]
      have := Nat.mul_le_mul_left Cm this
      omega

theorem mulIm_runs {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ} (hcl : Pm.Closed)
    (hspec : SpecMulBig Pm Cm) (lM : Lens σ Rm) (dv gv : Fin 4 → ℕ) (MB : ℕ)
    (hMB : ∀ a b, mulBigBound (dv a) (gv b) ≤ MB) (S0 : SK Esu → List Sym)
    (hF : ∀ b, S0 (sp (.F b)) = natSyms (gv b)) (hmb : ∀ g, S0 (sp (.mb g)) = []) :
    ∀ (l : List (Fin 8)) (f : BF), l.Nodup → (∀ a, f.d a = natSyms (dv a)) →
      (∀ j ∈ l, f.zi j = []) →
      Runs (mulIm lM Pm l) (bst S0 f)
        (bst S0 (f.setZi (fun j => if j ∈ l then natSyms (dv (imPairs j).1 * gv (imPairs j).2)
          else f.zi j))) (fun _ => True) (l.length * (Cm * MB) + 1)
  | [], f, _, _, _ => by
    have hf : f.setZi (fun j => if j ∈ ([] : List (Fin 8)) then
        natSyms (dv (imPairs j).1 * gv (imPairs j).2) else f.zi j) = f := by
      cases f; simp [BF.setZi]
    rw [hf]
    simpa [mulRe, mulIm] using runs_loadId (σ := σ) (bst S0 f)
  | j :: l, f, hnd, hd, hz => by
    have h1 := RunsIn.mulBig hcl hspec (ιMB_injective (Esu := Esu) (imPairs j).1 (imPairs j).2
      (z := .Zi j) (by simp) (by simp) (by simp)) lM (dv (imPairs j).1) (gv (imPairs j).2) [] [] []
      (bst S0 f) TermOK.nil TermOK.nil
      (by show f.d _ = _; rw [hd, List.append_nil])
      (by show S0 (sp (.F _)) = _; rw [hF, List.append_nil])
      (by show f.zi j = _; exact hz j (List.mem_cons_self ..))
      (fun g => by show S0 _ = _; exact hmb g) []
    have hι2 : ιMB (Esu := Esu) (imPairs j).1 (imPairs j).2 (.Zi j) (.inl 2) = sp (.Zi j) := rfl
    rw [hι2, List.append_nil, bst_upd_zi] at h1
    have hnd' := List.nodup_cons.mp hnd
    have h2 := mulIm_runs hcl hspec lM dv gv MB hMB S0 hF hmb l
      { f with zi := Function.update f.zi j (natSyms (dv (imPairs j).1 * gv (imPairs j).2)) }
      hnd'.2 hd (fun j' hj' => by
        have hne : j' ≠ j := fun h => hnd'.1 (h ▸ hj')
        show Function.update f.zi j _ j' = _
        rw [Function.update_of_ne hne]
        exact hz j' (List.mem_cons_of_mem _ hj'))
    have h12 := RunsIn.seq h1 (RunsIn.iff_runs.mpr h2)
    refine RunsIn.iff_runs.mp (RunsIn.congr h12 ?_ ?_)
    · congr 1
      simp only [BF.setZi]
      congr 1
      funext j'
      by_cases hj : j' = j
      · subst hj; simp [hnd'.1]
      · simp [hj, Function.update_of_ne hj]
    · have := hMB (imPairs j).1 (imPairs j).2
      rw [List.length_cons, Nat.add_mul, one_mul]
      have := Nat.mul_le_mul_left Cm this
      omega

end SubNLogN.Machine.Bridge.SpreadAux
