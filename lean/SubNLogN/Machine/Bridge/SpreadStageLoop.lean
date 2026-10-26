/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadStageBase
import SubNLogN.Machine.Bridge.SpreadStageInner
import SubNLogN.Machine.Bridge.SpreadPackMath
import IntMulTM.SpecFacts

/-!
# K5 spreading, stage loop: the double loop (`Bridge/SpreadStageLoop.lean`)

The double loop of one spreading stage: for each of the `A` tap records of the axis block on
`tapTab` (ruler `ru A`, walk temporary `X 3`), pack it (`PackFilterStmt`, roles `ιPF`: parts on
`F k`, restore copy on `TR`), run the line step (`SpreadLineStmt`) on the next `rep` lines of
`arr` (ruler `ru rep`, walk temporary `X 4`), and drain the packed parts.

`runs_groupLoop` (the interface consumed by `Bridge/SpreadStageMain.lean`): from a state `B` with
the stage rulers, empty line scratch, the input lines `xs` on `arr` and the axis block `tb` on
`tapTab`, the loop leaves `arr := rarr`, the outputs `stageOuts …` (reversed symbol order) on
`Out`, the tap block consumed onto `TR` (reversed), every other stack unchanged.

**Scope (honest summary).** Definitions, and the statement `runs_groupLoop`. Helpers live in
`SubNLogN.Machine.Bridge.SpreadAux.Stage`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.Stage

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Math.Common SubNLogN.Math.Bridge

variable {Es σ : Type} [DecidableEq Es]

/-- The specification of `PackFilterStmt` for one program on `SK Es` with the roles `ιPF`
(`hspec (SK Es) ιPF ιPF_injective` has this type). -/
def PFSpec (PF : AProg (SK Es)) (CF : ℕ) : Prop :=
  ∀ (w s : ℕ) (F : List CInt) (rest Dlo Dpad : List Sym) (S : SK Es → List Sym) (v : AReg),
    1 ≤ w → w ≤ s → (∀ x ∈ F, FitsTwos w x.1 ∧ FitsTwos w x.2) →
    Dlo.head? ≠ some .mark → Dpad.head? ≠ some .mark →
    S (ιPF .src) = carrSyms w [F] ++ rest →
    S (ιPF .Rlo) = List.replicate (w - 1) .mark ++ Dlo →
    S (ιPF .Rpad) = List.replicate (s - w) .mark ++ Dpad →
    (∀ j, S (ιPF (.tmp j)) = []) →
    ∃ (v' : AReg) (S' : SK Es → List Sym) (c : ℕ), Eval [] PF ⟨v, S⟩ ⟨v', S'⟩ c ∧
      c ≤ CF * (F.length * (s + 1) + 1) ∧
      S' (ιPF .src) = rest ∧
      S' (ιPF .tr) = (carrSyms w [F]).reverse ++ S (ιPF .tr) ∧
      (∀ k, S' (ιPF (.out k)) = natSyms (pack s (F.reverse.map (cpart w k))) ++ S (ιPF (.out k))) ∧
      ∀ k, k ≠ ιPF .src → k ≠ ιPF .tr → (∀ j, k ≠ ιPF (.out j)) → S' k = S k

/-- Drain the four packed filter parts. -/
def drainF : AProg (SK Es) :=
  .seq (dropAll (sp (.F 0))) (.seq (dropAll (sp (.F 1))) (.seq (dropAll (sp (.F 2)))
    (dropAll (sp (.F 3)))))

/-- One group: pack the next tap record, run the `rep` lines of the group (`lineWalk`), drain the
parts. -/
def gBody (lA : Lens σ AReg) (PF : AProg (SK Es)) (PL : Prog (SK Es) (fun _ => Sym) σ) :
    Prog (SK Es) (fun _ => Sym) σ :=
  .seq (ar lA PF) (.seq (lineWalk lA PL) (ar lA drainF))

/-- **The stage double loop**: one group per mark of `ru A`. -/
def groupLoop (lA : Lens σ AReg) (PF : AProg (SK Es)) (PL : Prog (SK Es) (fun _ => Sym) σ) :
    Prog (SK Es) (fun _ => Sym) σ :=
  .seq (walkL lA (sp (.ru .A)) (sp (.X 3)) (gBody lA PF PL))
    (ar lA (moveMarks (sp (.X 3)) (sp (.ru .A))))

/-- The outputs of the stage: line `l` (entries `l·t, …, l·t + t - 1` of `xs`) with the tap record
`l / rep` of `tb`, for `l < L`. -/
def stageOuts (q t W a0 rep : ℕ) (xs : List CInt) (tb : List (List CInt)) (L : ℕ) : List CInt :=
  (List.range L).flatMap fun l => lineOut q t W a0 ((xs.drop (l * t)).take t) (tb.getD (l / rep) [])

/-- Cost of one group (packing, `rep` line steps, walk, drains). -/
def grpCost (CF CL s t W rep : ℕ) : ℕ :=
  CF * (W * (s + 1) + 1) + rep * (CL * lineCost s t W + 4) + 4 * rep + 12 * (s * W) + 40

theorem closed_drainF : (drainF (Es := Es)).Closed := by
  unfold drainF
  exact closed_seq' (closed_dropAll _) (closed_seq' (closed_dropAll _) (closed_seq'
    (closed_dropAll _) (closed_dropAll _)))

theorem closed_groupLoop (lA : Lens σ AReg) {PF : AProg (SK Es)}
    {PL : Prog (SK Es) (fun _ => Sym) σ} (hPF : PF.Closed) (hPL : PL.Closed) :
    (groupLoop lA PF PL).Closed := by
  have hmm : ∀ X R : SK Es, (ar lA (moveMarks X R)).Closed := fun X R =>
    closed_ar lA (by simp [Prog.Closed, Prog.FreeBelow, moveMarks, mmLoop, peekR, drop1, pushS])
  have hlw : (lineWalk lA PL).Closed := by
    unfold lineWalk
    exact closed_seq' (closed_walkL lA _ _ hPL) (hmm _ _)
  unfold groupLoop gBody
  exact closed_seq' (closed_walkL lA _ _ (closed_seq' (closed_ar lA hPF)
    (closed_seq' hlw (closed_ar lA closed_drainF)))) (hmm _ _)

/-! ## List and size facts -/

theorem carr_append (w : ℕ) (u v : List (List CInt)) :
    carrSyms w (u ++ v) = carrSyms w u ++ carrSyms w v := by
  simp [carrSyms, arrSyms, blk]

theorem carr_nil (w : ℕ) : carrSyms w [] = [] := by
  simp [carrSyms, arrSyms, blk]

theorem tb_drop (tb : List (List CInt)) (g : ℕ) (hg : g < tb.length) :
    tb.drop g = tb.getD g [] :: tb.drop (g + 1) := by
  rw [List.drop_eq_getElem_cons hg]
  simp [List.getD, List.getElem?_eq_getElem hg]

theorem tb_take (tb : List (List CInt)) (g : ℕ) (hg : g < tb.length) :
    tb.take (g + 1) = tb.take g ++ [tb.getD g []] := by
  rw [List.take_succ]
  simp [List.getD, List.getElem?_eq_getElem hg]

theorem len_natSyms (n : ℕ) : (natSyms n).length = Nat.size n := by
  simp [natSyms, IntMulTM.length_encodeNat]

theorem len_pk (s wT : ℕ) (F : List CInt) (k : Fin 4) (hw : 1 ≤ wT) (hws : wT ≤ s) :
    (natSyms (pack s (F.reverse.map (cpart wT k)))).length ≤ s * F.length := by
  rw [len_natSyms]
  have h := pack_lt s (F.reverse.map (cpart wT k)) (by
    intro d hd
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    exact SpreadPackAux.cpart_lt hw hws k x)
  rw [List.length_map, List.length_reverse] at h
  exact Nat.size_le.2 h

theorem stageOuts_grp (q t W a0 rep : ℕ) (xs : List CInt) (tb : List (List CInt)) (g : ℕ) :
    stageOuts q t W a0 rep xs tb (g * rep + rep) =
      stageOuts q t W a0 rep xs tb (g * rep) ++ grpOuts q t W a0 xs (tb.getD g []) (g * rep) rep := by
  unfold stageOuts grpOuts
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  rw [List.flatMap, List.flatMap]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  have : (g * rep + j) / rep = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  simp only [this]

theorem stageOuts_mono (q t W a0 rep : ℕ) (xs : List CInt) (tb : List (List CInt)) {m n : ℕ}
    (h : m ≤ n) {y : CInt} (hy : y ∈ stageOuts q t W a0 rep xs tb m) :
    y ∈ stageOuts q t W a0 rep xs tb n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold stageOuts at hy ⊢
  rw [List.range_add, List.flatMap_append]
  exact List.mem_append_left _ hy

theorem xs_split (xs : List CInt) (t l : ℕ) :
    xs.drop (l * t) = (xs.drop (l * t)).take t ++ xs.drop ((l + 1) * t) := by
  conv_lhs => rw [← List.take_append_drop t (xs.drop (l * t))]
  rw [List.drop_drop, Nat.add_mul, Nat.one_mul]

/-! ## Loop states -/

/-- The stacks touched by the double loop. -/
structure LF where
  arr : List Sym
  out : List Sym
  tap : List Sym
  tr : List Sym
  f0 : List Sym
  f1 : List Sym
  f2 : List Sym
  f3 : List Sym
  x3 : List Sym
  x4 : List Sym
  rA : List Sym
  rR : List Sym

/-- A loop state: the fields `f` over the base state `B`. -/
def lst (B : SK Es → List Sym) (f : LF) : SK Es → List Sym := fun k =>
  if k = kW .arr then f.arr else
  if k = sp .Out then f.out else
  if k = kN .tapTab then f.tap else
  if k = sp .TR then f.tr else
  if k = sp (.F 0) then f.f0 else
  if k = sp (.F 1) then f.f1 else
  if k = sp (.F 2) then f.f2 else
  if k = sp (.F 3) then f.f3 else
  if k = sp (.X 3) then f.x3 else
  if k = sp (.X 4) then f.x4 else
  if k = sp (.ru .A) then f.rA else
  if k = sp (.ru .rep) then f.rR else B k

section LstLemmas

variable (B : SK Es → List Sym) (f : LF) (y : List Sym)

theorem lst_upd_arr : Function.update (lst B f) (kW .arr) y = lst B { f with arr := y } := by
  funext k; by_cases h : k = kW .arr
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_out : Function.update (lst B f) (sp .Out) y = lst B { f with out := y } := by
  funext k; by_cases h : k = sp .Out
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_tap : Function.update (lst B f) (kN .tapTab) y = lst B { f with tap := y } := by
  funext k; by_cases h : k = kN .tapTab
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_tr : Function.update (lst B f) (sp .TR) y = lst B { f with tr := y } := by
  funext k; by_cases h : k = sp .TR
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_f0 : Function.update (lst B f) (sp (.F 0)) y = lst B { f with f0 := y } := by
  funext k; by_cases h : k = sp (.F 0)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_f1 : Function.update (lst B f) (sp (.F 1)) y = lst B { f with f1 := y } := by
  funext k; by_cases h : k = sp (.F 1)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_f2 : Function.update (lst B f) (sp (.F 2)) y = lst B { f with f2 := y } := by
  funext k; by_cases h : k = sp (.F 2)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_f3 : Function.update (lst B f) (sp (.F 3)) y = lst B { f with f3 := y } := by
  funext k; by_cases h : k = sp (.F 3)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_x3 : Function.update (lst B f) (sp (.X 3)) y = lst B { f with x3 := y } := by
  funext k; by_cases h : k = sp (.X 3)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_x4 : Function.update (lst B f) (sp (.X 4)) y = lst B { f with x4 := y } := by
  funext k; by_cases h : k = sp (.X 4)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_rA : Function.update (lst B f) (sp (.ru .A)) y = lst B { f with rA := y } := by
  funext k; by_cases h : k = sp (.ru .A)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

theorem lst_upd_rR : Function.update (lst B f) (sp (.ru .rep)) y = lst B { f with rR := y } := by
  funext k; by_cases h : k = sp (.ru .rep)
  · subst h; simp [lst]
  · simp [lst, Function.update_of_ne h, h]

/-- Line scratch is read from the base state. -/
theorem lst_ls {x : SpS} (hx : LineScratch x) : lst B f (sp x) = B (sp x) := by
  unfold LineScratch at hx
  rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [lst]

end LstLemmas

section LstGet

variable (B : SK Es → List Sym) (f : LF)

@[simp] theorem lst_arr : lst B f (kW .arr) = f.arr := by simp [lst]
@[simp] theorem lst_out : lst B f (sp .Out) = f.out := by simp [lst]
@[simp] theorem lst_tap : lst B f (kN .tapTab) = f.tap := by simp [lst]
@[simp] theorem lst_tr : lst B f (sp .TR) = f.tr := by simp [lst]
@[simp] theorem lst_f0 : lst B f (sp (.F 0)) = f.f0 := by simp [lst]
@[simp] theorem lst_f1 : lst B f (sp (.F 1)) = f.f1 := by simp [lst]
@[simp] theorem lst_f2 : lst B f (sp (.F 2)) = f.f2 := by simp [lst]
@[simp] theorem lst_f3 : lst B f (sp (.F 3)) = f.f3 := by simp [lst]
@[simp] theorem lst_x3 : lst B f (sp (.X 3)) = f.x3 := by simp [lst]
@[simp] theorem lst_x4 : lst B f (sp (.X 4)) = f.x4 := by simp [lst]
@[simp] theorem lst_rA : lst B f (sp (.ru .A)) = f.rA := by simp [lst]
@[simp] theorem lst_rR : lst B f (sp (.ru .rep)) = f.rR := by simp [lst]

theorem lst_congr {f f' : LF} (h1 : f.arr = f'.arr) (h2 : f.out = f'.out)
    (h3 : f.tap = f'.tap) (h4 : f.tr = f'.tr) (h5 : f.f0 = f'.f0) (h6 : f.f1 = f'.f1)
    (h7 : f.f2 = f'.f2) (h8 : f.f3 = f'.f3) (h9 : f.x3 = f'.x3) (h10 : f.x4 = f'.x4)
    (h11 : f.rA = f'.rA) (h12 : f.rR = f'.rR) : lst B f = lst B f' := by
  unfold lst
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end LstGet

/-! ## Packing and draining on loop states -/

/-- The fields after packing the tap record `F` (`PackFilterStmt`). -/
def pfRec (f : LF) (wT s : ℕ) (F : List CInt) (rest : List Sym) : LF :=
  { f with
    tap := rest
    tr := (carrSyms wT [F]).reverse ++ f.tr
    f0 := natSyms (pack s (F.reverse.map (cpart wT 0))) ++ f.f0
    f1 := natSyms (pack s (F.reverse.map (cpart wT 1))) ++ f.f1
    f2 := natSyms (pack s (F.reverse.map (cpart wT 2))) ++ f.f2
    f3 := natSyms (pack s (F.reverse.map (cpart wT 3))) ++ f.f3 }

theorem runs_pf (lA : Lens σ AReg) {PF : AProg (SK Es)} {CF : ℕ} (hPF : PFSpec PF CF)
    (B : SK Es → List Sym) (f : LF) (wT s : ℕ) (F : List CInt) (rest : List Sym)
    (hw : 1 ≤ wT) (hws : wT ≤ s) (hF : ∀ x ∈ F, FitsTwos wT x.1 ∧ FitsTwos wT x.2)
    (htap : f.tap = carrSyms wT [F] ++ rest)
    (hlo : B (sp (.ru .wT1)) = List.replicate (wT - 1) .mark)
    (hpad : B (sp (.ru .sWT)) = List.replicate (s - wT) .mark)
    (htmp : ∀ j, B (sp (.tmp j)) = []) :
    Runs (ar lA PF) (lst B f) (lst B (pfRec f wT s F rest))
      (fun _ => True) (CF * (F.length * (s + 1) + 1)) := by
  refine runs_ar lA (Q := fun _ => True) (Runs.of_eval fun v => ?_)
  obtain ⟨v', S', c, e, hc, hsrc, htr, hout, hrest⟩ := hPF wT s F rest [] [] (lst B f) v hw hws hF
    (by simp) (by simp) (by simp [ιPF, htap]) (by simp [ιPF, lst, hlo])
    (by simp [ιPF, lst, hpad]) (fun j => by simp [ιPF, lst, htmp])
  refine ⟨v', c, ?_, trivial, hc⟩
  have key : S' = lst B (pfRec f wT s F rest) := by
    funext k
    by_cases h1 : k = kN .tapTab
    · subst h1; exact hsrc.trans (by simp [pfRec])
    by_cases h2 : k = sp .TR
    · subst h2; exact htr.trans (by simp [ιPF, pfRec])
    by_cases h3 : k = sp (.F 0)
    · subst h3; exact (hout 0).trans (by simp [ιPF, pfRec])
    by_cases h4 : k = sp (.F 1)
    · subst h4; exact (hout 1).trans (by simp [ιPF, pfRec])
    by_cases h5 : k = sp (.F 2)
    · subst h5; exact (hout 2).trans (by simp [ιPF, pfRec])
    by_cases h6 : k = sp (.F 3)
    · subst h6; exact (hout 3).trans (by simp [ιPF, pfRec])
    have hFj : ∀ j, k ≠ ιPF (.out j) := by
      intro j
      fin_cases j
      · exact h3
      · exact h4
      · exact h5
      · exact h6
    rw [hrest k h1 h2 hFj]
    simp [lst, pfRec, h1, h2, h3, h4, h5, h6]
  rw [← key]
  exact e

theorem runs_drainF (lA : Lens σ AReg) (B : SK Es → List Sym) (f : LF) :
    Runs (ar lA drainF) (lst B f) (lst B { f with f0 := [], f1 := [], f2 := [], f3 := [] })
      (fun _ => True)
      (3 * f.f0.length + 3 * f.f1.length + 3 * f.f2.length + 3 * f.f3.length + 8) := by
  apply runs_ar lA (Q := fun _ => True)
  have h0 := runs_dropAll (sp (.F 0) : SK Es) (lst B f)
  rw [lst_upd_f0, lst_f0] at h0
  have h1 := runs_dropAll (sp (.F 1) : SK Es) (lst B { f with f0 := [] })
  rw [lst_upd_f1, lst_f1] at h1
  have h2 := runs_dropAll (sp (.F 2) : SK Es) (lst B { f with f0 := [], f1 := [] })
  rw [lst_upd_f2, lst_f2] at h2
  have h3 := runs_dropAll (sp (.F 3) : SK Es) (lst B { f with f0 := [], f1 := [], f2 := [] })
  rw [lst_upd_f3, lst_f3] at h3
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h0 (WP.W9comp.runs_seq h1
    (WP.W9comp.runs_seq h2 h3))) (fun _ _ => trivial) ?_
  simp only
  omega

theorem lst_eq_of (B B' : SK Es → List Sym) (f : LF)
    (h1 : B' (kW .arr) = f.arr) (h2 : B' (sp .Out) = f.out) (h3 : B' (kN .tapTab) = f.tap)
    (h4 : B' (sp .TR) = f.tr) (h5 : B' (sp (.F 0)) = f.f0) (h6 : B' (sp (.F 1)) = f.f1)
    (h7 : B' (sp (.F 2)) = f.f2) (h8 : B' (sp (.F 3)) = f.f3) (h9 : B' (sp (.X 3)) = f.x3)
    (h10 : B' (sp (.X 4)) = f.x4) (h11 : B' (sp (.ru .A)) = f.rA)
    (h12 : B' (sp (.ru .rep)) = f.rR)
    (hrest : ∀ k, k ≠ kW .arr → k ≠ sp .Out → k ≠ kN .tapTab → k ≠ sp .TR →
      k ≠ sp (.F 0) → k ≠ sp (.F 1) → k ≠ sp (.F 2) → k ≠ sp (.F 3) → k ≠ sp (.X 3) →
      k ≠ sp (.X 4) → k ≠ sp (.ru .A) → k ≠ sp (.ru .rep) → B' k = B k) :
    lst B f = B' := by
  funext k
  unfold lst
  by_cases c1 : k = kW .arr
  · rw [if_pos c1, c1, h1]
  rw [if_neg c1]
  by_cases c2 : k = sp .Out
  · rw [if_pos c2, c2, h2]
  rw [if_neg c2]
  by_cases c3 : k = kN .tapTab
  · rw [if_pos c3, c3, h3]
  rw [if_neg c3]
  by_cases c4 : k = sp .TR
  · rw [if_pos c4, c4, h4]
  rw [if_neg c4]
  by_cases c5 : k = sp (.F 0)
  · rw [if_pos c5, c5, h5]
  rw [if_neg c5]
  by_cases c6 : k = sp (.F 1)
  · rw [if_pos c6, c6, h6]
  rw [if_neg c6]
  by_cases c7 : k = sp (.F 2)
  · rw [if_pos c7, c7, h7]
  rw [if_neg c7]
  by_cases c8 : k = sp (.F 3)
  · rw [if_pos c8, c8, h8]
  rw [if_neg c8]
  by_cases c9 : k = sp (.X 3)
  · rw [if_pos c9, c9, h9]
  rw [if_neg c9]
  by_cases c10 : k = sp (.X 4)
  · rw [if_pos c10, c10, h10]
  rw [if_neg c10]
  by_cases c11 : k = sp (.ru .A)
  · rw [if_pos c11, c11, h11]
  rw [if_neg c11]
  by_cases c12 : k = sp (.ru .rep)
  · rw [if_pos c12, c12, h12]
  rw [if_neg c12]
  exact (hrest k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12).symm

section Chain

variable (B : SK Es → List Sym) (a b c d : List Sym)

theorem ch_arr : Function.update (Function.update (Function.update (Function.update B (kW .arr) a)
    (sp .Out) b) (kN .tapTab) c) (sp .TR) d (kW .arr) = a := by
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
    Function.update_of_ne (by simp), Function.update_self]

theorem ch_out : Function.update (Function.update (Function.update (Function.update B (kW .arr) a)
    (sp .Out) b) (kN .tapTab) c) (sp .TR) d (sp .Out) = b := by
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem ch_tap : Function.update (Function.update (Function.update (Function.update B (kW .arr) a)
    (sp .Out) b) (kN .tapTab) c) (sp .TR) d (kN .tapTab) = c := by
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem ch_tr : Function.update (Function.update (Function.update (Function.update B (kW .arr) a)
    (sp .Out) b) (kN .tapTab) c) (sp .TR) d (sp .TR) = d :=
  Function.update_self ..

theorem ch_other (k : SK Es) (h1 : k ≠ kW .arr) (h2 : k ≠ sp .Out) (h3 : k ≠ kN .tapTab)
    (h4 : k ≠ sp .TR) :
    Function.update (Function.update (Function.update (Function.update B (kW .arr) a)
      (sp .Out) b) (kN .tapTab) c) (sp .TR) d k = B k := by
  rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h1]

end Chain

/-! ## The group walk -/

/-- The loop fields before group `g`. -/
def fG (wI wT q t W a0 rep : ℕ) (xs : List CInt) (tb : List (List CInt)) (rarr rest : List Sym)
    (A g : ℕ) : LF where
  arr := carrSyms wI ((xs.drop (g * rep * t)).map fun x => [x]) ++ rarr
  out := (carrSyms wI ((stageOuts q t W a0 rep xs tb (g * rep)).map fun y => [y])).reverse
  tap := carrSyms wT (tb.drop g) ++ Sym.mark :: rest
  tr := (carrSyms wT (tb.take g)).reverse
  f0 := []
  f1 := []
  f2 := []
  f3 := []
  x3 := List.replicate g .mark
  x4 := []
  rA := List.replicate (A - g) .mark
  rR := List.replicate rep .mark

/-- The fields at the start of the body of group `g` (one mark moved from `ru A` to `X 3`). -/
def fGa (wI wT q t W a0 rep : ℕ) (xs : List CInt) (tb : List (List CInt)) (rarr rest : List Sym)
    (A g : ℕ) : LF :=
  { fG wI wT q t W a0 rep xs tb rarr rest A g with
    rA := List.replicate (A - g - 1) Sym.mark ++ []
    x3 := Sym.mark :: List.replicate g Sym.mark }

set_option maxHeartbeats 1000000 in
theorem runs_gBody (hLW : LineWalkStmt) (lA : Lens σ AReg) {PF : AProg (SK Es)} {CF : ℕ}
    (hPF : PFSpec PF CF) {PL : Prog (SK Es) (fun _ => Sym) σ} {CL : ℕ}
    (hPL : SpreadLineSpec PL CL)
    (s wI wT q t W a0 A rep : ℕ) (xs : List CInt) (tb : List (List CInt))
    (rarr rest : List Sym) (B : SK Es → List Sym)
    (hxs : xs.length = A * rep * t) (htb : tb.length = A) (hFW : ∀ F ∈ tb, F.length = W)
    (hW1 : 1 ≤ W) (hWt : W ≤ t) (ha0 : a0 ≤ t) (hwI : 1 ≤ wI) (hwIs : wI ≤ s) (hq : q ≤ s)
    (hwT : 1 ≤ wT) (hwTs : wT ≤ s)
    (hX : ∀ x ∈ xs, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hF : ∀ F ∈ tb, ∀ y ∈ F, FitsTwos wT y.1 ∧ FitsTwos wT y.2)
    (hslot1 : (W : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1))
    (hslot2 : W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s)
    (hY : ∀ y ∈ stageOuts q t W a0 rep xs tb (A * rep), FitsTwos wI y.1 ∧ FitsTwos wI y.2)
    (hs : B (sp (.ru .s)) = List.replicate s .mark)
    (hsq : B (sp (.ru .sq)) = List.replicate q .mark)
    (hh : B (sp (.ru .h)) = List.replicate (s - q) .mark)
    (hwIr : B (sp (.ru .wI)) = List.replicate wI .mark)
    (hWm1 : B (sp (.ru .Wm1)) = List.replicate (W - 1) .mark)
    (hWr : B (sp (.ru .W)) = List.replicate W .mark)
    (hwI1 : B (sp (.ru .wI1)) = List.replicate (wI - 1) .mark)
    (hsWI : B (sp (.ru .sWI)) = List.replicate (s - wI) .mark)
    (hwT1 : B (sp (.ru .wT1)) = List.replicate (wT - 1) .mark)
    (hsWT : B (sp (.ru .sWT)) = List.replicate (s - wT) .mark)
    (hp0 : B (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark)
    (hp1 : B (sp (.pr 1)) = List.replicate (t * (2 * wI + 1)) .mark)
    (hp2 : B (sp (.pr 2)) = List.replicate (a0 * (2 * wI + 1)) .mark)
    (hp3 : B (sp (.pr 3)) = List.replicate ((t - a0) * (2 * wI + 1)) .mark)
    (hp4 : B (sp (.pr 4)) = List.replicate ((W - 1) * s) .mark)
    (hLS : ∀ x, LineScratch x → B (sp x) = []) (g : ℕ) (hg : g < A) :
    Runs (gBody lA PF PL)
      (Function.update (Function.update (lst B (fG wI wT q t W a0 rep xs tb rarr rest A g))
        (sp (.ru .A)) (List.replicate (A - g - 1) .mark ++ [])) (sp (.X 3))
        (.mark :: lst B (fG wI wT q t W a0 rep xs tb rarr rest A g) (sp (.X 3))))
      (lst B (fG wI wT q t W a0 rep xs tb rarr rest A (g + 1))) (fun _ => True)
      (grpCost CF CL s t W rep) := by
  rw [lst_upd_rA, lst_upd_x3, lst_x3]
  show Runs (gBody lA PF PL) (lst B (fGa wI wT q t W a0 rep xs tb rarr rest A g))
    (lst B (fG wI wT q t W a0 rep xs tb rarr rest A (g + 1))) (fun _ => True)
    (grpCost CF CL s t W rep)
  have hgt : g < tb.length := by omega
  have hFgmem : tb.getD g [] ∈ tb := by
    simp only [List.getD, List.getElem?_eq_getElem hgt, Option.getD_some]
    exact List.getElem_mem hgt
  have hFgl : (tb.getD g []).length = W := hFW _ hFgmem
  have h1 := runs_pf lA hPF B (fGa wI wT q t W a0 rep xs tb rarr rest A g) wT s (tb.getD g [])
    (carrSyms wT (tb.drop (g + 1)) ++ Sym.mark :: rest) hwT hwTs (hF _ hFgmem)
    (by
      show carrSyms wT (tb.drop g) ++ Sym.mark :: rest = _
      rw [tb_drop tb g hgt, ← List.singleton_append, carr_append, List.append_assoc])
    hwT1 hsWT (fun j => hLS _ (by unfold LineScratch; simp))
  have hlen : (g * rep + rep) * t ≤ xs.length := by
    rw [hxs]
    calc (g * rep + rep) * t = (g + 1) * rep * t := by ring
      _ ≤ A * rep * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hYg : ∀ y ∈ grpOuts q t W a0 xs (tb.getD g []) (g * rep) rep,
      FitsTwos wI y.1 ∧ FitsTwos wI y.2 := by
    intro y hy
    apply hY
    apply stageOuts_mono q t W a0 rep xs tb (m := g * rep + rep)
    · calc g * rep + rep = (g + 1) * rep := by ring
        _ ≤ A * rep := Nat.mul_le_mul_right _ (by omega)
    · rw [stageOuts_grp]
      exact List.mem_append_right _ hy
  have h2 := hLW lA PL CL hPL s wI wT q t W a0 rep (g * rep) xs (tb.getD g []) rarr
    (lst B (pfRec (fGa wI wT q t W a0 rep xs tb rarr rest A g) wT s (tb.getD g [])
      (carrSyms wT (tb.drop (g + 1)) ++ Sym.mark :: rest))) hlen hFgl
    hW1 hWt ha0 hwI hwIs hq hX (hF _ hFgmem) hslot1 hslot2 hYg (by simp [pfRec, fGa, fG])
    (fun k => by fin_cases k <;> simp [pfRec, fGa, fG]) (by simp [pfRec, fGa, fG])
    (by simp [pfRec, fGa, fG]) (by simp [lst, hs])
    (by simp [lst, hsq]) (by simp [lst, hh]) (by simp [lst, hwIr]) (by simp [lst, hWm1])
    (by simp [lst, hWr]) (by simp [lst, hwI1]) (by simp [lst, hsWI]) (by simp [lst, hp0])
    (by simp [lst, hp1]) (by simp [lst, hp2]) (by simp [lst, hp3]) (by simp [lst, hp4])
    (fun x hx => (lst_ls B _ hx).trans (hLS x hx))
  rw [lst_upd_arr, lst_upd_out, lst_out] at h2
  have h := WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (runs_drainF lA B _))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h (lst_congr B ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_)) (fun _ _ => trivial) ?_
  · simp only [fG]
    rw [show (g * rep + rep) * t = (g + 1) * rep * t by ring]
  · simp only [pfRec, fGa, fG]
    rw [show (g + 1) * rep = g * rep + rep by ring, stageOuts_grp, List.map_append, carr_append,
      List.reverse_append]
  · simp only [pfRec, fGa, fG]
  · simp only [pfRec, fGa, fG]
    rw [tb_take tb g hgt, carr_append, List.reverse_append]
  · simp only [fG]
  · simp only [fG]
  · simp only [fG]
  · simp only [fG]
  · simp only [pfRec, fGa, fG, List.replicate_succ]
  · simp only [pfRec, fGa, fG]
  · simp only [pfRec, fGa, fG, List.append_nil]
    congr 1 <;> omega
  · simp only [pfRec, fGa, fG]
  · have hk : ∀ k : Fin 4, (natSyms (pack s ((tb.getD g []).reverse.map (cpart wT k)))).length ≤
        s * W := fun k => by
      have := len_pk s wT (tb.getD g []) k hwT hwTs
      rwa [hFgl] at this
    have hk0 := hk 0
    have hk1 := hk 1
    have hk2 := hk 2
    have hk3 := hk 3
    simp only [pfRec, fGa, fG, List.append_nil, hFgl]
    unfold grpCost
    omega

set_option maxHeartbeats 1000000 in
/-- **The stage double loop** (interface of `Bridge/SpreadStageMain.lean`). -/
theorem runs_groupLoop (lA : Lens σ AReg) {PF : AProg (SK Es)} {CF : ℕ} (hPF : PFSpec PF CF)
    {PL : Prog (SK Es) (fun _ => Sym) σ} {CL : ℕ} (hPL : SpreadLineSpec PL CL)
    (s wI wT q t W a0 A rep : ℕ) (xs : List CInt) (tb : List (List CInt))
    (rarr rest : List Sym) (B : SK Es → List Sym)
    (hxs : xs.length = A * rep * t) (htb : tb.length = A) (hFW : ∀ F ∈ tb, F.length = W)
    (hW1 : 1 ≤ W) (hWt : W ≤ t) (ha0 : a0 ≤ t) (hwI : 1 ≤ wI) (hwIs : wI ≤ s) (hq : q ≤ s)
    (hwT : 1 ≤ wT) (hwTs : wT ≤ s)
    (hX : ∀ x ∈ xs, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hF : ∀ F ∈ tb, ∀ y ∈ F, FitsTwos wT y.1 ∧ FitsTwos wT y.2)
    (hslot1 : (W : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1))
    (hslot2 : W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s)
    (hY : ∀ y ∈ stageOuts q t W a0 rep xs tb (A * rep), FitsTwos wI y.1 ∧ FitsTwos wI y.2)
    (harr : B (kW .arr) = carrSyms wI (xs.map fun x => [x]) ++ rarr)
    (hout : B (sp .Out) = [])
    (htap : B (kN .tapTab) = carrSyms wT tb ++ Sym.mark :: rest)
    (htr : B (sp .TR) = []) (hFk : ∀ k, B (sp (.F k)) = [])
    (hX3 : B (sp (.X 3)) = []) (hX4 : B (sp (.X 4)) = [])
    (hrA : B (sp (.ru .A)) = List.replicate A .mark)
    (hrR : B (sp (.ru .rep)) = List.replicate rep .mark)
    (hs : B (sp (.ru .s)) = List.replicate s .mark)
    (hsq : B (sp (.ru .sq)) = List.replicate q .mark)
    (hh : B (sp (.ru .h)) = List.replicate (s - q) .mark)
    (hwIr : B (sp (.ru .wI)) = List.replicate wI .mark)
    (hWm1 : B (sp (.ru .Wm1)) = List.replicate (W - 1) .mark)
    (hWr : B (sp (.ru .W)) = List.replicate W .mark)
    (hwI1 : B (sp (.ru .wI1)) = List.replicate (wI - 1) .mark)
    (hsWI : B (sp (.ru .sWI)) = List.replicate (s - wI) .mark)
    (hwT1 : B (sp (.ru .wT1)) = List.replicate (wT - 1) .mark)
    (hsWT : B (sp (.ru .sWT)) = List.replicate (s - wT) .mark)
    (hp0 : B (sp (.pr 0)) = List.replicate ((W - 1) * (2 * wI + 1)) .mark)
    (hp1 : B (sp (.pr 1)) = List.replicate (t * (2 * wI + 1)) .mark)
    (hp2 : B (sp (.pr 2)) = List.replicate (a0 * (2 * wI + 1)) .mark)
    (hp3 : B (sp (.pr 3)) = List.replicate ((t - a0) * (2 * wI + 1)) .mark)
    (hp4 : B (sp (.pr 4)) = List.replicate ((W - 1) * s) .mark)
    (hLS : ∀ x, LineScratch x → B (sp x) = []) :
    Runs (groupLoop lA PF PL) B
      (Function.update (Function.update (Function.update (Function.update B (kW .arr) rarr)
        (sp .Out) (carrSyms wI ((stageOuts q t W a0 rep xs tb (A * rep)).map fun y => [y])).reverse)
        (kN .tapTab) (Sym.mark :: rest)) (sp .TR) (carrSyms wT tb).reverse)
      (fun _ => True) (A * (grpCost CF CL s t W rep + 8) + 4) := by
  have hLW : LineWalkStmt := lineWalk_holds
  have hw := runs_walkL lA (R := sp (.ru .A)) (X := sp (.X 3)) (by simp) (gBody lA PF PL) A [] []
    (by simp) (fun g => lst B (fG wI wT q t W a0 rep xs tb rarr rest A g))
    (fun g _ => by simp [fG]) (fun g _ => by simp [fG]) (grpCost CF CL s t W rep)
    (fun g hg => runs_gBody hLW lA hPF hPL s wI wT q t W a0 A rep xs tb rarr rest B hxs htb hFW
      hW1 hWt ha0 hwI hwIs hq hwT hwTs hX hF hslot1 hslot2 hY hs hsq hh hwIr hWm1 hWr hwI1 hsWI
      hwT1 hsWT hp0 hp1 hp2 hp3 hp4 hLS g hg)
  have h0 : lst B (fG wI wT q t W a0 rep xs tb rarr rest A 0) = B := by
    apply lst_eq_of
    · simp only [fG, Nat.zero_mul, List.drop_zero]; rw [harr]
    · simp only [fG, Nat.zero_mul]; rw [hout]; simp [stageOuts, carr_nil]
    · simp only [fG, List.drop_zero]; rw [htap]
    · simp only [fG, List.take_zero, carr_nil, List.reverse_nil]; rw [htr]
    · simp only [fG]; rw [hFk 0]
    · simp only [fG]; rw [hFk 1]
    · simp only [fG]; rw [hFk 2]
    · simp only [fG]; rw [hFk 3]
    · simp only [fG, List.replicate_zero]; rw [hX3]
    · simp only [fG]; rw [hX4]
    · simp only [fG, Nat.sub_zero]; rw [hrA]
    · simp only [fG]; rw [hrR]
    · intros; rfl
  beta_reduce at hw
  rw [h0] at hw
  have hm : Runs (ar lA (moveMarks (sp (.X 3)) (sp (.ru .A))))
      (lst B (fG wI wT q t W a0 rep xs tb rarr rest A A))
      (Function.update (Function.update (lst B (fG wI wT q t W a0 rep xs tb rarr rest A A))
        (sp (.X 3)) []) (sp (.ru .A))
        (List.replicate A .mark ++ lst B (fG wI wT q t W a0 rep xs tb rarr rest A A) (sp (.ru .A))))
      (fun _ => True) (4 * A + 2) :=
    runs_ar lA (Q := fun _ => True) (Runs.of_eval fun v =>
      ⟨_, _, moveMarks_eval (by simp) A [] v _ (by simp) (by simp [fG]), trivial, le_rfl⟩)
  rw [lst_upd_x3, lst_upd_rA, lst_rA] at hm
  have h := WP.W9comp.runs_seq hw hm
  have hd : xs.drop (A * rep * t) = [] := List.drop_eq_nil_of_le (by omega)
  have htd : tb.drop A = [] := List.drop_eq_nil_of_le (by omega)
  have htk : tb.take A = tb := List.take_of_length_le (by omega)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) ?_
  · apply lst_eq_of
    · simp only [fG, hd, List.map_nil, carr_nil, List.nil_append]; rw [ch_arr]
    · simp only [fG]; rw [ch_out]
    · simp only [fG, htd, carr_nil, List.nil_append]; rw [ch_tap]
    · simp only [fG, htk]; rw [ch_tr]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hFk 0]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hFk 1]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hFk 2]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hFk 3]
    · rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hX3]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hX4]
    · simp only [fG, Nat.sub_self, List.replicate_zero, List.append_nil]
      rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hrA]
    · simp only [fG]; rw [ch_other _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), hrR]
    · intro k h1 h2 h3 h4 _ _ _ _ _ _ _ _
      exact ch_other B _ _ _ _ k h1 h2 h3 h4
  · have e : A * (grpCost CF CL s t W rep + 8) = A * (grpCost CF CL s t W rep + 4) + 4 * A := by
      ring
    rw [e]
    omega

end SubNLogN.Machine.Bridge.SpreadAux.Stage
