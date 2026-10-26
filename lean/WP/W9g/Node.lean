import WP.W9g.Comb

/-!
# WP.W9g.Node — the pieces of one FFT node (table algebra, unshuffle, stage counter, base case)

* LEAF body algebra: `leafTape_succ`, `leafTape_split` (the stage-`t` table inside the body),
  `twSeg_split` (its two halves), `length_leafTape`, `notGuard_leafTape`; `segsL t` lists the
  first `t` stage tables as segments.
* `cells_range`: the cells of one pass as a `List.range` map (the shape of `fftV`).
* `unshProg`: `W0 = ⟦x⟧ $D rest` ↦ `⟦evens x⟧ $D ⟦odds x⟧ $D rest` (`$D` = `symD`).
* `pushCnt`/`popCnt`: push the child stage `t` above the stage `t+1` on `CS`; pop it.
* `baseProg`: a one-entry block is rescaled (`rescK`) and pushed on `R`, followed by `$D`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## The LEAF body -/

theorem leafTape_succ (K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) :
    leafTape (K + 1) tw = leafTape K tw ++ twSeg (2 ^ (K + 1)) (tw K) := by
  have h : List.range (K + 1) = List.range K ++ [K] := List.range_succ
  simp only [leafTape, h, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem leafTape_split (tw : ℕ → ℕ → ℤ × ℤ) (t : ℕ) :
    ∀ K, t < K → ∃ rest, leafTape K tw = leafTape t tw ++ (twSeg (2 ^ (t + 1)) (tw t) ++ rest)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | K + 1, h => by
    by_cases h' : t < K
    · obtain ⟨rest, hr⟩ := leafTape_split tw t K h'
      exact ⟨rest ++ twSeg (2 ^ (K + 1)) (tw K), by
        rw [leafTape_succ, hr, List.append_assoc, List.append_assoc]⟩
    · obtain rfl : t = K := by omega
      exact ⟨[], by rw [leafTape_succ, List.append_nil]⟩

theorem twSeg_split (t : ℕ) (f : ℕ → ℤ × ℤ) :
    twSeg (2 ^ (t + 1)) f = blkE ((List.range (2 ^ t)).map f) ++
      (blkE ((List.range (2 ^ t)).map (fun j => f (2 ^ t + j))) ++ [symSub]) := by
  have h : List.range (2 ^ (t + 1)) =
      List.range (2 ^ t) ++ (List.range (2 ^ t)).map (fun j => 2 ^ t + j) := by
    rw [show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by rw [Nat.pow_succ]; omega]
    exact List.range_add
  rw [twSeg_eq, h, List.map_append, List.map_map, blkE_append, List.append_assoc]
  all_goals rfl

theorem length_twSeg (w n : ℕ) (f : ℕ → ℤ × ℤ) (hw : ∀ u < n, EntryW w (f u)) :
    (twSeg n f).length ≤ n * eb w + 1 := by
  have hb := length_blkE w ((List.range n).map f) (fun z hz => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz
    exact hw u (List.mem_range.1 hu))
  rw [List.length_map, List.length_range] at hb
  rw [twSeg_eq, List.length_append, List.length_singleton]
  omega

theorem length_leafTape (w K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) (htw : TwOK w K tw) :
    ∀ t, t ≤ K → (leafTape t tw).length ≤ 2 ^ (t + 1) * eb w + t
  | 0, _ => by simp [leafTape]
  | t + 1, ht => by
    have ih := length_leafTape w K tw htw t (by omega)
    have h2 := length_twSeg w (2 ^ (t + 1)) (tw t) (fun u hu => htw t (by omega) u hu)
    have e : 2 ^ (t + 1 + 1) = 2 ^ (t + 1) * 2 := rfl
    have e2 : 2 ^ (t + 1 + 1) * eb w = 2 ^ (t + 1) * eb w + 2 ^ (t + 1) * eb w := by
      rw [e, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
    rw [leafTape_succ, List.length_append]
    omega

theorem notGuard_twSeg (n : ℕ) (f : ℕ → ℤ × ℤ) :
    ∀ y ∈ twSeg n f, notSym symGuard (some y) = true := by
  intro y hy
  rw [twSeg_eq, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · exact notSym_blkE (by decide) (by decide) y hy
  · decide

theorem notGuard_leafTape (K : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) :
    ∀ y ∈ leafTape K tw, notSym symGuard (some y) = true := by
  intro y hy
  unfold leafTape at hy
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 hy
  exact notGuard_twSeg _ _ y hs

/-- The first `t` stage tables of the LEAF body, as segments. -/
def segsL (t : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : List (List Sym) :=
  (List.range t).map (fun s => twSeg (2 ^ (s + 1)) (tw s))

theorem segsL_flatten (t : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : (segsL t tw).flatten = leafTape t tw := rfl

theorem segsL_length (t : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : (segsL t tw).length = t := by
  simp [segsL]

theorem segsL_ok (t : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) : ∀ g ∈ segsL t tw, SegOK g := by
  intro g hg
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  exact segOK_twSeg _ _

/-! ## Cells of a pass -/

theorem cells_range (q2 : ℕ) : ∀ (n : ℕ) (f : ℕ → ℤ × ℤ) (a b : List (ℤ × ℤ)),
    a.length = n → b.length = n →
      cells q2 a b ((List.range n).map f) =
        (List.range n).map (fun j => cellV q2 (a.getD j (0, 0)) (b.getD j (0, 0)) (f j))
  | 0, _, [], [], _, _ => rfl
  | 0, _, _ :: _, _, ha, _ => by simp at ha
  | 0, _, [], _ :: _, _, hb => by simp at hb
  | _ + 1, _, [], _, ha, _ => by simp at ha
  | _ + 1, _, _ :: _, [], _, hb => by simp at hb
  | n + 1, f, x :: a, y :: b, ha, hb => by
    have ih := cells_range q2 n (fun j => f (j + 1)) a b (by simpa using ha) (by simpa using hb)
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    simp only [cells, Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_zero,
      List.getD_cons_succ, ih]

/-! ## Programs -/

section Prog

variable {τ : Type}

/-- Unshuffle: `W0 = ⟦x⟧ $D rest` ↦ `⟦evens x⟧ $D ⟦odds x⟧ $D rest`. -/
def unshProg : MProg Stk τ :=
  .seq (lm (pushC .E .mark)) (.seq (lm (pushC .O .mark)) (.seq (unshPairs .W0 .E .O .T1)
    (.seq (moveAll .O .W0 .T1 .mark) (.seq (lm (popR .O)) (.seq (lm (pushC .W0 symD))
    (.seq (moveAll .E .W0 .T1 .mark) (lm (popR .E))))))))

/-- Push the child stage: `CS = t+1 $ …` ↦ `t $ t+1 $ …` (temporaries `CK`, `CT`). -/
def pushCnt : MProg Stk τ :=
  .seq (lm (pushC .CK .mark)) (.seq (lm (copyBlock .CS .CK .CT)) (.seq (lm (dec .CK .CT))
    (.seq (lm (pushC .CS .mark)) (.seq (lm (copyBlock .CK .CS .CT))
    (.seq (lm (WP.W6a.dropBits .CK)) (lm (popR .CK)))))))

/-- Pop the child stage. -/
def popCnt : MProg Stk τ := .seq (lm (WP.W6a.dropBits .CS)) (lm (popR .CS))

theorem copyBlockS_closed (src dst tmp : Stk) : (copyBlock src dst tmp : SProg Stk).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, pushC, pushR, popR, restoreR, skip]

theorem decS_closed (k t : Stk) : (dec k t : SProg Stk).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dec, scanLoop, scanBody, decFix, pushC, popR, peekR, skip,
    moveBits, moveBitsBody, pushR]

theorem unshProg_closed : (unshProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed trivial, unshPairs_closed _ _ _ _, moveAll_closed _ _ _ _,
    lm_closed trivial, lm_closed trivial, moveAll_closed _ _ _ _, lm_closed trivial⟩

theorem pushCnt_closed : (pushCnt : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed (decS_closed _ _),
    lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed (WP.W6a.closed_dropBits _),
    lm_closed trivial⟩

theorem popCnt_closed : (popCnt : MProg Stk τ).Closed :=
  ⟨lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial⟩

end Prog

/-- The base case: rescale the single entry, push it and the delimiter on `R`. -/
def baseProg (X : Prims) : MProg Stk X.Reg :=
  .seq (lm (pushC .R symD)) (.seq (lm (emove .W0 .RI .T1)) (.seq (rescK X)
    (.seq (lm (emove .RO .R .T1)) (.seq (lm (dropEntry .RI)) (lm (popR .W0))))))

theorem baseProg_closed (X : Prims) : (baseProg X).Closed :=
  ⟨lm_closed trivial, lm_closed (emove_closed _ _ _), rescK_closed X,
    lm_closed (emove_closed _ _ _), lm_closed (dropEntry_closed _), lm_closed trivial⟩

/-! ## Specs -/

section Spec

variable {τ : Type}

theorem unsh_rs (w n : ℕ) (xs : List (ℤ × ℤ)) (rest : List Sym) (σ : Stk → List Sym)
    (hl : xs.length = 2 * n) (hw : ∀ z ∈ xs, EntryW w z) (h0 : σ .W0 = blkE xs ++ symD :: rest) :
    RS [] (unshProg : MProg Stk τ) σ
      (Function.update σ .W0 (blkE (evensL xs) ++ symD :: (blkE (oddsL xs) ++ symD :: rest)))
      (n * (24 * eb w + 18) + 11) := by
  obtain ⟨he, ho⟩ := length_evensL_oddsL n xs hl
  refine ((pushC_rs (τ := τ) .E .mark σ).seq
    ((pushC_rs .O .mark _).seq
    ((unshPairs_rs (w0 := Stk.W0) (e := Stk.E) (o := Stk.O) (t := Stk.T1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) w n xs [] [] rest (Sym.mark :: σ .E)
      (Sym.mark :: σ .O) _ hl hw (by exact h0) (by rfl) (by rfl)).seq
    ((moveAll_rs (src := Stk.O) (dst := Stk.W0) (t := Stk.T1) (by decide) (by decide) (by decide)
      mark_ok w (oddsL xs) (σ .O) (symD :: rest) _ (fun z hz => hw z (mem_oddsL hz)) (by rfl)
      (by rfl)).seq
    ((popR_rs .O _ Sym.mark (σ .O) (by rfl)).seq
    ((pushC_rs .W0 symD _).seq
    ((moveAll_rs (src := Stk.E) (dst := Stk.W0) (t := Stk.T1) (by decide) (by decide) (by decide)
      mark_ok w (evensL xs) (σ .E) (symD :: (blkE (oddsL xs) ++ symD :: rest)) _
      (fun z hz => hw z (mem_evensL hz)) (by rfl) (by rfl)).seq
    (popR_rs .E _ Sym.mark (σ .E) (by rfl))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have key : n * (12 * eb w + 8) + n * (6 * eb w + 5) + n * (6 * eb w + 5) =
        n * (24 * eb w + 18) := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      congr 1
      omega
    rw [he, ho]
    omega

theorem pushCnt_rs (t : ℕ) (c0 : List Sym) (σ : Stk → List Sym)
    (h : σ .CS = natSyms (t + 1) ++ Sym.mark :: c0) :
    RS [] (pushCnt : MProg Stk τ) σ (Function.update σ .CS (natSyms t ++ Sym.mark :: σ .CS))
      (23 * bitLen (t + 1) + 27) := by
  refine ((pushC_rs (τ := τ) .CK .mark σ).seq
    ((copyNat_rs (src := Stk.CS) (dst := Stk.CK) (tmp := Stk.CT) (by decide) (by decide)
      (by decide) (t + 1) (Sym.mark :: c0) _ (termOK_mark' _) (by exact h)).seq
    ((dec_rs (k := Stk.CK) (t := Stk.CT) (by decide) t (Sym.mark :: σ .CK) _ (termOK_mark' _)
      (by rfl)).seq
    ((pushC_rs .CS .mark _).seq
    ((copyNat_rs (src := Stk.CK) (dst := Stk.CS) (tmp := Stk.CT) (by decide) (by decide)
      (by decide) t (Sym.mark :: σ .CK) _ (termOK_mark' _) (by rfl)).seq
    ((dropNat_rs .CK t (Sym.mark :: σ .CK) _ (termOK_mark' _) (by rfl)).seq
    (popR_rs .CK _ Sym.mark (σ .CK) (by rfl)))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have := bitLen_mono' (Nat.le_add_right t 1)
    omega

theorem popCnt_rs (t : ℕ) (c0 : List Sym) (σ : Stk → List Sym)
    (h : σ .CS = natSyms t ++ Sym.mark :: c0) :
    RS [] (popCnt : MProg Stk τ) σ (Function.update σ .CS c0) (3 * bitLen t + 3) := by
  refine ((dropNat_rs (τ := τ) Stk.CS t (Sym.mark :: c0) σ (termOK_mark' _) h).seq
    (popR_rs Stk.CS _ Sym.mark c0 (by rfl))).congr ?_ (by omega)
  funext k
  cases k <;> rfl

theorem base_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (left : Bool) (w d : ℕ) (a b : ℤ) (rest rs rd : List Sym)
    (σ : Stk → List Sym) (h0 : σ .W0 = entrySyms (a, b) ++ symD :: rest)
    (hSH : σ .SH = natSyms d ++ rs) (hrs : TermOK rs) (hDIR : σ .DIR = dirSym left :: rd)
    (hT : ∀ k ∈ rsTemps, TermOK (σ k)) (hw : EntryW w (a, b))
    (hw' : EntryW w (rescLD left d a, rescLD left d b)) :
    RS [] (baseProg X) σ
      (Function.update (Function.update σ .W0 rest) .R
        (entrySyms (rescLD left d a, rescLD left d b) ++ symD :: σ .R))
      (rescCost CL CA CR w d + 14 * eb w + 8) := by
  refine ((pushC_rs .R symD σ).seq
    ((emove_rs (src := Stk.W0) (dst := Stk.RI) (t := Stk.T1) (by decide) (by decide) (by decide)
      (a, b) (symD :: rest) _ (by exact h0)).seq
    ((rescK_rs hok left w d a b (σ .RI) rs rd _ (by rfl) (by exact hSH) hrs (by exact hDIR)
      (fun k hk => by
        simp only [rsTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hT _ (by decide)) hw.1 hw.2).seq
    ((emove_rs (src := Stk.RO) (dst := Stk.R) (t := Stk.T1) (by decide) (by decide) (by decide)
      (rescLD left d a, rescLD left d b) (σ .RO) _ (by rfl)).seq
    ((dropEntry_rs .RI (a, b) (σ .RI) _ (by rfl)).seq
    (popR_rs .W0 _ symD rest (by rfl))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have e1 := length_entrySyms_le hw
    have e2 := length_entrySyms_le hw'
    omega

end Spec

#assert_std_axioms leafTape_succ leafTape_split twSeg_split length_twSeg length_leafTape
  notGuard_twSeg notGuard_leafTape segsL_flatten segsL_length segsL_ok cells_range
  copyBlockS_closed decS_closed unshProg_closed pushCnt_closed popCnt_closed baseProg_closed
  unsh_rs pushCnt_rs popCnt_rs base_rs

end WP.W9g
