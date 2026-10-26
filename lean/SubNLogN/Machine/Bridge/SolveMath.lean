import SubNLogN.Machine.Bridge.SolveSweepDefs
import SubNLogN.Machine.Bridge.SolveSplitDefs
import SubNLogN.Machine.Contracts.Bridge
import SubNLogN.Math.Bridge.IntForms.Solver
import SubNLogN.Math.Bridge.Proofs.LemmaB_Inverse

/-!
# K5-SOLVE value glue (SOLVE-MATH): the kernel's integer recurrences are `deconvAxisFixedR`

The solver kernel of `SolveAxisStmt` (`Contracts/Bridge.lean`) computes, on the numerators of the
array in natural frequency order, the integer recurrence `sweepHalfI` (`Bridge/SolveSweepDefs.lean`)
on the forward half and on the reindexed backward half (`Bridge/SolveSplitDefs.lean`), and merges
the halves. `deconvAxis_glue` states that this composition is exactly `encVec q` of
`deconvAxisFixedR roundHalfUpR q t T i Y` (`q = P + 2`), for tables and data on the `q`-grid.

Proof route: the kernel's operations are the half-up numerator operations of
`Math/Bridge/IntForms/Solver.lean` (`colI q μ na γ = cycSweepFwdInt q μ (-na) γ`), whose value lemma
`gridValC_cycSweepInt_of_eq` identifies them with `cycSweepR roundHalfUpR`; on the cycle of
`f = j₀·2M + s` the digit is `u = s / U` (`U = ∏_{l>i} t_l`), forward iff `s < M`; the backward
reindex maps `reindexI`, `reindexJ` are `imod (1 - i) L`, `imod (-j) L` (`imod_one_sub`,
`imod_neg`).

`sweepFits_of_solveFits` turns the real-level width side condition `SolveFits` of `SolveAxisStmt`
into the kernel's integer width conditions `ColFitsI` (`Bridge/SolveSweepDefs.lean`) for every column
of both halves (`colFits_of_sweepFits`: `SweepFits` of a cycle is `ColFitsI` of its numerators).

Main results (namespace `SubNLogN.Machine.Bridge`): `deconvAxis_glue`, `solveF_eq`, `solveB_eq`,
`sweepFits_of_solveFits`, with the data `solveM`, `solveU`, `solveRowF`, `solveRowB`, `solveGMu`,
`solveGNa`, `solveGGm`, `solveYs`, `solveF`, `solveB`; helpers in `SolveMathAux`.
-/

namespace SubNLogN.Machine.Bridge

open SubNLogN.Machine SubNLogN.Machine.Bridge.SolveAux SubNLogN.Math.Common
open SubNLogN.Math.Common.GridInt SubNLogN.Math.Bridge SubNLogN.Math.Bridge.IntForms

namespace SolveMathAux

/-! ### The kernel's integer operations are the IntForms operations -/

theorem gridInt_eq_gridIntC (F : ℕ) (z : ℂ) : gridInt F z = gridIntC F z := rfl

theorem gridInt_gridValC (F : ℕ) (c : ℤ × ℤ) : gridInt F (gridValC F c) = c :=
  gridIntC_gridValC F c

theorem bI_eq (q : ℕ) (mu : ℤ) (y : CInt) : bI q mu y = rhuShiftC q (smulC mu y) := by
  rw [bI, cmulTruncC_zero_real, smulC, mul_comm y.1, mul_comm y.2]; rfl

theorem rI_eq (q : ℕ) (a : ℤ) (p : CInt) : rI q a p = rhuShiftC q (smulC a p) := by
  rw [rI, cmulTruncC_zero_real, smulC, mul_comm p.1, mul_comm p.2]; rfl

theorem stepI_eq (q : ℕ) (na : ℤ) (b p : CInt) :
    stepI q na b p = b + rhuShiftC q (smulC na p) := by
  rw [stepI, rI_eq]; rfl

theorem passI_eq (q : ℕ) (mu na : ℤ) (ys : ℕ → CInt) (z0 : CInt) (n : ℕ) :
    passI q mu na ys z0 n = sweepPrefixInt q (-na) (fun j => bI q mu (ys j)) z0 n := by
  induction n with
  | zero => rw [passI, sweepPrefixInt, stepI_eq, neg_neg]
  | succ n ih => rw [passI, sweepPrefixInt, stepI_eq, ih, neg_neg]

theorem closI_eq (q : ℕ) (mu na gm : ℤ) (L : ℕ) (ys : ℕ → CInt) :
    closI q mu na gm L ys =
      rhuShiftC q (smulC gm (sweepPrefixInt q (-na) (fun j => bI q mu (ys j)) 0 (L - 1))) := by
  rw [closI, rI_eq, passI_eq]; rfl

/-- The kernel's column output is the IntForms forward sweep with `â = -na`. -/
theorem colI_eq (q : ℕ) (mu na gm : ℤ) (L : ℕ) (ys : ℕ → CInt) (j : ℕ) :
    colI q mu na gm L ys j = cycSweepFwdInt q mu (-na) gm L ys j := by
  simp only [colI, cycSweepFwdInt, closI_eq, passI_eq, bI_eq]

/-! ### The sweep only reads the rows `< L` -/

theorem sweepPrefixInt_congr (q : ℕ) (A : ℤ) {B B' : ℕ → CInt} (Z0 : CInt) (n : ℕ)
    (h : ∀ k, k ≤ n → B k = B' k) : sweepPrefixInt q A B Z0 n = sweepPrefixInt q A B' Z0 n := by
  induction n with
  | zero => rw [sweepPrefixInt, sweepPrefixInt, h 0 le_rfl]
  | succ n ih =>
    rw [sweepPrefixInt, sweepPrefixInt, h (n + 1) le_rfl, ih (fun k hk => h k (by omega))]

theorem cycSweepFwdInt_congr (q : ℕ) (M A G : ℤ) (L : ℕ) {Y Y' : ℕ → CInt}
    (h : ∀ k, k < L → Y k = Y' k) {j : ℕ} (hj : j < L) :
    cycSweepFwdInt q M A G L Y j = cycSweepFwdInt q M A G L Y' j := by
  have hb := sweepPrefixInt_congr q A (B := fun k => rhuShiftC q (smulC M (Y k)))
    (B' := fun k => rhuShiftC q (smulC M (Y' k))) 0 (L - 1)
    (fun k hk => by simp only [h k (by omega)])
  simp only [cycSweepFwdInt]
  rw [hb]
  by_cases hjL : j = L - 1
  · rw [if_pos hjL, if_pos hjL]
  · rw [if_neg hjL, if_neg hjL]
    exact sweepPrefixInt_congr q A _ j (fun k hk => by simp only [h k (by omega)])

end SolveMathAux

/-! ### The data of the glue statement -/

variable {d : ℕ}

/-- Columns per half: `M = (R / A_i) / 2`. -/
def solveM (t : Fin d → ℕ) (i : Fin d) : ℕ := totalLen t / prefixProd t i / 2

/-- Column block of one digit: `U = 2M / t_i` (it is `∏_{l>i} t_l`). -/
def solveU (t : Fin d → ℕ) (i : Fin d) : ℕ := 2 * solveM t i / t i

/-- The forward parameter row: column `s < M` belongs to the digit `s / U`. -/
def solveRowF (t : Fin d → ℕ) (i : Fin d) (g : ℕ → ℤ) : List ℤ :=
  (List.range (solveM t i)).map fun s => g (s / solveU t i)

/-- The backward parameter row: column `s < M` belongs to the digit `t_i/2 + s / U`. -/
def solveRowB (t : Fin d → ℕ) (i : Fin d) (g : ℕ → ℤ) : List ℤ :=
  (List.range (solveM t i)).map fun s => g (t i / 2 + s / solveU t i)

/-- `μ̂` numerator of digit `u`. -/
noncomputable def solveGMu (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d) (u : ℕ) : ℤ :=
  realInt (P + 2) (T.mu i u)

/-- Negated `â` numerator of digit `u` (the kernel rounds `(-â)·p`). -/
noncomputable def solveGNa (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d) (u : ℕ) : ℤ :=
  -(realInt (P + 2) (T.ahat i u))

/-- `γ̂` numerator of digit `u`. -/
noncomputable def solveGGm (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d) (u : ℕ) : ℤ :=
  realInt (P + 2) (T.gam i u)

/-- The input numerators in natural frequency order. -/
noncomputable def solveYs (q : ℕ) {t : Fin d → ℕ} (Y : Fin (totalLen t) → ℂ) : List CInt :=
  (List.finRange (totalLen t)).map fun f => gridInt q (Y f)

/-- The kernel's output on the forward half. -/
noncomputable def solveF (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) : List CInt :=
  sweepHalfI (P + 2) (prefixProd t i) (solveM t i) (solveRowF t i (solveGMu P T i))
    (solveRowF t i (solveGNa P T i)) (solveRowF t i (solveGGm P T i))
    (SolveSplit.fwdHalf (solveM t i) (solveYs (P + 2) Y))

/-- The kernel's output on the backward half (reindexed input, read out by `reindexJ`). -/
noncomputable def solveB (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) : List CInt :=
  SolveSplit.reindexJ (solveM t i)
    (sweepHalfI (P + 2) (prefixProd t i) (solveM t i) (solveRowB t i (solveGMu P T i))
      (solveRowB t i (solveGNa P T i)) (solveRowB t i (solveGGm P T i))
      (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i) (solveYs (P + 2) Y))))

namespace SolveMathAux

/-! ### Arithmetic of the shape -/

theorem solve_arith {t : Fin d → ℕ} (hshape : ShapeOK t) (i : Fin d) :
    0 < prefixProd t i ∧ 0 < solveM t i ∧ aliasStep t i = 2 * solveM t i ∧
      solveM t i = t i / 2 * suffixProd t i ∧ solveU t i = suffixProd t i ∧
      totalLen t = prefixProd t i * (2 * solveM t i) ∧ 2 * (t i / 2) = t i := by
  have hL := LemmaBInverse.prefixProd_pos hshape i
  have hσ := LemmaBInverse.suffixProd_pos hshape i
  have hw := LemmaBInverse.aliasStep_eq hshape i
  have hR := LemmaBInverse.totalLen_eq_mul hshape i
  obtain ⟨h2, a, ha⟩ := hshape i
  have ha0 : a ≠ 0 := by rintro rfl; rw [pow_zero] at ha; omega
  have hev : Even (t i) := by rw [ha]; exact (Nat.even_pow' ha0).2 even_two
  have ht2 : 2 * (t i / 2) = t i := Nat.two_mul_div_two_of_even hev
  set h := t i / 2 with hh
  have ht2' : t i = 2 * h := ht2.symm
  have hh1 : 0 < h := by omega
  have hM : solveM t i = h * suffixProd t i := by
    show aliasStep t i / 2 = _
    rw [hw, ht2', mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hw2 : aliasStep t i = 2 * solveM t i := by rw [hw, hM, ht2']; ring
  refine ⟨hL, by rw [hM]; positivity, hw2, hM, ?_, by rw [hR, hw2, mul_comm], ht2⟩
  show 2 * solveM t i / t i = _
  rw [hM, ht2', ← mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2 * h)]

theorem div_mod_row {M k s : ℕ} (hs : s < M) : (k * M + s) / M = k ∧ (k * M + s) % M = s := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hs, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem row_lt {M L k s : ℕ} (hk : k < L) (hs : s < M) : k * M + s < L * M := by
  calc k * M + s < k * M + M := by omega
    _ = (k + 1) * M := by ring
    _ ≤ L * M := Nat.mul_le_mul_right _ hk

theorem getElem?_map_finRange {R : ℕ} {β : Type} (g : Fin R → β) {n : ℕ} (hn : n < R) :
    ((List.finRange R).map g)[n]? = some (g ⟨n, hn⟩) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hn)]
  simp

theorem solveRow_getD {M U : ℕ} (g : ℕ → ℤ) (c : ℕ) {s : ℕ} (hs : s < M) :
    ((List.range M).map fun s => g (c + s / U)).getD s 0 = g (c + s / U) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]; rfl

theorem solveRowF_getD {t : Fin d → ℕ} (i : Fin d) (g : ℕ → ℤ) {s : ℕ} (hs : s < solveM t i) :
    (solveRowF t i g).getD s 0 = g (s / solveU t i) := by
  rw [solveRowF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]; rfl

theorem solveRowB_getD {t : Fin d → ℕ} (i : Fin d) (g : ℕ → ℤ) {s : ℕ} (hs : s < solveM t i) :
    (solveRowB t i g).getD s 0 = g (t i / 2 + s / solveU t i) := by
  rw [solveRowB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]; rfl

theorem length_sweepHalfI (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) :
    (sweepHalfI q L M mus nas gms ys).length = L * M := by
  simp [sweepHalfI]

theorem sweepHalfI_getElem? (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) {x : ℕ}
    (hx : x < L * M) :
    (sweepHalfI q L M mus nas gms ys)[x]? =
      some (colI q (mus.getD (x % M) 0) (nas.getD (x % M) 0) (gms.getD (x % M) 0) L
        (fun j => ys.getD (j * M + x % M) 0) (x / M)) := by
  rw [sweepHalfI, List.getElem?_map, List.getElem?_range hx]; rfl

/-- The cycle of `f = j₀ w + s`: `shiftFin f ((k - j₀) w) = k w + s` for `k < L`, `R = L w`. -/
theorem shiftFin_cycle {R w L : ℕ} (hR : R = L * w) (f : Fin R) {j0 s k : ℕ}
    (hf : (f : ℕ) = j0 * w + s) (hs : s < w) (hk : k < L) :
    ((shiftFin f (((k : ℤ) - (j0 : ℤ)) * (w : ℤ)) : Fin R) : ℕ) = k * w + s := by
  have hlt : k * w + s < R := by rw [hR]; exact row_lt hk hs
  show (((((f : ℕ) : ℤ) + ((k : ℤ) - (j0 : ℤ)) * (w : ℤ)) % ((R : ℕ) : ℤ)).toNat) = _
  have e : ((f : ℕ) : ℤ) + ((k : ℤ) - (j0 : ℤ)) * (w : ℤ) = ((k * w + s : ℕ) : ℤ) := by
    rw [hf]; push_cast; ring
  rw [e, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt), Int.toNat_natCast]

theorem realInt_spec {q : ℕ} {x : ℝ} (hx : OnGridR q x) : x = (realInt q x : ℝ) * gridUnit q := by
  obtain ⟨a, rfl⟩ := hx
  rw [realInt, round_intCast_mul_gridUnit_mul]

theorem cycSweepInt_true (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → CInt) :
    cycSweepInt true q M A G L Y = cycSweepFwdInt q M A G L Y := rfl

theorem cycSweepInt_false (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → CInt) (j : ℕ) :
    cycSweepInt false q M A G L Y j =
      cycSweepFwdInt q M A G L (fun i => Y (imod (1 - (i : ℤ)) L)) (imod (-(j : ℤ)) L) := rfl

/-! ### Entries of the halves -/

theorem ys_getElem? (q : ℕ) {t : Fin d → ℕ} (Y : Fin (totalLen t) → ℂ) {n : ℕ}
    (hn : n < totalLen t) : (solveYs q Y)[n]? = some (gridInt q (Y ⟨n, hn⟩)) :=
  getElem?_map_finRange _ hn

/-- Row `k`, column `s` of the forward half is `Y_{k·2M + s}`. -/
theorem fwd_getD {t : Fin d → ℕ} (hshape : ShapeOK t) (i : Fin d) (q : ℕ)
    (Y : Fin (totalLen t) → ℂ) {k s : ℕ} (hk : k < prefixProd t i) (hs : s < solveM t i)
    (g : Fin (totalLen t)) (hg : (g : ℕ) = k * (2 * solveM t i) + s) :
    (SolveSplit.fwdHalf (solveM t i) (solveYs q Y)).getD (k * solveM t i + s) 0 =
      gridInt q (Y g) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hlen : (solveYs q Y).length = prefixProd t i * (2 * solveM t i) := by simp [solveYs, hR]
  obtain ⟨h1, h2⟩ := div_mod_row (k := k) hs
  have hgR : k * (2 * solveM t i) + s < totalLen t := by rw [← hg]; exact g.isLt
  rw [List.getD_eq_getElem?_getD, SolveSplit.getElem?_fwdHalf hM hlen (row_lt hk hs), h1, h2,
    ys_getElem? q Y hgR]
  have e : (⟨k * (2 * solveM t i) + s, hgR⟩ : Fin (totalLen t)) = g := Fin.ext hg.symm
  rw [e]; rfl

/-- Row `k`, column `s` of the reindexed backward half is `Y_{((L+1-k) mod L)·2M + M + s}`. -/
theorem bwd_getD {t : Fin d → ℕ} (hshape : ShapeOK t) (i : Fin d) (q : ℕ)
    (Y : Fin (totalLen t) → ℂ) {k s : ℕ} (hk : k < prefixProd t i) (hs : s < solveM t i)
    (g : Fin (totalLen t))
    (hg : (g : ℕ) = (prefixProd t i + 1 - k) % prefixProd t i * (2 * solveM t i) + solveM t i + s) :
    (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i) (solveYs q Y))).getD
      (k * solveM t i + s) 0 = gridInt q (Y g) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hlen : (solveYs q Y).length = prefixProd t i * (2 * solveM t i) := by simp [solveYs, hR]
  have hblen := SolveSplit.length_bwdHalf hM hlen
  have hm : (prefixProd t i + 1 - k) % prefixProd t i < prefixProd t i := Nat.mod_lt _ hL
  obtain ⟨h1, h2⟩ := div_mod_row (k := (prefixProd t i + 1 - k) % prefixProd t i) hs
  have hgR : (prefixProd t i + 1 - k) % prefixProd t i * (2 * solveM t i) + solveM t i + s <
      totalLen t := by rw [← hg]; exact g.isLt
  rw [List.getD_eq_getElem?_getD, SolveSplit.getElem?_reindexI hM hblen hk hs,
    SolveSplit.getElem?_bwdHalf hM hlen (row_lt hm hs), h1, h2, ys_getElem? q Y hgR]
  have e : (⟨_, hgR⟩ : Fin (totalLen t)) = g := Fin.ext hg.symm
  rw [e]; rfl

/-! ### One output entry -/

/-- Forward cycles (`s < M`): the output numerator at `f = j₀·2M + s` is the kernel's column
output. -/
theorem entry_fwd (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f)) {j0 s : ℕ}
    (hj0 : j0 < prefixProd t i) (hs : s < solveM t i) (f : Fin (totalLen t))
    (hf : (f : ℕ) = j0 * (2 * solveM t i) + s) :
    gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f) =
      colI (P + 2) (solveGMu P T i (s / solveU t i)) (solveGNa P T i (s / solveU t i))
        (solveGGm P T i (s / solveU t i)) (prefixProd t i)
        (fun j => (SolveSplit.fwdHalf (solveM t i) (solveYs (P + 2) Y)).getD
          (j * solveM t i + s) 0) j0 := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hσ := LemmaBInverse.suffixProd_pos hshape i
  have hs2 : s < aliasStep t i := by omega
  have hf' : (f : ℕ) = j0 * aliasStep t i + s := by rw [hw]; exact hf
  have hRw : totalLen t = prefixProd t i * aliasStep t i := by rw [hw]; exact hR
  have hfw : (f : ℕ) / aliasStep t i = j0 := by rw [hf']; exact (div_mod_row hs2).1
  have hfm : (f : ℕ) % aliasStep t i = s := by rw [hf']; exact (div_mod_row hs2).2
  have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) = s / solveU t i := by
    rw [LemmaBInverse.encFreq_digit_eq hshape i, hfm, hU]
  have hsu : s / solveU t i < t i / 2 := by
    rw [hU, Nat.div_lt_iff_lt_mul hσ, ← hMσ]; exact hs
  have h2u : 2 * (s / solveU t i) < t i := by omega
  obtain ⟨-, htabi⟩ := htab i hi
  obtain ⟨hmu, ha, hg⟩ := htabi (s / solveU t i) (by omega)
  have hdec : deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f =
      cycSweepR roundHalfUpR true (P + 2) (T.mu i (s / solveU t i)) (T.ahat i (s / solveU t i))
        (T.gam i (s / solveU t i)) (prefixProd t i)
        (fun j : ℕ => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ)))) j0 := by
    simp only [deconvAxisFixedR]
    rw [hu, hfw, decide_eq_true h2u]
  have hval := gridValC_cycSweepInt_of_eq true (P + 2) (realInt_spec hmu) (realInt_spec ha)
    (realInt_spec hg) (prefixProd t i)
    (Yc := fun j : ℕ => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ))))
    (Y := fun j : ℕ =>
      gridInt (P + 2) (Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ)))))
    (fun j => (gridValC_gridIntC (hY _)).symm) j0
  rw [hdec, ← hval, gridInt_gridValC, cycSweepInt_true, colI_eq,
    show -solveGNa P T i (s / solveU t i) = realInt (P + 2) (T.ahat i (s / solveU t i)) from
      neg_neg _]
  refine cycSweepFwdInt_congr _ _ _ _ _ (fun k hk => ?_) hj0
  have hkR : k * aliasStep t i + s < totalLen t := by rw [hRw]; exact row_lt hk hs2
  rw [fwd_getD hshape i (P + 2) Y hk hs ⟨k * aliasStep t i + s, hkR⟩
    (by show k * aliasStep t i + s = _; rw [hw])]
  have hsf := shiftFin_cycle hRw f hf' hs2 hk
  rw [show shiftFin f _ = (⟨_, hkR⟩ : Fin (totalLen t)) from Fin.ext hsf]

/-- Backward cycles (`s < M` in the backward half, i.e. frequency `f = j₀·2M + M + s`): the output
numerator is the kernel's column output, read at row `(L - j₀) mod L`. -/
theorem entry_bwd (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f)) {j0 s : ℕ}
    (hj0 : j0 < prefixProd t i) (hs : s < solveM t i) (f : Fin (totalLen t))
    (hf : (f : ℕ) = j0 * (2 * solveM t i) + solveM t i + s) :
    gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f) =
      colI (P + 2) (solveGMu P T i (t i / 2 + s / solveU t i))
        (solveGNa P T i (t i / 2 + s / solveU t i)) (solveGGm P T i (t i / 2 + s / solveU t i))
        (prefixProd t i)
        (fun j => (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i)
          (solveYs (P + 2) Y))).getD (j * solveM t i + s) 0)
        ((prefixProd t i - j0) % prefixProd t i) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hσ := LemmaBInverse.suffixProd_pos hshape i
  have hs2 : solveM t i + s < aliasStep t i := by omega
  have hf' : (f : ℕ) = j0 * aliasStep t i + (solveM t i + s) := by rw [hw, hf]; ring
  have hRw : totalLen t = prefixProd t i * aliasStep t i := by rw [hw]; exact hR
  have hfw : (f : ℕ) / aliasStep t i = j0 := by rw [hf']; exact (div_mod_row hs2).1
  have hfm : (f : ℕ) % aliasStep t i = solveM t i + s := by rw [hf']; exact (div_mod_row hs2).2
  have hdig : (solveM t i + s) / suffixProd t i = t i / 2 + s / solveU t i := by
    rw [hMσ, hU, Nat.add_comm, Nat.add_mul_div_right _ _ hσ, Nat.add_comm]
  have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) = t i / 2 + s / solveU t i := by
    rw [LemmaBInverse.encFreq_digit_eq hshape i, hfm, hdig]
  have hsu : s / solveU t i < t i / 2 := by
    rw [hU, Nat.div_lt_iff_lt_mul hσ, ← hMσ]; exact hs
  have h2u : ¬ (2 * (t i / 2 + s / solveU t i) < t i) :=
    Nat.not_lt.2 (by rw [Nat.mul_add, ht2]; exact Nat.le_add_right _ _)
  obtain ⟨-, htabi⟩ := htab i hi
  obtain ⟨hmu, ha, hg⟩ := htabi (t i / 2 + s / solveU t i) (by omega)
  have hdec : deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f =
      cycSweepR roundHalfUpR false (P + 2) (T.mu i (t i / 2 + s / solveU t i))
        (T.ahat i (t i / 2 + s / solveU t i)) (T.gam i (t i / 2 + s / solveU t i))
        (prefixProd t i)
        (fun j : ℕ => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ)))) j0 := by
    simp only [deconvAxisFixedR]
    rw [hu, hfw, decide_eq_false h2u]
  have hval := gridValC_cycSweepInt_of_eq false (P + 2) (realInt_spec hmu) (realInt_spec ha)
    (realInt_spec hg) (prefixProd t i)
    (Yc := fun j : ℕ => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ))))
    (Y := fun j : ℕ =>
      gridInt (P + 2) (Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (aliasStep t i : ℤ)))))
    (fun j => (gridValC_gridIntC (hY _)).symm) j0
  rw [hdec, ← hval, gridInt_gridValC, cycSweepInt_false, colI_eq,
    show -solveGNa P T i (t i / 2 + s / solveU t i) =
      realInt (P + 2) (T.ahat i (t i / 2 + s / solveU t i)) from neg_neg _,
    imod_neg (le_of_lt hj0)]
  refine cycSweepFwdInt_congr _ _ _ _ _ (fun k hk => ?_) (Nat.mod_lt _ hL)
  rw [imod_one_sub (le_of_lt hk)]
  have hm : (prefixProd t i + 1 - k) % prefixProd t i < prefixProd t i := Nat.mod_lt _ hL
  have hkR : (prefixProd t i + 1 - k) % prefixProd t i * aliasStep t i + (solveM t i + s) <
      totalLen t := by rw [hRw]; exact row_lt hm hs2
  rw [bwd_getD hshape i (P + 2) Y hk hs ⟨_, hkR⟩
    (by show _ * aliasStep t i + (solveM t i + s) = _; rw [hw]; ring)]
  have hsf := shiftFin_cycle hRw f hf' hs2 hm
  rw [show shiftFin f _ = (⟨_, hkR⟩ : Fin (totalLen t)) from Fin.ext hsf]

end SolveMathAux


/-! ### The halves of the output and the glue -/

open SolveMathAux in
/-- The kernel's forward half is the forward half of the output numerators. -/
theorem solveF_eq (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f)) :
    solveF P T i Y = SolveSplit.fwdHalf (solveM t i) ((List.finRange (totalLen t)).map
      fun f => gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f)) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hzlen : ((List.finRange (totalLen t)).map fun f =>
      gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f)).length =
        prefixProd t i * (2 * solveM t i) := by simp [hR]
  apply List.ext_getElem?
  intro x
  by_cases hx : x < prefixProd t i * solveM t i
  · have hj : x / solveM t i < prefixProd t i := by
      rw [Nat.div_lt_iff_lt_mul hM]; exact hx
    have hs : x % solveM t i < solveM t i := Nat.mod_lt _ hM
    have hidx : x / solveM t i * (2 * solveM t i) + x % solveM t i < totalLen t := by
      rw [hR]; exact row_lt hj (by omega)
    rw [SolveSplit.getElem?_fwdHalf hM hzlen hx, getElem?_map_finRange _ hidx, solveF,
      sweepHalfI_getElem? _ _ _ _ _ _ _ hx, solveRowF_getD i _ hs, solveRowF_getD i _ hs,
      solveRowF_getD i _ hs, entry_fwd P T i Y hshape hi htab hY hj hs _ rfl]
  · have h1 : (solveF P T i Y).length ≤ x := by
      rw [solveF, length_sweepHalfI]; omega
    have h2 : (SolveSplit.fwdHalf (solveM t i) ((List.finRange (totalLen t)).map fun f =>
        gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f))).length ≤ x := by
      rw [SolveSplit.length_fwdHalf hM hzlen]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

open SolveMathAux in
/-- The kernel's (reindexed) backward half is the backward half of the output numerators. -/
theorem solveB_eq (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f)) :
    solveB P T i Y = SolveSplit.bwdHalf (solveM t i) ((List.finRange (totalLen t)).map
      fun f => gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f)) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hzlen : ((List.finRange (totalLen t)).map fun f =>
      gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f)).length =
        prefixProd t i * (2 * solveM t i) := by simp [hR]
  have hSlen := length_sweepHalfI (P + 2) (prefixProd t i) (solveM t i)
    (solveRowB t i (solveGMu P T i)) (solveRowB t i (solveGNa P T i))
    (solveRowB t i (solveGGm P T i))
    (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i) (solveYs (P + 2) Y)))
  apply List.ext_getElem?
  intro x
  by_cases hx : x < prefixProd t i * solveM t i
  · have hj : x / solveM t i < prefixProd t i := by
      rw [Nat.div_lt_iff_lt_mul hM]; exact hx
    have hs : x % solveM t i < solveM t i := Nat.mod_lt _ hM
    have hm : (prefixProd t i - x / solveM t i) % prefixProd t i < prefixProd t i :=
      Nat.mod_lt _ hL
    obtain ⟨h1, h2⟩ := div_mod_row (k := (prefixProd t i - x / solveM t i) % prefixProd t i) hs
    have hidx : x / solveM t i * (2 * solveM t i) + solveM t i + x % solveM t i < totalLen t := by
      have h3 : solveM t i + x % solveM t i < 2 * solveM t i := by
        have := Nat.add_lt_add_left hs (solveM t i); rw [two_mul]; exact this
      rw [hR, Nat.add_assoc]; exact row_lt hj h3
    have hxe : x = x / solveM t i * solveM t i + x % solveM t i := (Nat.div_add_mod' x _).symm
    rw [SolveSplit.getElem?_bwdHalf hM hzlen hx, getElem?_map_finRange _ hidx, solveB]
    conv_lhs => rw [hxe]
    rw [SolveSplit.getElem?_reindexJ hM hSlen hj hs, sweepHalfI_getElem? _ _ _ _ _ _ _ (row_lt hm hs),
      h1, h2, solveRowB_getD i _ hs, solveRowB_getD i _ hs, solveRowB_getD i _ hs,
      entry_bwd P T i Y hshape hi htab hY hj hs _ rfl]
  · have h1 : (solveB P T i Y).length ≤ x := by
      rw [solveB, SolveSplit.length_reindexJ hM hSlen]; omega
    have h2 : (SolveSplit.bwdHalf (solveM t i) ((List.finRange (totalLen t)).map fun f =>
        gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f))).length ≤ x := by
      rw [SolveSplit.length_bwdHalf hM hzlen]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

open SolveMathAux in
/-- **SOLVE-MATH glue.** The merged output of the solver kernel (forward half `solveF`, backward
half `solveB`, both computed by `sweepHalfI` on the numerators) is exactly the encoding of the
deconvolution stage `deconvAxisFixedR roundHalfUpR` (`q = P + 2`), for tables and data on the
`q`-grid. -/
theorem deconvAxis_glue (P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f)) :
    encVec (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y) =
      (SolveSplit.mergeHalves (solveM t i) (solveF P T i Y) (solveB P T i Y)).map
        fun c => [c] := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hzlen : ((List.finRange (totalLen t)).map fun f =>
      gridInt (P + 2) (deconvAxisFixedR roundHalfUpR (P + 2) t T i Y f)).length =
        prefixProd t i * (2 * solveM t i) := by simp [hR]
  rw [solveF_eq P T i Y hshape hi htab hY, solveB_eq P T i Y hshape hi htab hY,
    SolveSplit.mergeHalves_fwdHalf_bwdHalf hM hzlen, List.map_map]
  rfl


/-! ### Width facts of the kernel's columns from `SolveFits` -/

namespace SolveMathAux

theorem fits_of_fitsC {w q : ℕ} {c : CInt} (h : FitsC w q (gridValC q c)) :
    FitsTwos w c.1 ∧ FitsTwos w c.2 := by
  unfold FitsC at h; rw [gridInt_gridValC] at h; exact h

theorem passI_congr (q : ℕ) (mu na : ℤ) {ys ys' : ℕ → CInt} (z0 : CInt) (n : ℕ)
    (h : ∀ k, k ≤ n → ys k = ys' k) : passI q mu na ys z0 n = passI q mu na ys' z0 n := by
  rw [passI_eq, passI_eq]
  exact sweepPrefixInt_congr q (-na) z0 n (fun k hk => by simp only [h k hk])

theorem closI_congr (q : ℕ) (mu na gm : ℤ) {L : ℕ} {ys ys' : ℕ → CInt}
    (h : ∀ k, k < L → ys k = ys' k) (hL : 0 < L) :
    closI q mu na gm L ys = closI q mu na gm L ys' := by
  rw [closI, closI, passI_congr q mu na (0, 0) (L - 1) (fun k hk => h k (by omega))]

theorem colFits_congr {w q : ℕ} {mu na gm : ℤ} {L : ℕ} {ys ys' : ℕ → CInt}
    (h : ∀ k, k < L → ys k = ys' k) (hL : 0 < L) (hc : ColFitsI w q mu na gm L ys) :
    ColFitsI w q mu na gm L ys' := by
  obtain ⟨hcl, hrows⟩ := hc
  have e := closI_congr q mu na gm h hL
  refine ⟨by rw [← e]; exact hcl, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hrows n hn
  have hp : ∀ z0, passI q mu na ys z0 n = passI q mu na ys' z0 n :=
    fun z0 => passI_congr q mu na z0 n (fun k hk => h k (by omega))
  exact ⟨by rw [← h n hn]; exact h1, by rw [← hp]; exact h2, by rw [← e, ← hp]; exact h3⟩

/-- The real-level width facts of one forward sweep (`SweepFits`) are the kernel's integer width
facts of the column with the same numerators. -/
theorem colFits_of_sweepFits {w q : ℕ} {Mu A G : ℤ} {L : ℕ} {Yc : ℕ → ℂ} {Ys : ℕ → CInt}
    (hY : ∀ j, Yc j = gridValC q (Ys j))
    (h : SweepFits w q ((Mu : ℝ) * gridUnit q) ((A : ℝ) * gridUnit q) ((G : ℝ) * gridUnit q) L
      Yc) :
    ColFitsI w q Mu (-A) G L Ys := by
  have hYc : Yc = fun j => gridValC q (Ys j) := funext hY
  subst hYc
  have hb : (fun j => crnd roundHalfUpR q ((((Mu : ℝ) * gridUnit q : ℝ) : ℂ) *
      gridValC q (Ys j))) = fun j => gridValC q (rhuShiftC q (smulC Mu (Ys j))) :=
    funext fun j => crnd_ofReal_mul q Mu (Ys j)
  have hz : gridValC q ((0, 0) : ℤ × ℤ) = 0 := gridValC_zero q
  have hpre : ∀ (Z0 : CInt) (n : ℕ), sweepPrefixR roundHalfUpR q ((A : ℝ) * gridUnit q)
      (fun j => gridValC q (rhuShiftC q (smulC Mu (Ys j)))) (gridValC q Z0) n =
      gridValC q (passI q Mu (-A) Ys Z0 n) := by
    intro Z0 n
    rw [passI_eq, neg_neg, gridValC_sweepPrefixInt]
    simp only [bI_eq]
  have hclos : crnd roundHalfUpR q ((((G : ℝ) * gridUnit q : ℝ) : ℂ) *
      sweepPrefixR roundHalfUpR q ((A : ℝ) * gridUnit q)
        (fun j => gridValC q (rhuShiftC q (smulC Mu (Ys j)))) 0 (L - 1)) =
      gridValC q (closI q Mu (-A) G L Ys) := by
    rw [← hz, hpre, crnd_ofReal_mul, closI, rI_eq]
  obtain ⟨hcl, hrows⟩ := h
  simp only [hb] at hcl hrows
  rw [hclos] at hcl
  refine ⟨fits_of_fitsC hcl, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hrows n hn
  rw [crnd_ofReal_mul] at h1
  rw [← hz, hpre] at h2
  rw [hclos, hpre] at h3
  exact ⟨by rw [bI_eq]; exact fits_of_fitsC h1, fits_of_fitsC h2, fits_of_fitsC h3⟩

end SolveMathAux

open SolveMathAux in
/-- **Width facts of the kernel's columns.** From `SolveFits` (the real-level width side condition of
`SolveAxisStmt`), every column `s < M` of the forward half and of the reindexed backward half
satisfies the kernel's integer width condition `ColFitsI` (scaled inputs, prefix states, closure
value, second-pass states). -/
theorem sweepFits_of_solveFits (w P : ℕ) {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) (hshape : ShapeOK t) (hi : (i : ℕ) ≠ 0)
    (htab : TablesOnGrid P t T) (hY : ∀ f, OnGrid (P + 2) (Y f))
    (hfit : SolveFits w (P + 2) t T i Y) :
    (∀ s, s < solveM t i →
      ColFitsI w (P + 2) ((solveRowF t i (solveGMu P T i)).getD s 0)
        ((solveRowF t i (solveGNa P T i)).getD s 0) ((solveRowF t i (solveGGm P T i)).getD s 0)
        (prefixProd t i)
        (fun j => (SolveSplit.fwdHalf (solveM t i) (solveYs (P + 2) Y)).getD
          (j * solveM t i + s) 0)) ∧
    (∀ s, s < solveM t i →
      ColFitsI w (P + 2) ((solveRowB t i (solveGMu P T i)).getD s 0)
        ((solveRowB t i (solveGNa P T i)).getD s 0) ((solveRowB t i (solveGGm P T i)).getD s 0)
        (prefixProd t i)
        (fun j => (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i)
          (solveYs (P + 2) Y))).getD (j * solveM t i + s) 0)) := by
  obtain ⟨hL, hM, hw, hMσ, hU, hR, ht2⟩ := solve_arith hshape i
  have hσ := LemmaBInverse.suffixProd_pos hshape i
  have hRw : totalLen t = prefixProd t i * aliasStep t i := by rw [hw]; exact hR
  obtain ⟨-, htabi⟩ := htab i hi
  constructor
  · intro s hs
    have hs2 : s < aliasStep t i := by omega
    have hsR : s < totalLen t := by rw [hRw]; exact row_lt (k := 0) hL hs2 |>.trans_le' (by simp)
    set f : Fin (totalLen t) := ⟨s, hsR⟩ with hfdef
    have hf' : (f : ℕ) = 0 * aliasStep t i + s := by simp [hfdef]
    have hfw : (f : ℕ) / aliasStep t i = 0 := by rw [hf']; exact (div_mod_row hs2).1
    have hfm : (f : ℕ) % aliasStep t i = s := by rw [hf']; exact (div_mod_row hs2).2
    have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) = s / solveU t i := by
      rw [LemmaBInverse.encFreq_digit_eq hshape i, hfm, hU]
    have hsu : s / solveU t i < t i / 2 := by
      rw [hU, Nat.div_lt_iff_lt_mul hσ, ← hMσ]; exact hs
    have h2u : 2 * (s / solveU t i) < t i := by omega
    obtain ⟨hmu, ha, hg⟩ := htabi (s / solveU t i) (by omega)
    have hsw := hfit f
    rw [hu, hfw, if_pos h2u, realInt_spec hmu, realInt_spec ha, realInt_spec hg] at hsw
    have hcol := colFits_of_sweepFits
      (Ys := fun j : ℕ =>
        gridInt (P + 2) (Y (shiftFin f (((j : ℤ) - ((0 : ℕ) : ℤ)) * (aliasStep t i : ℤ)))))
      (fun j => (gridValC_gridIntC (hY _)).symm) hsw
    rw [solveRowF_getD i _ hs, solveRowF_getD i _ hs, solveRowF_getD i _ hs]
    refine colFits_congr (fun k hk => ?_) hL hcol
    have hkR : k * aliasStep t i + s < totalLen t := by rw [hRw]; exact row_lt hk hs2
    rw [fwd_getD hshape i (P + 2) Y hk hs ⟨k * aliasStep t i + s, hkR⟩
      (by show k * aliasStep t i + s = _; rw [hw])]
    have hsf := shiftFin_cycle hRw f hf' hs2 hk
    rw [show shiftFin f _ = (⟨_, hkR⟩ : Fin (totalLen t)) from Fin.ext hsf]
  · intro s hs
    have hs2 : solveM t i + s < aliasStep t i := by omega
    have hsR : solveM t i + s < totalLen t := by
      rw [hRw]; exact row_lt (k := 0) hL hs2 |>.trans_le' (by simp)
    set f : Fin (totalLen t) := ⟨solveM t i + s, hsR⟩ with hfdef
    have hf' : (f : ℕ) = 0 * aliasStep t i + (solveM t i + s) := by simp [hfdef]
    have hfw : (f : ℕ) / aliasStep t i = 0 := by rw [hf']; exact (div_mod_row hs2).1
    have hfm : (f : ℕ) % aliasStep t i = solveM t i + s := by rw [hf']; exact (div_mod_row hs2).2
    have hdig : (solveM t i + s) / suffixProd t i = t i / 2 + s / solveU t i := by
      rw [hMσ, hU, Nat.add_comm, Nat.add_mul_div_right _ _ hσ, Nat.add_comm]
    have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) = t i / 2 + s / solveU t i := by
      rw [LemmaBInverse.encFreq_digit_eq hshape i, hfm, hdig]
    have hsu : s / solveU t i < t i / 2 := by
      rw [hU, Nat.div_lt_iff_lt_mul hσ, ← hMσ]; exact hs
    have h2u : ¬ (2 * (t i / 2 + s / solveU t i) < t i) :=
      Nat.not_lt.2 (by rw [Nat.mul_add, ht2]; exact Nat.le_add_right _ _)
    obtain ⟨hmu, ha, hg⟩ := htabi (t i / 2 + s / solveU t i) (by omega)
    have hsw := hfit f
    rw [hu, hfw, if_neg h2u, realInt_spec hmu, realInt_spec ha, realInt_spec hg] at hsw
    have hcol := colFits_of_sweepFits
      (Ys := fun j : ℕ => gridInt (P + 2) (reorientIn (prefixProd t i)
        (fun j : ℕ => Y (shiftFin f (((j : ℤ) - ((0 : ℕ) : ℤ)) * (aliasStep t i : ℤ)))) j))
      (fun j => (gridValC_gridIntC (hY _)).symm) hsw
    rw [solveRowB_getD i _ hs, solveRowB_getD i _ hs, solveRowB_getD i _ hs]
    refine colFits_congr (fun k hk => ?_) hL hcol
    simp only [reorientIn]
    rw [imod_one_sub (le_of_lt hk)]
    have hm : (prefixProd t i + 1 - k) % prefixProd t i < prefixProd t i := Nat.mod_lt _ hL
    have hkR : (prefixProd t i + 1 - k) % prefixProd t i * aliasStep t i + (solveM t i + s) <
        totalLen t := by rw [hRw]; exact row_lt hm hs2
    rw [bwd_getD hshape i (P + 2) Y hk hs ⟨_, hkR⟩
      (by show _ * aliasStep t i + (solveM t i + s) = _; rw [hw]; ring)]
    have hsf := shiftFin_cycle hRw f hf' hs2 hm
    rw [show shiftFin f _ = (⟨_, hkR⟩ : Fin (totalLen t)) from Fin.ext hsf]

end SubNLogN.Machine.Bridge
