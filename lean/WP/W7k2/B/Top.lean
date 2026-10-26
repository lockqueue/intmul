import WP.W7k2.B.Fix
import WP.W7k2.B.Inst
import Contracts.W7.Tables

/-!
# WP.W7k2.B.Top — the table builder: init, levels, final; the `W7_buildTablesRef` wrapper

Top-level initialization, recursion, and finalization of the W7k2 table builder.

* `buildProg I`: push a `mark` floor on the scratch stacks (`pushMarks floorSlots`), set up the level
  registers `vL := min L K`, `vp := p`, `vK := K` (and `vpI := 0`, `STG := []` implicitly), run
  the levels (`levels`, B/Fix), restore `STG`'s floor and pop all floors.
* `buildProg_spec`: from the contract's input stacks to `TR := tapeFromC 0 L p K ++ TR`, at cost
  `levelSum … + 4·C·(|L| + |p| + |K| + 1) + 70`.
  - init: `HT.pushMarks` + `marked_floor`, `HT.bmin`, two `HT.bcp`, then `init_eq` (the level state
    `LS S (min L K) p K 0 [] (S TR)`);
  - final: `HT.pushS` + `FS_mark_eq`, then `HT.popMarks` + `marked_floor`;
  - `tapeFromC_min` turns the fuel `min L K` back into `L`.
* `W7_buildTablesRef_holds`: the `MContract` wrapper (instances from `exists_BI`, B/Inst), with the
  cost from `levels_cost_le` (B/LevelSum) and the tape from `tape_ref_eq` (Canon/Tape).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- **The table builder.** -/
def buildProg (I : BI) : BP I :=
  (pushMarks I floorSlots).seq <| (bmin I sLin sKin vL).seq <| (bcp I sPin vp).seq <|
  (bcp I sKin vK).seq <| (levels I).seq <| (pushS sSTG .mark).seq (popMarks I floorSlots)

theorem buildProg_closed (I : BI) : (buildProg I).Closed :=
  ⟨pushMarks_closed I floorSlots, bmin_closed I sLin sKin vL, callI_closed _ _ _ _,
    callI_closed _ _ _ _, levels_closed I, trivial, popMarks_closed I floorSlots⟩

section Top

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

/-- After the initialisation the stacks are the level state `LS S (min L K) p K 0 [] (S TR)`. -/
theorem init_eq (S : BL → List Sym) (Lc p K : ℕ) :
    Function.update (Function.update (Function.update (Bf S) vL (natSyms Lc ++ Bf S vL)) vp
        (natSyms p ++ Bf S vp)) vK (natSyms K ++ Bf S vK) = LS S Lc p K 0 [] (S sTR) := by
  funext g
  by_cases h1 : g = vK
  · subst h1
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_floor]
  by_cases h2 : g = vp
  · subst h2
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_floor]
  by_cases h3 : g = vL
  · subst h3
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_floor]
  by_cases h4 : g = vpI
  · subst h4
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_floor,
      natSyms_zero, List.nil_append]
  by_cases h5 : g = sSTG
  · subst h5
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_floor,
      List.nil_append]
  by_cases h6 : g = sTR
  · subst h6
    simp (disch := decide) only [LS, Function.update_self, Function.update_of_ne, Bf_nofloor]
  · simp only [LS, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]

/-- Pushing `mark` back on `STG` after the levels gives the floored state over the output stacks. -/
theorem FS_mark_eq (S : BL → List Sym) (tr : List Sym) :
    Function.update (FS S tr) sSTG (Sym.mark :: S sSTG) = Bf (Function.update S sTR tr) := by
  funext g
  by_cases h1 : g = sSTG
  · subst h1
    simp (disch := decide) only [Function.update_self, Bf_floor, Function.update_of_ne]
  by_cases h2 : g = sTR
  · subst h2
    simp (disch := decide) only [FS, Function.update_self, Function.update_of_ne, Bf_nofloor]
  · simp only [FS, Bf, Function.update_of_ne h1, Function.update_of_ne h2]

/-- The level invariant `K ≤ 2^(Lc+1)` at the fuel `Lc = min L K`. -/
theorem le_two_pow_min (L K : ℕ) (hK : K ≤ 2 ^ (L + 1)) : K ≤ 2 ^ (min L K + 1) := by
  rcases le_total L K with h | h
  · rw [Nat.min_eq_left h]
    exact hK
  · rw [Nat.min_eq_right h]
    exact le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The builder's run.** -/
theorem buildProg_spec (hI : I.Spec Mul C) (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (L p K : ℕ) (rL rp rK : List Sym) (S : BL → List Sym) (hp : 8 ≤ p) (hK : K ≤ 2 ^ (L + 1))
    (h1 : TermOK rL) (h2 : TermOK rp) (h3 : TermOK rK) (e1 : S sLin = natSyms L ++ rL)
    (e2 : S sPin = natSyms p ++ rp) (e3 : S sKin = natSyms K ++ rK) :
    HT [] S (buildProg I) (Function.update S sTR (tapeFromC 0 L p K ++ S sTR))
      (levelSum (stepLvG C KM) (leafLvG C KM) 0 (min L K) p K +
        4 * (C * (bitLen L + bitLen p + bitLen K + 1)) + 70) := by
  have bL : Bf S sLin = natSyms L ++ rL := by rw [Bf_nofloor S sLin (by decide)]; exact e1
  have bP : Bf S sPin = natSyms p ++ rp := by rw [Bf_nofloor S sPin (by decide)]; exact e2
  have bK : Bf S sKin = natSyms K ++ rK := by rw [Bf_nofloor S sKin (by decide)]; exact e3
  -- init
  have i0 : HT [] S (pushMarks I floorSlots) (Bf S) (floorSlots.length + 1) := by
    have h := HT.pushMarks (I := I) [] floorSlots S
    rw [marked_floor] at h
    exact h
  have i1 := HT.bmin hI sLin sKin vL (by decide) (Bf S) L K rL rK h1 h3 bL bK []
  have i2 : HT [] (Function.update (Bf S) vL (natSyms (min L K) ++ Bf S vL)) (bcp I sPin vp)
      (Function.update (Function.update (Bf S) vL (natSyms (min L K) ++ Bf S vL)) vp
        (natSyms p ++ Bf S vp)) (C * (bitLen p + 1)) :=
    (HT.bcp hI sPin vp (by decide) _ p rp h2
      (by rw [Function.update_of_ne (by decide)]; exact bP) []).of_eq
      (by rw [Function.update_of_ne (show vp ≠ vL by decide)]) le_rfl
  have i3 : HT [] (Function.update (Function.update (Bf S) vL (natSyms (min L K) ++ Bf S vL)) vp
        (natSyms p ++ Bf S vp)) (bcp I sKin vK) (LS S (min L K) p K 0 [] (S sTR))
      (C * (bitLen K + 1)) :=
    (HT.bcp hI sKin vK (by decide) _ K rK h3
      (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact bK)
      []).of_eq
      (by rw [Function.update_of_ne (show vK ≠ vp by decide),
        Function.update_of_ne (show vK ≠ vL by decide), init_eq]) le_rfl
  -- levels
  have i4 := (levels_spec hI KM hMul S [] (min L K) p K 0 [] (S sTR) hp (le_trans (Nat.min_le_right L K) (Nat.le_add_left K p))
    (le_two_pow_min L K hK) (Nat.zero_le _) (by simp)).of_eq
    (show FS S (([] : List Sym).reverse ++ (tapeFromC 0 (min L K) p K ++ S sTR)) =
      FS S (tapeFromC 0 (min L K) p K ++ S sTR) by simp only [List.reverse_nil, List.nil_append])
    le_rfl
  -- final
  have hF : FS S (tapeFromC 0 (min L K) p K ++ S sTR) sSTG = S sSTG := by
    simp only [FS, Function.update_self]
  have i5 : HT ([] : List (BP I)) (FS S (tapeFromC 0 (min L K) p K ++ S sTR))
      (pushS (σ := I.R) sSTG .mark)
      (Bf (Function.update S sTR (tapeFromC 0 (min L K) p K ++ S sTR))) 1 :=
    (HT.pushS sSTG .mark (FS S (tapeFromC 0 (min L K) p K ++ S sTR)) ([] : List (BP I))).of_eq
      (by rw [hF, FS_mark_eq]) le_rfl
  have i6 := HT.popMarks (I := I) []
    (Function.update S sTR (tapeFromC 0 (min L K) p K ++ S sTR)) floorSlots (by decide)
  rw [marked_floor] at i6
  refine (HT.seq i0 (HT.seq i1 (HT.seq i2 (HT.seq i3 (HT.seq i4 (HT.seq i5 i6)))))).of_eq
    (by rw [← tapeFromC_min 0 L p K (by omega)]) ?_
  have hfl : floorSlots.length = 31 := rfl
  have hnil : ([] : List Sym).length = 0 := rfl
  have a1 : C * (bitLen L + bitLen K + 1) ≤ C * (bitLen L + bitLen p + bitLen K + 1) :=
    Nat.mul_le_mul_left C (by omega)
  have a2 : max (C * (bitLen L + 1)) (C * (bitLen K + 1)) ≤
      C * (bitLen L + bitLen p + bitLen K + 1) :=
    max_le (Nat.mul_le_mul_left C (by omega)) (Nat.mul_le_mul_left C (by omega))
  have a3 : C * (bitLen p + 1) ≤ C * (bitLen L + bitLen p + bitLen K + 1) :=
    Nat.mul_le_mul_left C (by omega)
  have a4 : C * (bitLen K + 1) ≤ C * (bitLen L + bitLen p + bitLen K + 1) :=
    Nat.mul_le_mul_left C (by omega)
  omega

end Top

/-- **`W7_buildTablesRef` for the snapshot schedule** (the W7k2 deliverable). -/
theorem W7_buildTablesRef_holds : ∀ Mul : ℕ → ℕ, W5_mulAt Mul →
    (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
    W7_buildTablesRef W7.snapshotSchedule := by
  intro Mul hmul hMulG hyps hk
  obtain ⟨KM, hKM⟩ := hMulG
  obtain ⟨I, C, hC, hI⟩ := exists_BI Mul hmul hyps hk
  refine ⟨(3000 * (C * (KM + 1)) + 6) + 4 * C + 70, fun _ => ⟨32, I.R, fun _ => (), buildProg I,
    le_rfl, I.R_finite, I.R_nonempty, buildProg_closed I, ?_⟩⟩
  intro L p K rL rp rK S hp hK h1 h2 h3 e1 e2 e3
  have hb := buildProg_spec hI KM hKM L p K rL rp rK S hp hK h1 h2 h3 e1 e2 e3
  have hc := levels_cost_le C KM L p K hC hp
  rw [tape_ref_eq]
  refine HT.runs (hb.mono ?_)
  set A := 3000 * (C * (KM + 1)) + 6 with hA
  set PC := (buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost with hPC
  set TL := (tapeFromC 0 L p K).length with hTL
  set Y := PC + TL + bitLen L + bitLen p + bitLen K + 1 with hY
  have hY1 : PC + TL + 1 ≤ Y := by omega
  have hY2 : bitLen L + bitLen p + bitLen K + 1 ≤ Y := by omega
  have m1 : A * (PC + TL + 1) ≤ A * Y := Nat.mul_le_mul_left A hY1
  have m2 : 4 * C * (bitLen L + bitLen p + bitLen K + 1) ≤ 4 * C * Y := Nat.mul_le_mul_left _ hY2
  have m3 : 70 ≤ 70 * Y := by omega
  have e : (A + 4 * C + 70) * Y = A * Y + 4 * C * Y + 70 * Y := by ring
  have e2 : 4 * (C * (bitLen L + bitLen p + bitLen K + 1)) =
      4 * C * (bitLen L + bitLen p + bitLen K + 1) := by ring
  rw [e, e2]
  omega

#assert_std_axioms buildProg_closed init_eq FS_mark_eq le_two_pow_min buildProg_spec
  W7_buildTablesRef_holds

end WP.W7k2
