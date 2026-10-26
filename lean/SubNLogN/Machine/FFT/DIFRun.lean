/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFFacts

/-!
# K4-DIF, the whole run (`Machine/FFT/DIFRun.lean`)

**Scope (honest summary).** `runs_main` (proved, no `sorry`): conditional on the two arithmetic
sub-kernels given as `HSDSpec`/`CMSpec` hypotheses on given programs, the kernel `mainProg`
turns the data stack `carrSyms w (encCube q z) ++ rest` into
`carrSyms w (encCube q (lastAxisFFT q ℓ θt z)) ++ rest` (`lastAxisFFT`,
`Math/Walsh/DirectFFT.lean:73`), leaves every other stack as it was (private scratch empty at
both ends), within `setup + ℓ·(LB + 2) + 2 + ℓ·(BB + 2) + 2 + (4V + 2) + cleanup` steps.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Common SubNLogN.Math.Walsh

/-- Cost of the cleanup. -/
def cleanupCost (w q ℓ : ℕ) : ℕ :=
  (3 * (2 * w) + 2) + ((3 * bitLen w + 2) + ((3 * bitLen w + 2) + ((3 * bitLen w + 2) +
    ((3 * bitLen q + 2) + (3 * (2 ^ (ℓ + 1) - 1) + 2)))))

theorem encCube_cons (q ℓ m : ℕ) (z : RArr (Cube m) (2 ^ ℓ)) :
    ∃ row0 Brest, encCube q z = row0 :: Brest ∧ row0.length = 2 ^ ℓ := by
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ m = n + 1 := ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
  refine ⟨(List.finRange (2 ^ ℓ)).map fun k => gridInt q (z (cubeOfNat m 0) k),
    ((List.range n).map (fun i => cubeOfNat m (i + 1))).map fun x =>
      (List.finRange (2 ^ ℓ)).map fun k => gridInt q (z x k), ?_, by simp⟩
  simp only [encCube, encArr, cubeAddrs, hn, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem tabInt_cons (q ℓ : ℕ) (θt : ℕ → ℂ) :
    ∃ tl, tabInt q ℓ θt = gridInt q (θt 0) :: tl := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * 2 ^ ℓ = n + 1 := ⟨2 * 2 ^ ℓ - 1, by have := Nat.one_le_two_pow (n := ℓ); omega⟩
  have h : tabInt q ℓ θt = gridInt q (θt 0) ::
      List.map (fun j => gridInt q (θt j)) (List.map Nat.succ (List.range n)) := by
    simp only [tabInt, hn, List.range_succ_eq_map, List.map_cons]
  exact ⟨_, h⟩

theorem ncoef_uniform (v : List (List CInt)) (k : ℕ) (h : ∀ row ∈ v, row.length = k) :
    ncoef v = v.length * k := by
  unfold ncoef
  rw [List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

section Main

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ Rh Rc : Type}

set_option maxHeartbeats 4000000 in
theorem runs_main (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc) {Ch Cc : ℕ}
    {Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh} {Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc}
    (hHSD : HSDSpec Eh Rh Ch Ph) (hCM : CMSpec Ec Rc Cc Pc)
    (S : KD Eh Ec → List Sym) (hclean : ∀ e : DS ⊕ (Eh ⊕ Ec), S (.inr e) = [])
    (q ℓ m f1 f2 f3 w : ℕ) (hr : List Sym) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))
    (rest trest : List Sym) (hqw : q + 2 ≤ w)
    (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z)
    (hrest : BlkTerm rest)
    (hD : S nD = carrSyms w (encCube q z) ++ rest)
    (hH : S nH = natSyms q ++ Sym.mark :: (natSyms f1 ++ Sym.mark :: (natSyms f2 ++ Sym.mark ::
      (natSyms f3 ++ Sym.mark :: (natSyms w ++ Sym.mark :: hr)))))
    (hTB : S nTB = carrSyms w ((tabInt q ℓ θt).map fun c => [c]) ++ trest) :
    Runs (mainProg lO lh lc Ph Pc) S
      (Function.update S nD (carrSyms w (encCube q (lastAxisFFT q ℓ θt z)) ++ rest))
      (fun _ => True)
      (setupCost q f1 f2 f3 w ℓ (carrSyms w (encCube q z)).length +
        (ℓ * (LB Ch Cc w q (2 ^ m * 2 ^ ℓ) + 2) + 2 +
        (ℓ * (BB w (2 ^ m * 2 ^ ℓ) + 2) + 2 +
        (4 * (carrSyms w (encCube q (lastAxisFFT q ℓ θt z))).length + 2 +
        cleanupCost w q ℓ)))) := by
  have hw : 1 ≤ w := by omega
  obtain ⟨row0, Brest, hB0c, hrow0⟩ := encCube_cons q ℓ m z
  obtain ⟨tl, htl⟩ := tabInt_cons q ℓ θt
  have hTB' : S nTB = (crecBits w [gridInt q (θt 0)]).map Sym.bit ++ Sym.sep ::
      (carrSyms w (tl.map fun c => [c]) ++ trest) := by
    rw [hTB, htl, List.map_cons, carrSyms_eq, List.map_cons, arrSyms_cons', recSyms_eq]
    simp [carrSyms_eq]
  -- the setup
  have e1 := runs_setup lO S (fun d => hclean (.inl d)) q f1 f2 f3 w ℓ hr hw (encCube q z) row0
    Brest hB0c hrow0 (gridInt q (θt 0)) rest _ hrest hD hH hTB'
  set S0 := baseState S w q rest with hS0
  have cl : ∀ d : DS, S (Sum.inr (Sum.inl d)) = [] := fun d => hclean (.inl d)
  have hbase : BaseOK S0 w q ((tabInt q ℓ θt).map fun c => crecBits w [c]) trest := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hS0, baseState, hTB, carrSyms_eq, List.map_map, Function.comp_def]
    · simp [hS0, baseState]
    · simp [hS0, baseState]
    · simp [hS0, baseState]
    · simp [hS0, baseState]
    · simp [hS0, baseState]
    · intro d h1 h2 h3 h4 h5
      simp [hS0, baseState, ds, nD, h1, h2, h3, h4, h5, cl]
    · intro e
      simp [hS0, baseState, ds, nD, hclean]
  have hS0P : S0 (ds .P) = [] := hbase.empty .P (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hS0Q : S0 (ds .Q) = [] := hbase.empty .Q (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hS0RA : S0 (ds .RA) = [] := hbase.empty .RA (by decide) (by decide) (by decide)
    (by decide) (by decide)
  -- the level loop
  have hL := runs_ploop_const lO (ds .HC) Option.isSome (levelBody lO lh lc Ph Pc) ℓ
    (fun s => lvState S0 w (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)) (2 ^ ℓ / 2 ^ (s + 1))
      (2 ^ (s + 1) - 1) s) (LB Ch Cc w q (2 ^ m * 2 ^ ℓ)) ?_ ?_
  rotate_left
  · intro s hs
    show ((lvState S0 w _ (2 ^ ℓ / 2 ^ (s + 1)) (2 ^ (s + 1) - 1) s) (ds .HC)).head?.isSome =
      decide (s < ℓ)
    rw [lvState, upd4_2 (by simp) (by simp), isSome_head?_replicate]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      by_contra hc
      have : 2 ^ ℓ < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt this] at h
      omega
    · intro h
      exact Nat.div_pos (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
  · intro s hs
    obtain ⟨hlen, hrow, hfB, hfT, hfY, hfZ⟩ := level_facts q ℓ m w θt z hqw hθ hz s hs
    have hh : 2 ^ ℓ / 2 ^ (s + 1) = 2 ^ (ℓ - s - 1) := by
      rw [Nat.pow_div (by omega) (by norm_num)]
      congr 1
    have hq1 : 2 ^ (s + 1) - 1 + 1 = 2 ^ (s + 1) := by
      have := Nat.one_le_two_pow (n := s + 1)
      omega
    have hpow3 : 2 ^ (ℓ - s - 1) * 2 ^ (s + 1) = 2 ^ ℓ := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hk : 2 ^ (ℓ - s - 1) * (2 ^ (s + 1) - 1 + 1) ≤ (tabInt q ℓ θt).length := by
      rw [hq1, hpow3]
      simp [tabInt]
    have e := runs_levelBody lO lh lc hHSD hCM S0 w q (tabInt q ℓ θt) trest hbase hw
      (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)) (2 ^ m * 2 ^ s) (2 ^ (ℓ - s - 1))
      (2 ^ (s + 1) - 1) s hlen hrow hk hfB (by rw [hq1]; exact hfT) hfY (by rw [hq1]; exact hfZ)
    rw [hq1] at e
    have hhalf : 2 ^ (ℓ - s - 1) / 2 = 2 ^ ℓ / 2 ^ (s + 1 + 1) := by
      rw [← hh, Nat.div_div_eq_div_mul, ← pow_succ]
    have hqc : 2 * (2 ^ (s + 1) - 1) + 1 = 2 ^ (s + 1 + 1) - 1 := by
      have := Nat.one_le_two_pow (n := s + 1)
      rw [pow_succ 2 (s + 1)]
      omega
    rw [hhalf, hqc] at e
    have hNh : 2 ^ m * 2 ^ s * (2 * 2 ^ (ℓ - s - 1)) = 2 ^ m * 2 ^ ℓ := by
      rw [show 2 ^ m * 2 ^ s * (2 * 2 ^ (ℓ - s - 1)) = 2 ^ m * (2 ^ (ℓ - s - 1) * 2 ^ (s + 1)) by
        rw [pow_succ]; ring, hpow3]
    have hYsh := zipC_halves_shape halfDiffC (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z))
      (2 ^ (ℓ - s - 1)) hrow
    have hstl : (stageB (tabInt q ℓ θt) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1))).length = 2 ^ (ℓ - s - 1) := by
      simp [stageB]
    have hcost := levelCost_le Ch Cc w q (2 ^ m * 2 ^ s) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1) - 1)
      (2 ^ ℓ) (2 ^ m * 2 ^ ℓ)
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.take (2 ^ (ℓ - s - 1))))
      ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map (List.drop (2 ^ (ℓ - s - 1))))
      (zipC halfDiffC ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map
        (List.take (2 ^ (ℓ - s - 1)))) ((levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)).map
        (List.drop (2 ^ (ℓ - s - 1)))))
      (List.replicate (2 ^ m * 2 ^ s) (stageB (tabInt q ℓ θt) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1))))
      hw Nat.one_le_two_pow (Nat.one_le_iff_ne_zero.mpr (by positivity)) hNh (by rw [hq1, hpow3])
      (Nat.le_mul_of_pos_left _ (by positivity))
      (by rw [cvol_eq, ncoef_uniform _ (2 ^ (ℓ - s - 1)) (fun row hr => by
            obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hr
            rw [List.length_take, hrow blk hb]; omega), List.length_map, hlen])
      (by rw [cvol_eq, ncoef_uniform _ (2 ^ (ℓ - s - 1)) (fun row hr => by
            obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 hr
            rw [List.length_drop, hrow blk hb]; omega), List.length_map, hlen])
      (by rw [cvol_eq, ncoef_uniform _ (2 ^ (ℓ - s - 1)) hYsh.2, hYsh.1, hlen])
      (by rw [cvol_eq, ncoef_uniform _ (2 ^ (ℓ - s - 1)) (fun row hr => by
            rw [List.eq_of_mem_replicate hr, hstl]), List.length_replicate])
      (by rw [ncoef_uniform _ (2 ^ (ℓ - s - 1)) hYsh.2, hYsh.1, hlen])
    show Runs _ (lvState S0 w (levelsB q ℓ (tabInt q ℓ θt) s (encCube q z)) (2 ^ ℓ / 2 ^ (s + 1))
      (2 ^ (s + 1) - 1) s) _ _ _
    rw [hh]
    exact runs_mono e (fun _ _ => trivial) hcost
  -- the bit-reversal loop
  have hBR := runs_ploop_const lO (ds .LC) Option.isSome (brBody lO) ℓ
    (fun t => upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC)
      (carrSyms w (brIter t (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)))).reverse []
      (List.replicate (2 ^ (ℓ + 1) - 1) .mark) (List.replicate (ℓ - t) .mark))
    (BB w (2 ^ m * 2 ^ ℓ)) ?_ ?_
  rotate_left
  · intro t ht
    show ((upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) _ [] _
      (List.replicate (ℓ - t) .mark)) (ds .LC)).head?.isSome = decide (t < ℓ)
    rw [upd4_4, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro t ht
    obtain ⟨A, Bb, hIt, hlen, hAl, hA, hB, hIt1⟩ := br_facts q ℓ m θt z hθ hz t ht
    have e := runs_brBody lO S0 w hw hS0P hS0Q hbase.rc hS0RA A Bb (2 ^ t) (2 ^ (ℓ + 1) - 1)
      (ℓ - t - 1) hlen hA hB
    rw [← hIt, ← hIt1, show ℓ - t - 1 + 1 = ℓ - t by omega] at e
    have hcost := brCost_le w (2 ^ t) A.length (2 ^ m * 2 ^ ℓ) hw Nat.one_le_two_pow (by
      rw [hAl, show 2 ^ m * 2 ^ (ℓ - t - 1) * (2 * 2 ^ t) = 2 ^ m * 2 ^ (ℓ - t - 1 + 1 + t) by
        rw [pow_add, pow_succ]; ring]
      congr 2
      omega)
    refine runs_congr (runs_mono e (fun _ _ => trivial) hcost) ?_
    show upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) _ [] _ (List.replicate (ℓ - t - 1) .mark) =
      upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) _ [] _ (List.replicate (ℓ - (t + 1)) .mark)
    rw [show ℓ - (t + 1) = ℓ - t - 1 by omega]
  -- glue the loops
  have hLend : lvState S0 w (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) (2 ^ ℓ / 2 ^ (ℓ + 1))
      (2 ^ (ℓ + 1) - 1) ℓ = upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC)
      (carrSyms w (brIter 0 (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)))).reverse []
      (List.replicate (2 ^ (ℓ + 1) - 1) .mark) (List.replicate (ℓ - 0) .mark) := by
    have h0 : 2 ^ ℓ / 2 ^ (ℓ + 1) = 0 :=
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [h0, lvState]
    rfl
  have hL0 : lvState S0 w (levelsB q ℓ (tabInt q ℓ θt) 0 (encCube q z)) (2 ^ ℓ / 2 ^ (0 + 1))
      (2 ^ (0 + 1) - 1) 0 = lvState S0 w (encCube q z) (2 ^ ℓ / 2) 1 0 := rfl
  rw [hL0, hLend] at hL
  -- the final rewind
  set Bf := brIter ℓ (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) with hBf
  have hBf' : Bf = encCube q (lastAxisFFT q ℓ θt z) := pipeline_correct q ℓ m θt z hθ hz
  set X := upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) (carrSyms w Bf).reverse []
    (List.replicate (2 ^ (ℓ + 1) - 1) .mark) (List.replicate (ℓ - ℓ) .mark) with hX
  have e4 := runs_revArr_in lO (src := ds .T) (dst := nD) (by simp) X (Bf.map (crecBits w))
    (by rw [hX, upd4_1 (by simp) (by simp) (by simp), carrSyms_eq])
  have hXD : X nD = rest := by simp [hX, upd4, hS0, baseState]
  rw [hXD, ← carrSyms_eq, hBf'] at e4
  set X1 := Function.update (Function.update X (ds .T) []) nD
    (carrSyms w (encCube q (lastAxisFFT q ℓ θt z)) ++ rest) with hX1
  -- the cleanup
  have c1 := runs_drain lO (ds .RC) X1
  have hX1RC : X1 (ds .RC) = List.replicate (2 * w) .mark := by
    simp [hX1, hX, upd4, hS0, baseState]
  rw [hX1RC, List.length_replicate] at c1
  set X2 := Function.update X1 (ds .RC) [] with hX2
  have c2 := runs_drain lO (ds .W1) X2
  have hX2W1 : X2 (ds .W1) = natSyms w := by simp [hX2, hX1, hX, upd4, hS0, baseState]
  rw [hX2W1, length_natSyms] at c2
  set X3 := Function.update X2 (ds .W1) [] with hX3
  have c3 := runs_drain lO (ds .W2) X3
  have hX3W2 : X3 (ds .W2) = natSyms w := by simp [hX3, hX2, hX1, hX, upd4, hS0, baseState]
  rw [hX3W2, length_natSyms] at c3
  set X4 := Function.update X3 (ds .W2) [] with hX4
  have c4 := runs_drain lO (ds .W3) X4
  have hX4W3 : X4 (ds .W3) = natSyms w := by
    simp [hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState]
  rw [hX4W3, length_natSyms] at c4
  set X5 := Function.update X4 (ds .W3) [] with hX5
  have c5 := runs_drain lO (ds .QS) X5
  have hX5QS : X5 (ds .QS) = natSyms q := by
    simp [hX5, hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState]
  rw [hX5QS, length_natSyms] at c5
  set X6 := Function.update X5 (ds .QS) [] with hX6
  have c6 := runs_drain lO (ds .QC) X6
  have hX6QC : X6 (ds .QC) = List.replicate (2 ^ (ℓ + 1) - 1) .mark := by
    simp [hX6, hX5, hX4, hX3, hX2, hX1, hX, upd4]
  rw [hX6QC, List.length_replicate] at c6
  refine runs_congr (runs_seq' e1 (runs_seq' hL (runs_seq' hBR (runs_seq' e4
    (runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_seq' c5 c6))))))))) ?_
  funext x
  rcases x with (i | (d | (e | e)))
  · fin_cases i <;>
      simp [hX6, hX5, hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState, Function.update_apply, nD,
        nH, nTB, ds]
  · cases d <;>
      simp [hX6, hX5, hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState, Function.update_apply, ds,
        nD, cl]
  · simp [hX6, hX5, hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState, Function.update_apply, ds, nD]
  · simp [hX6, hX5, hX4, hX3, hX2, hX1, hX, upd4, hS0, baseState, Function.update_apply, ds, nD]

end Main

end SubNLogN.Machine.FFT.DIF
