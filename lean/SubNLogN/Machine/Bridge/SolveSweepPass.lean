/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepRow
import SubNLogN.Machine.Bridge.SolveSweepCol

/-!
# K5-SOLVE (1l): the passes of the sweep kernel

* `prePass`: prefix row `0` (`r1`), then rows `1..L-1` (`r2`) while data remain;
* `r3` and the rewind of the `b` stream (`bS → bS2`);
* `secPass`: second-pass rows (`r4`) while the `b` stream is non-empty;
* `finPass`: drop the last second-pass row (lockstep erase with the state row), then emit the
  closure row and the second-pass rows `0..L-2` onto `dst`.
`runs_sweepBody`: the whole body maps the input state to `dst = sweepHalfI … ++ old dst`.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

theorem zPrev_zero (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) :
    zPrev q M mus nas ys c 0 = c := rfl

theorem zPrev_succ (q M : ℕ) (mus nas : List ℤ) (ys c : List CInt) (k : ℕ) :
    zPrev q M mus nas ys c (k + 1) = secRows q M mus nas ys c k := rfl

/-! ## Input bundles and width facts -/

/-- The input state of the sweep on its data/work stacks. -/
structure SwIn (V : SwD ⊕ SwW → List Sym) (wI wT : ℕ) (ys : List CInt) (mus nas gms : List ℤ)
    (rdat rmu rna rgm : List Sym) : Prop where
  dat : V (.inl .dat) = rec1s wI ys ++ rdat
  mu : V (.inl .mu) = rec1s wT (mus.map toP) ++ rmu
  na : V (.inl .na) = rec1s wT (nas.map toP) ++ rna
  gm : V (.inl .gm) = rec1s wT (gms.map toP) ++ rgm
  work : ∀ w, V (.inr w) = []

/-- The width premises of the sweep. -/
structure SwFits (q wI wT L M : ℕ) (ys : List CInt) (mus nas gms : List ℤ) : Prop where
  y : ∀ y ∈ ys, Fits2 wI y
  mu : ∀ m ∈ mus, FitsTwos wT m
  na : ∀ m ∈ nas, FitsTwos wT m
  gm : ∀ m ∈ gms, FitsTwos wT m
  col : ∀ s, s < M → ColFitsI wI q (mus.getD s 0) (nas.getD s 0) (gms.getD s 0) L
    (fun j => ys.getD (j * M + s) 0)

theorem fits2_getD {w : ℕ} {l : List CInt} (h : ∀ y ∈ l, Fits2 w y) (s : ℕ) :
    Fits2 w (l.getD s 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[s]? with
  | none => exact ⟨fitsTwos_zero, fitsTwos_zero⟩
  | some y => exact h y (List.mem_of_getElem? hx)

theorem fitsT_getD {w : ℕ} {l : List ℤ} (h : ∀ m ∈ l, FitsTwos w m) (s : ℕ) :
    FitsTwos w (l.getD s 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[s]? with
  | none => exact fitsTwos_zero
  | some y => exact h y (List.mem_of_getElem? hx)

section FitsRows

variable {q wI wT L M : ℕ} {ys : List CInt} {mus nas gms : List ℤ}

theorem row1Fits_of (hF : SwFits q wI wT L M ys mus nas gms) (hL : 1 ≤ L) :
    Row1Fits q wI wT M mus (rowOf M ys 0) where
  y s hs := by rw [rowOf_getD M ys 0 s hs]; exact fits2_getD hF.y _
  mu s _ := fitsT_getD hF.mu s
  b s hs := by rw [rowOf_getD M ys 0 s hs]; exact ((hF.col s hs).2 0 (by omega)).1

theorem row2Fits_of (hF : SwFits q wI wT L M ys mus nas gms) (k : ℕ) (hk : k + 1 < L) :
    Row2Fits q wI wT M mus nas (rowOf M ys (k + 1)) (prefRows q M mus nas ys k) where
  y s hs := by rw [rowOf_getD M ys (k + 1) s hs]; exact fits2_getD hF.y _
  mu s _ := fitsT_getD hF.mu s
  na s _ := fitsT_getD hF.na s
  p s hs := by
    rw [prefRows_eq, getD_map_range M _ _ s hs]; exact ((hF.col s hs).2 k (by omega)).2.1
  b s hs := by rw [rowOf_getD M ys (k + 1) s hs]; exact ((hF.col s hs).2 (k + 1) hk).1
  p' s hs := by
    rw [rowOf_getD M ys (k + 1) s hs, prefRows_eq, getD_map_range M _ _ s hs]
    exact ((hF.col s hs).2 (k + 1) hk).2.1

theorem row3Fits_of (hF : SwFits q wI wT L M ys mus nas gms) (hL : 1 ≤ L) :
    Row3Fits q wI wT M gms (prefRows q M mus nas ys (L - 1)) where
  gm s _ := fitsT_getD hF.gm s
  p s hs := by
    rw [prefRows_eq, getD_map_range M _ _ s hs]; exact ((hF.col s hs).2 (L - 1) (by omega)).2.1
  c s hs := by rw [prefRows_eq, getD_map_range M _ _ s hs]; exact (hF.col s hs).1

theorem row4Fits_of (hF : SwFits q wI wT L M ys mus nas gms) (k : ℕ) (hk : k < L) :
    Row4Fits q wI wT M nas (bRowI q M mus (rowOf M ys k))
      (zPrev q M mus nas ys (crowOf q L M mus nas gms ys) k) where
  b s hs := by
    rw [bRowI, getD_map_range M _ _ s hs, rowOf_getD M ys k s hs]
    exact ((hF.col s hs).2 k hk).1
  na s _ := fitsT_getD hF.na s
  p s hs := by
    cases k with
    | zero =>
      simp only [zPrev]
      rw [crowOf_eq, getD_map_range M _ _ s hs]
      exact (hF.col s hs).1
    | succ k =>
      rw [zPrev_getD q M mus nas ys _ s hs k, crowOf_eq, getD_map_range M _ _ s hs]
      exact ((hF.col s hs).2 k (by omega)).2.2
  z s hs := by
    cases k with
    | zero =>
      simp only [zPrev]
      rw [bRowI, getD_map_range M _ _ s hs, rowOf_getD M ys 0 s hs, crowOf_eq,
        getD_map_range M _ _ s hs]
      exact ((hF.col s hs).2 0 hk).2.2
    | succ k =>
      rw [bRowI, getD_map_range M _ _ s hs, rowOf_getD M ys (k + 1) s hs,
        zPrev_getD q M mus nas ys _ s hs k, crowOf_eq, getD_map_range M _ _ s hs]
      exact ((hF.col s hs).2 (k + 1) hk).2.2

end FitsRows

theorem decide_pos_sub1 (L M n : ℕ) (hL : 1 ≤ L) (hM : 1 ≤ M) (hn : n ≤ L - 1) :
    decide (0 < L * M - (L - 1 - n + 1) * M) = decide (0 < n) := by
  rw [show L - 1 - n + 1 = L - n by omega, ← Nat.sub_mul, show L - (L - n) = n by omega]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · simp [h, Nat.mul_pos h (by omega : 0 < M)]

theorem decide_pos_sub0 (L M n : ℕ) (hM : 1 ≤ M) (hn : n ≤ L) :
    decide (0 < L * M - (L - n) * M) = decide (0 < n) := by
  rw [← Nat.sub_mul, show L - (L - n) = n by omega]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · simp [h, Nat.mul_pos h (by omega : 0 < M)]

section Passes

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

/-- The prefix pass. -/
def prePass : PS Ecm Erh Eca Rcm Rrh Rca := .seq (r1 G) (whileP lS (.inl .dat) (r2 G))

/-- The second pass. -/
def secPass : PS Ecm Erh Eca Rcm Rrh Rca := whileP lS (.inr .bS2) (r4 G)

/-- The final pass: drop the last second-pass row, then emit. -/
def finPass : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (whileP lS (.inr .stI) (.seq (erP lS (.inr .stI)) (erP lS (.inr .oS))))
    (.seq (drP lS (.inr .cS) (.inl .dst)) (drP lS (.inr .oS) (.inl .dst)))

/-- The sweep body. -/
def sweepBody : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (prePass G) (.seq (.seq (r3 G) (drP lS (.inr .bS) (.inr .bS2))) (.seq (secPass G) finPass))

/-- Prefix-pass state after rows `0..k`. -/
def preV (Vi : SwD ⊕ SwW → List Sym) (q wI M : ℕ) (mus nas : List ℤ) (ys : List CInt)
    (rdat : List Sym) (k : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update Vi
    (.inl .dat) (rec1s wI (ys.drop ((k + 1) * M)) ++ rdat))
    (.inr .stI) (rec1s wI (prefRows q M mus nas ys k)))
    (.inr .bS) (rec1s wI (bAll q M mus ys (k + 1)).reverse)

theorem runs_r1_pre {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm) (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hL : 1 ≤ L)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (trmu : TermOK rmu) (hys : ys.length = L * M) (hmus : mus.length = M)
    (hF : SwFits q wI wT L M ys mus nas gms) :
    Runs (r1 G) (mk base Vi) (mk base (preV Vi q wI M mus nas ys rdat 0)) (fun _ => True)
      (r1Cost Ccm Crh wI wT q M) := by
  have hT : TempsEmpty Vi :=
    ⟨hI.work _, hI.work _, hI.work _, hI.work _, hI.work _, hI.work _, hI.work _⟩
  have hr0 : (rowOf M ys 0).length = M :=
    rowOf_length M ys 0 (by rw [hys, Nat.zero_add]; exact Nat.mul_le_mul_right M hL)
  have hsplit := drop_rowOf M ys 0
  simp only [Nat.zero_mul, List.drop_zero, Nat.zero_add, Nat.one_mul] at hsplit
  have hdat : Vi (.inl .dat) = rec1s wI (rowOf M ys 0) ++ (rec1s wI (ys.drop M) ++ rdat) := by
    rw [hI.dat, ← List.append_assoc, ← rec1s_append, ← hsplit]
  have h := runs_r1 G scm srh hB hwI hwT Vi hT hr0 hmus (row1Fits_of hF hL) hdat hI.mu trmu
    (hI.work _) (hI.work _)
  refine WP.W9comp.runs_congr h ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [preV, Function.update_apply, hI.work, bAll, prefRows]
  · cases w <;> simp [preV, Function.update_apply, hI.work, bAll, prefRows]

theorem runs_r2_pre {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (hys : ys.length = L * M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hF : SwFits q wI wT L M ys mus nas gms) (k : ℕ) (hk : k + 1 < L) :
    Runs (r2 G) (mk base (preV Vi q wI M mus nas ys rdat k))
      (mk base (preV Vi q wI M mus nas ys rdat (k + 1))) (fun _ => True)
      (r2Cost Ccm Crh Cca wI wT q M) := by
  have hT : TempsEmpty (preV Vi q wI M mus nas ys rdat k) := by
    constructor <;> simp [preV, Function.update_apply, hI.work]
  have hr : (rowOf M ys (k + 1)).length = M :=
    rowOf_length M ys (k + 1) (by rw [hys]; exact Nat.mul_le_mul_right M (by omega))
  have hdat : (preV Vi q wI M mus nas ys rdat k) (.inl .dat) =
      rec1s wI (rowOf M ys (k + 1)) ++ (rec1s wI (ys.drop ((k + 1 + 1) * M)) ++ rdat) := by
    rw [← List.append_assoc, ← rec1s_append, ← drop_rowOf]
    simp [preV, Function.update_apply]
  have h := runs_r2 G scm srh sca hB hwI hwT _ hT hr (prefRows_length q M mus nas ys k) hmus hnas
    (row2Fits_of hF k hk) hdat (Mu := rmu) (Na := rna) (St := [])
    (by simp [preV, Function.update_apply, hI.mu]) (by simp [preV, Function.update_apply, hI.na])
    (by simp [preV, Function.update_apply]) TermOK.nil
    (by simp [preV, Function.update_apply, hI.work]) (by simp [preV, Function.update_apply, hI.work])
    (by simp [preV, Function.update_apply, hI.work])
  refine WP.W9comp.runs_congr h ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [preV, Function.update_apply]
  · cases w <;> simp [preV, Function.update_apply, prefRows, bAll, List.reverse_append,
      rec1s_append]

theorem runs_prePass {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hL : 1 ≤ L) (hM : 1 ≤ M)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (trdat : TermOK rdat) (trmu : TermOK rmu)
    (hys : ys.length = L * M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hF : SwFits q wI wT L M ys mus nas gms) :
    Runs (prePass G) (mk base Vi) (mk base (preV Vi q wI M mus nas ys rdat (L - 1)))
      (fun _ => True)
      (r1Cost Ccm Crh wI wT q M + (1 + loopCost (fun _ => r2Cost Ccm Crh Cca wI wT q M + 1)
        (L - 1))) := by
  have h1 := runs_r1_pre G scm srh hB hwI hwT hL hI trmu hys hmus hF
  have htop : ∀ n, n ≤ L - 1 → optIsBit ((mk base (preV Vi q wI M mus nas ys rdat (L - 1 - n)))
      (loc (.inl .dat))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (preV Vi q wI M mus nas ys rdat (L - 1 - n))) (loc (.inl .dat)) =
        rec1s wI (ys.drop ((L - 1 - n + 1) * M)) ++ rdat := by
      simp [preV, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ trdat, List.length_drop, hys]
    exact decide_pos_sub1 L M n hL hM hn
  have hstep : ∀ n, n < L - 1 →
      Runs (r2 G) (mk base (preV Vi q wI M mus nas ys rdat (L - 1 - (n + 1))))
        (mk base (preV Vi q wI M mus nas ys rdat (L - 1 - n))) (fun _ => True)
        (r2Cost Ccm Crh Cca wI wT q M) := by
    intro n hn
    rw [show L - 1 - n = L - 1 - (n + 1) + 1 by omega]
    exact runs_r2_pre G scm srh sca hB hwI hwT hI hys hmus hnas hF (L - 1 - (n + 1)) (by omega)
  have h2 := runs_whileP lS (.inl .dat) (r2 G)
    (fun n => mk base (preV Vi q wI M mus nas ys rdat (L - 1 - n))) (L - 1)
    (fun _ => r2Cost Ccm Crh Cca wI wT q M) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h2
  exact WP.W9comp.runs_seq h1 h2

/-- Second-pass state after `k` rows. -/
def secV (Vi : SwD ⊕ SwW → List Sym) (q wI L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt)
    (rdat : List Sym) (k : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update Vi
    (.inl .dat) rdat)
    (.inr .cS) (rec1s wI (crowOf q L M mus nas gms ys).reverse))
    (.inr .bS2) (rec1s wI ((bAll q M mus ys L).drop (k * M))))
    (.inr .stI) (rec1s wI (zPrev q M mus nas ys (crowOf q L M mus nas gms ys) k)))
    (.inr .oS) (rec1s wI (secAll q M mus nas ys (crowOf q L M mus nas gms ys) k).reverse)

theorem runs_clos {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm) (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hL : 1 ≤ L)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (hys : ys.length = L * M) (hgms : gms.length = M)
    (hF : SwFits q wI wT L M ys mus nas gms) :
    Runs (.seq (r3 G) (drP lS (.inr .bS) (.inr .bS2)))
      (mk base (preV Vi q wI M mus nas ys rdat (L - 1)))
      (mk base (secV Vi q wI L M mus nas gms ys rdat 0)) (fun _ => True)
      (r1Cost Ccm Crh wI wT q M + (L * M * (12 * wI + 12) + 2)) := by
  have hT : TempsEmpty (preV Vi q wI M mus nas ys rdat (L - 1)) := by
    constructor <;> simp [preV, Function.update_apply, hI.work]
  have hLL : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hdrop : ys.drop ((L - 1 + 1) * M) = [] :=
    List.drop_eq_nil_of_le (le_of_eq (by rw [hys, hLL]))
  have hdrop' : ys.drop (L * M) = [] := List.drop_eq_nil_of_le (le_of_eq hys)
  have h3 := runs_r3 G scm srh hB hwI hwT _ hT (prefRows_length q M mus nas ys (L - 1)) hgms
    (row3Fits_of hF hL) (Gm := rgm) (St := []) (by simp [preV, Function.update_apply]) TermOK.nil
    (by simp [preV, Function.update_apply, hI.gm]) (by simp [preV, Function.update_apply, hI.work])
    (by simp [preV, Function.update_apply, hI.work])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h3
    (runs_drP1 lS (x := .inr .bS) (y := .inr .bS2) (by decide) (by decide) (by decide) base _ hwI
      (bAll q M mus ys L).reverse (rx := []) ?h1 TermOK.nil ?h2)) ?he) (fun _ _ => trivial) ?hc
  case h1 => simp [preV, Function.update_apply, hLL]
  case h2 => simp [preV, Function.update_apply, hI.work]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [preV, secV, Function.update_apply, hdrop, hdrop', hLL]
    · cases w <;> simp [preV, secV, Function.update_apply, hI.work, zPrev_zero, secAll, crowOf, hLL]
  case hc => simp only [List.length_reverse, bAll_length, le_refl]

theorem runs_r4_sec {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (hnas : nas.length = M) (hF : SwFits q wI wT L M ys mus nas gms) (k : ℕ) (hk : k < L) :
    Runs (r4 G) (mk base (secV Vi q wI L M mus nas gms ys rdat k))
      (mk base (secV Vi q wI L M mus nas gms ys rdat (k + 1))) (fun _ => True)
      (r4Cost Ccm Crh Cca wI wT q M) := by
  have hT : TempsEmpty (secV Vi q wI L M mus nas gms ys rdat k) := by
    constructor <;> simp [secV, Function.update_apply, hI.work]
  have hb2 : (secV Vi q wI L M mus nas gms ys rdat k) (.inr .bS2) =
      rec1s wI (bRowI q M mus (rowOf M ys k)) ++
        rec1s wI ((bAll q M mus ys L).drop ((k + 1) * M)) := by
    rw [← rec1s_append, ← bAll_drop q M mus ys hk]
    simp [secV, Function.update_apply]
  have h := runs_r4 G scm srh sca hB hwI hwT _ hT (bRowI_length q M mus _)
    (zPrev_length q M mus nas ys _ (crowOf_length q L M mus nas gms ys) k) hnas
    (row4Fits_of hF k hk) hb2 (Na := rna) (St := [])
    (by simp [secV, Function.update_apply]) TermOK.nil
    (by simp [secV, Function.update_apply, hI.na]) (by simp [secV, Function.update_apply, hI.work])
    (by simp [secV, Function.update_apply, hI.work])
  refine WP.W9comp.runs_congr h ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [secV, Function.update_apply]
  · cases w <;> simp [secV, Function.update_apply, zPrev_step, zPrev_succ, secAll,
      List.reverse_append, rec1s_append]

theorem runs_secPass {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hM : 1 ≤ M)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (hnas : nas.length = M) (hF : SwFits q wI wT L M ys mus nas gms) :
    Runs (secPass G) (mk base (secV Vi q wI L M mus nas gms ys rdat 0))
      (mk base (secV Vi q wI L M mus nas gms ys rdat L)) (fun _ => True)
      (1 + loopCost (fun _ => r4Cost Ccm Crh Cca wI wT q M + 1) L) := by
  have htop : ∀ n, n ≤ L → optIsBit ((mk base (secV Vi q wI L M mus nas gms ys rdat (L - n)))
      (loc (.inr .bS2))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (secV Vi q wI L M mus nas gms ys rdat (L - n))) (loc (.inr .bS2)) =
        rec1s wI ((bAll q M mus ys L).drop ((L - n) * M)) ++ [] := by
      simp [secV, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ TermOK.nil, List.length_drop, bAll_length]
    exact decide_pos_sub0 L M n hM hn
  have hstep : ∀ n, n < L →
      Runs (r4 G) (mk base (secV Vi q wI L M mus nas gms ys rdat (L - (n + 1))))
        (mk base (secV Vi q wI L M mus nas gms ys rdat (L - n))) (fun _ => True)
        (r4Cost Ccm Crh Cca wI wT q M) := by
    intro n hn
    rw [show L - n = L - (n + 1) + 1 by omega]
    exact runs_r4_sec G scm srh sca hB hwI hwT hI hnas hF (L - (n + 1)) (by omega)
  have h := runs_whileP lS (.inr .bS2) (r4 G)
    (fun n => mk base (secV Vi q wI L M mus nas gms ys rdat (L - n))) L
    (fun _ => r4Cost Ccm Crh Cca wI wT q M) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- Final-erase state after `i` iterations (`zL` the last second-pass row, `A` the earlier rows). -/
def finV (Vi : SwD ⊕ SwW → List Sym) (wI : ℕ) (crow zL A : List CInt) (rdat : List Sym)
    (i : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update Vi
    (.inl .dat) rdat)
    (.inr .cS) (rec1s wI crow.reverse))
    (.inr .stI) (rec1s wI (zL.drop i)))
    (.inr .oS) (rec1s wI (zL.reverse.drop i ++ A.reverse))

theorem runs_fin_step {base : KS (LEs Ecm Erh Eca) → List Sym} {wI : ℕ}
    (Vi : SwD ⊕ SwW → List Sym) (crow zL A : List CInt) (rdat : List Sym) (i : ℕ)
    (hi : i < zL.length) :
    Runs (.seq (erP lS (.inr .stI)) (erP lS (.inr .oS)) : PS Ecm Erh Eca Rcm Rrh Rca)
      (mk base (finV Vi wI crow zL A rdat i)) (mk base (finV Vi wI crow zL A rdat (i + 1)))
      (fun _ => True) ((4 * wI + 2) + (4 * wI + 2)) := by
  have hzr : i < zL.reverse.length := by rw [List.length_reverse]; exact hi
  have h1 := runs_erP1 (LE := LEs Ecm Erh Eca) (σ := σs Rcm Rrh Rca) lS (.inr .stI) base
    (finV Vi wI crow zL A rdat i) (w := wI) (c := zL[i]) (r := rec1s wI (zL.drop (i + 1)))
    (by
      have e : (finV Vi wI crow zL A rdat i) (.inr .stI) = rec1s wI (zL.drop i) := by
        simp [finV, Function.update_apply]
      rw [e, rec1s_drop_cons wI zL i hi])
  have h2 := runs_erP1 (LE := LEs Ecm Erh Eca) (σ := σs Rcm Rrh Rca) lS (.inr .oS) base
    (Function.update (finV Vi wI crow zL A rdat i) (.inr .stI) (rec1s wI (zL.drop (i + 1))))
    (w := wI) (c := zL.reverse[i]) (r := rec1s wI (zL.reverse.drop (i + 1) ++ A.reverse))
    (by
      have e : (Function.update (finV Vi wI crow zL A rdat i) (.inr .stI)
          (rec1s wI (zL.drop (i + 1)))) (.inr .oS) =
          rec1s wI (zL.reverse.drop i) ++ rec1s wI A.reverse := by
        simp [finV, Function.update_apply, rec1s_append]
      rw [e, rec1s_drop_cons wI zL.reverse i hzr, rec1s_append, List.append_assoc])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [finV, Function.update_apply]
  · cases w <;> simp [finV, Function.update_apply]

theorem runs_finPass {base : KS (LEs Ecm Erh Eca) → List Sym} {wI : ℕ} (hwI : 1 ≤ wI)
    (Vi : SwD ⊕ SwW → List Sym) (hW : ∀ w, Vi (.inr w) = []) (crow zL A : List CInt)
    (rdat : List Sym) (M : ℕ) (hz : zL.length = M) :
    Runs (finPass : PS Ecm Erh Eca Rcm Rrh Rca) (mk base (finV Vi wI crow zL A rdat 0))
      (mk base (Function.update (Function.update Vi (.inl .dat) rdat) (.inl .dst)
        (rec1s wI (A ++ crow) ++ Vi (.inl .dst))))
      (fun _ => True) ((1 + loopCost (fun _ => (4 * wI + 2) + (4 * wI + 2) + 1) M) +
        ((crow.length * (12 * wI + 12) + 2) + (A.length * (12 * wI + 12) + 2))) := by
  have htop : ∀ n, n ≤ M → optIsBit ((mk base (finV Vi wI crow zL A rdat (M - n)))
      (loc (.inr .stI))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (finV Vi wI crow zL A rdat (M - n))) (loc (.inr .stI)) =
        rec1s wI (zL.drop (M - n)) ++ [] := by
      simp [finV, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ TermOK.nil, List.length_drop, hz, Nat.sub_sub_self hn]
  have hstep : ∀ n, n < M →
      Runs (.seq (erP lS (.inr .stI)) (erP lS (.inr .oS)) : PS Ecm Erh Eca Rcm Rrh Rca)
        (mk base (finV Vi wI crow zL A rdat (M - (n + 1))))
        (mk base (finV Vi wI crow zL A rdat (M - n))) (fun _ => True)
        ((4 * wI + 2) + (4 * wI + 2)) := by
    intro n hn
    rw [show M - n = M - (n + 1) + 1 by omega]
    exact runs_fin_step Vi crow zL A rdat (M - (n + 1)) (by omega)
  have hL := runs_whileP lS (.inr .stI)
    (.seq (erP lS (.inr .stI)) (erP lS (.inr .oS)) : PS Ecm Erh Eca Rcm Rrh Rca)
    (fun n => mk base (finV Vi wI crow zL A rdat (M - n))) M
    (fun _ => (4 * wI + 2) + (4 * wI + 2)) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at hL
  have hd : zL.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have hdr : zL.reverse.drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  unfold finPass
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hL
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .cS) (y := .inl .dst) (by decide) (by decide)
      (by decide) base _ hwI crow.reverse (rx := []) ?h1 TermOK.nil ?h2)
    (runs_drP1 lS (x := .inr .oS) (y := .inl .dst) (by decide) (by decide)
      (by decide) base _ hwI A.reverse (rx := []) ?h3 TermOK.nil ?h4))) ?he)
    (fun _ _ => trivial) ?hc
  case h1 => simp [finV, Function.update_apply]
  case h2 => simp [finV, Function.update_apply, hW]
  case h3 => simp [finV, Function.update_apply, hdr, hz]
  case h4 => simp [finV, Function.update_apply, hW]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [finV, Function.update_apply, rec1s_append]
    · cases w <;> simp [finV, Function.update_apply, hd, hdr, hW, hz]
  case hc => simp only [List.length_reverse, le_refl]

theorem secV_L_eq {q wI L M : ℕ} (hL : 1 ≤ L) {Vi : SwD ⊕ SwW → List Sym}
    (hW : ∀ w, Vi (.inr w) = []) {ys : List CInt} {mus nas gms : List ℤ} {rdat : List Sym} :
    secV Vi q wI L M mus nas gms ys rdat L =
      finV Vi wI (crowOf q L M mus nas gms ys)
        (secRows q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1))
        (secAll q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1)) rdat 0 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hd : (bAll q M mus ys (L' + 1)).drop ((L' + 1) * M) = [] :=
    List.drop_eq_nil_of_le (le_of_eq (bAll_length q M mus ys (L' + 1)))
  funext x
  rcases x with d | w
  · cases d <;> simp [secV, finV, Function.update_apply]
  · cases w <;> simp [secV, finV, Function.update_apply, hd, hW, zPrev_succ, secAll,
      List.reverse_append, rec1s_append]

/-- Cost of the sweep body. -/
def bodyCost (Ccm Crh Cca wI wT q L M : ℕ) : ℕ :=
  (r1Cost Ccm Crh wI wT q M + (1 + loopCost (fun _ => r2Cost Ccm Crh Cca wI wT q M + 1) (L - 1))) +
  ((r1Cost Ccm Crh wI wT q M + (L * M * (12 * wI + 12) + 2)) +
  ((1 + loopCost (fun _ => r4Cost Ccm Crh Cca wI wT q M + 1) L) +
  ((1 + loopCost (fun _ => (4 * wI + 2) + (4 * wI + 2) + 1) M) +
    ((M * (12 * wI + 12) + 2) + ((L - 1) * M * (12 * wI + 12) + 2)))))

/-- **The sweep body**: from the input state, `dat` is consumed and `sweepHalfI` is pushed on
`dst`; every other data/work stack is restored. -/
theorem runs_sweepBody {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT L M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hL : 1 ≤ L) (hM : 1 ≤ M)
    {Vi : SwD ⊕ SwW → List Sym} {ys : List CInt} {mus nas gms : List ℤ}
    {rdat rmu rna rgm : List Sym} (hI : SwIn Vi wI wT ys mus nas gms rdat rmu rna rgm)
    (trdat : TermOK rdat) (trmu : TermOK rmu)
    (hys : ys.length = L * M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hgms : gms.length = M) (hF : SwFits q wI wT L M ys mus nas gms) :
    Runs (sweepBody G) (mk base Vi)
      (mk base (Function.update (Function.update Vi (.inl .dat) rdat) (.inl .dst)
        (rec1s wI (sweepHalfI q L M mus nas gms ys) ++ Vi (.inl .dst))))
      (fun _ => True) (bodyCost Ccm Crh Cca wI wT q L M) := by
  have hP := runs_prePass G scm srh sca hB hwI hwT hL hM hI trdat trmu hys hmus hnas hF
  have hC := runs_clos G scm srh hB hwI hwT hL hI hys hgms hF
  have hS := runs_secPass G scm srh sca hB hwI hwT hM hI hnas hF
  rw [secV_L_eq hL hI.work] at hS
  have hFin := runs_finPass (Ecm := Ecm) (Erh := Erh) (Eca := Eca) (Rcm := Rcm) (Rrh := Rrh)
    (Rca := Rca) (base := base) hwI Vi hI.work (crowOf q L M mus nas gms ys)
    (secRows q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1))
    (secAll q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1)) rdat M
    (secRows_length q M mus nas ys _ (L - 1))
  have hout : secAll q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1) ++
      crowOf q L M mus nas gms ys = sweepHalfI q L M mus nas gms ys :=
    sweepOut_eq q L M hL hM mus nas gms ys
  rw [hout] at hFin
  unfold sweepBody
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq hP (WP.W9comp.runs_seq hC
    (WP.W9comp.runs_seq hS hFin))) (fun _ _ => trivial) (le_of_eq ?_)
  simp only [bodyCost, crowOf_length, secAll_length]

end Passes

end SubNLogN.Machine.Bridge.SolveAux
