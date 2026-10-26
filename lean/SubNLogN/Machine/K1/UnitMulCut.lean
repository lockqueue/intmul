/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulA

/-!
# K5-unit, the cut phase (`K1/UnitMulCut.lean`)

**Scope (honest summary).** Proved exact-stack specifications (no contract here):
* `loopM_cutPiece`: for each token on `Z_j`, one block moves from the top of the store onto
  `X_j` (restored to its order);
* `runsM_cutP`: pieces `k-1, …, 0` (`cutL`, consecutive pieces of the class counts);
* `runsM_phA2`: phase 2 of pass A on one fiber: after the cut, `X_j` holds the class-`j` blocks of
  the multiplied fiber (`mulA_cut`), the counters and the store are restored.
Construction: [OAI26, §2.1, proof of Lemma 4] ("reversing the roles of this split and merge").
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem rev_arrSyms_flatten : ∀ l : List (List (List Bool)),
    (arrSyms l.flatten).reverse = l.reverse.flatMap (fun b => (arrSyms b).reverse)
  | [] => rfl
  | b :: l => by
    rw [List.flatten_cons, arrSyms_append, List.reverse_append, rev_arrSyms_flatten l,
      List.reverse_cons, List.flatMap_append]
    simp

theorem vol_flatten_reverse (l : List (List (List Bool))) :
    vol l.reverse.flatten = vol l.flatten := by
  rw [vol_flatten, vol_flatten, List.map_reverse, List.sum_reverse]

theorem termOK_revArr (X : List (List Bool)) (R : List Sym) (hR : TermOK R) :
    TermOK ((arrSyms X).reverse ++ R) := by
  rw [arrSyms_reverse_eq]
  exact termOK_revRecs _ _ hR

section Cut

variable {n a d : ℕ}

theorem loopM_cutPiece (nm : Fin 4 → List Sym) (s : ℕ) (r3 : List Sym) (hr3 : TermOK r3)
    (hnm3 : nm 3 = natSyms s ++ r3) (j : ℕ) (hj : j < n) (Z0j Rn : List Sym) (hRn : TermOK Rn)
    (m : MU a d) :
    ∀ (rbs : List (List (List Bool))) (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym),
      (∀ b ∈ rbs, b.length = s) →
      zF j = List.replicate rbs.length tok ++ Sym.mark :: Z0j →
      sg 4 = rbs.flatMap (fun b => (arrSyms b).reverse) ++ Rn →
      LoopM (zst j) isTokS (.seq (popM (zst j)) (blkMvR NEG5 (xst j)) : PU n a d) m
        (mkF nm sg zF xF) m
        (mkF nm (Function.update sg 4 Rn) (Function.update zF j (Sym.mark :: Z0j))
          (Function.update xF j (arrSyms rbs.reverse.flatten ++ xF j)))
        (3 * vol rbs.flatten + rbs.length * (26 * s + 17) + 1)
  | [], sg, zF, xF, _, hz, hneg => by
    have e1 : Function.update sg 4 Rn = sg := by
      have : sg 4 = Rn := by rw [hneg]; rfl
      rw [← this, Function.update_eq_self]
    have e2 : Function.update zF j (Sym.mark :: Z0j) = zF := by
      have : zF j = Sym.mark :: Z0j := by rw [hz]; rfl
      rw [← this, Function.update_eq_self]
    have e3 : Function.update xF j
        (arrSyms ([] : List (List (List Bool))).reverse.flatten ++ xF j) = xF := by
      simp only [List.reverse_nil, List.flatten_nil, arrSyms_nil, List.nil_append,
        Function.update_eq_self]
    rw [e1, e2, e3]
    refine (LoopM.stop ?_).mono (by simp)
    rw [mkF_zst nm sg zF xF hj, hz]
    rfl
  | blk :: rbs, sg, zF, xF, hbs, hz, hneg => by
    have hb := hbs blk List.mem_cons_self
    have hc : testO isTokS ((mkF (n := n) nm sg zF xF) (zst j)).head? = true := by
      rw [mkF_zst nm sg zF xF hj, hz, List.length_cons, List.replicate_succ]
      rfl
    have h1 := RunsM.pop (M := MU a d) (zst j) tok
      (List.replicate rbs.length tok ++ Sym.mark :: Z0j) m (mkF (n := n) nm sg zF xF)
      (by rw [mkF_zst nm sg zF xF hj, hz, List.length_cons, List.replicate_succ, List.cons_append])
    rw [updF_zst nm sg zF xF hj] at h1
    have hR' := termOK_revBlocks rbs Rn hRn
    have h2 := runsM_cdMvRev (M := MU a d) (ns := SC5) (cnt := CNT5) (tmp := TMP5) (src := NEG5)
      (dst := xst j) (nm_ne_sg 3 2) (nm_ne_sg 3 3) (sg_ne_sg (by decide))
      (Ne.symm (xst_ne_sg hj 4)) (sg_ne_sg (by decide)) (xst_ne_sg hj 2) r3 hr3 blk.reverse (rbs.flatMap (fun b => (arrSyms b).reverse) ++ Rn) hR'
      m (mkF nm sg (Function.update zF j (List.replicate rbs.length tok ++ Sym.mark :: Z0j)) xF)
      (by rw [mkF_sg, hneg, List.flatMap_cons, List.append_assoc, arrSyms_reverse_eq])
      (by rw [mkF_nm, List.length_reverse, hb, hnm3])
    rw [mkF_xst _ _ _ _ hj, updF_sg, updF_xst _ _ _ _ hj, List.reverse_reverse] at h2
    have ih := loopM_cutPiece nm s r3 hr3 hnm3 j hj Z0j Rn hRn m rbs
      (Function.update sg 4 (rbs.flatMap (fun b => (arrSyms b).reverse) ++ Rn))
      (Function.update zF j (List.replicate rbs.length tok ++ Sym.mark :: Z0j))
      (Function.update xF j (arrSyms blk ++ xF j))
      (fun b h => hbs b (List.mem_cons_of_mem _ h)) (Function.update_self _ _ _)
      (Function.update_self _ _ _)
    refine ((LoopM.step hc (h1.seq h2) ih).congr ?_).mono ?_
    · rw [Function.update_idem, Function.update_idem, Function.update_idem, Function.update_self,
        List.reverse_cons, List.flatten_append, List.flatten_singleton, arrSyms_append,
        List.append_assoc]
    · have := incSeqCost_le 6 8 s
      have := bitLen_le_self s
      have e : (rbs.length + 1) * (26 * s + 17) = rbs.length * (26 * s + 17) + (26 * s + 17) := by
        ring
      rw [vol_reverse, List.flatten_cons, vol_append, List.length_reverse, hb, List.length_cons, e]
      omega

end Cut

section CutP

variable {n a d : ℕ}

theorem runsM_cutP (nm : Fin 4 → List Sym) (s : ℕ) (r3 : List Sym) (hr3 : TermOK r3)
    (hnm3 : nm 3 = natSyms s ++ r3) (Z0 X0 : ℕ → List Sym) (neg0 : List Sym)
    (fb : List (List (List Bool))) (hfb : ∀ b ∈ fb, b.length = s) (cnt : ℕ → ℕ) (m : MU a d) :
    ∀ k, k ≤ n → ((List.range k).map cnt).sum ≤ fb.length →
    ∀ (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym),
      sg 4 = (arrSyms (fb.take ((List.range k).map cnt).sum).flatten).reverse ++
        Sym.mark :: neg0 →
      (∀ j < k, zF j = List.replicate (cnt j) tok ++ Sym.mark :: Z0 j) →
      (∀ j < k, xF j = Sym.mark :: X0 j) →
      RunsM (forN cutPiece k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm (Function.update sg 4 (Sym.mark :: neg0))
          (fun j => if j < k then Sym.mark :: Z0 j else zF j)
          (fun j => if j < k then arrSyms (cutL cnt fb j).flatten ++ Sym.mark :: X0 j else xF j))
        (3 * vol (fb.take ((List.range k).map cnt).sum).flatten +
          ((List.range k).map cnt).sum * (26 * s + 17) + 2 * k + 1)
  | 0, _, _, sg, zF, xF, hneg, _, _ => by
    have e1 : Function.update sg 4 (Sym.mark :: neg0) = sg := by
      have : sg 4 = Sym.mark :: neg0 := by rw [hneg]; simp [arrSyms_nil]
      rw [← this, Function.update_eq_self]
    rw [e1]
    exact RunsM.of_eq (RunsM.skip m _) rfl rfl rfl
      (mkF_ext rfl rfl (fun j _ => by simp) (fun j _ => by simp)) (by simp)
  | k + 1, hk, hP, sg, zF, xF, hneg, hz, hx => by
    have hsum : ((List.range (k + 1)).map cnt).sum = ((List.range k).map cnt).sum + cnt k := by
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have hPk : ((List.range k).map cnt).sum ≤ fb.length := by omega
    have hpl : (cutL cnt fb k).length = cnt k := by
      rw [cutL, List.length_take, List.length_drop]; omega
    have hpb : ∀ b ∈ (cutL cnt fb k).reverse, b.length = s := by
      intro b hb
      rw [List.mem_reverse, cutL] at hb
      exact hfb b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    have hRn := termOK_revArr (fb.take ((List.range k).map cnt).sum).flatten (Sym.mark :: neg0)
      (TermOK.cons rfl _)
    have h1 := runsM_whileTop' (loopM_cutPiece (n := n) nm s r3 hr3 hnm3 k (by omega) (Z0 k)
      ((arrSyms (fb.take ((List.range k).map cnt).sum).flatten).reverse ++ Sym.mark :: neg0) hRn m
      (cutL cnt fb k).reverse sg zF xF hpb
      (by rw [hz k (by omega), List.length_reverse, hpl])
      (by rw [hneg, take_cutL, List.flatten_append, arrSyms_append, List.reverse_append,
            rev_arrSyms_flatten (cutL cnt fb k), List.append_assoc]))
    rw [hx k (by omega), List.reverse_reverse] at h1
    have ih := runsM_cutP nm s r3 hr3 hnm3 Z0 X0 neg0 fb hfb cnt m k (by omega) hPk
      (Function.update sg 4
        ((arrSyms (fb.take ((List.range k).map cnt).sum).flatten).reverse ++ Sym.mark :: neg0))
      (Function.update zF k (Sym.mark :: Z0 k))
      (Function.update xF k (arrSyms (cutL cnt fb k).flatten ++ Sym.mark :: X0 k))
      (Function.update_self _ _ _)
      (fun j hj => by rw [Function.update_of_ne (show j ≠ k by omega)]; exact hz j (by omega))
      (fun j hj => by rw [Function.update_of_ne (show j ≠ k by omega)]; exact hx j (by omega))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl ?_ ?_
    · rw [Function.update_idem]
      refine mkF_ext rfl rfl (fun j _ => ?_) (fun j _ => ?_)
      · by_cases hjk : j = k
        · subst hjk; simp
        · by_cases hj : j < k
          · simp [hj, show j < k + 1 by omega]
          · simp [hj, show ¬ j < k + 1 by omega, Function.update_of_ne hjk]
      · by_cases hjk : j = k
        · subst hjk; simp
        · by_cases hj : j < k
          · simp [hj, show j < k + 1 by omega]
          · simp [hj, show ¬ j < k + 1 by omega, Function.update_of_ne hjk]
    · rw [take_cutL, List.flatten_append, vol_append, vol_flatten_reverse, List.length_reverse,
        hpl, hsum, Nat.add_mul (((List.range k).map cnt).sum) (cnt k) (26 * s + 17)]
      omega

/-- **Phase 2 of pass A** on one fiber: cut the store into the class pieces (`X_j` receives the
class-`j` blocks of the multiplied fiber, `mulA_cut`), drop the counter and store marks. -/
theorem runsM_phA2 [NeZero a] (ha : a ≤ n) (Q : ℕ) (hcQ : Nat.Coprime Q a)
    (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym) (s : ℕ)
    (r3 : List Sym) (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3) (w : List (List Bool))
    (hw : Q * s ≤ w.length) (neg0 : List Sym) (m : MU a d)
    (hsg4 : sg 4 = (arrSyms (w.take (Q * s))).reverse ++ Sym.mark :: neg0) :
    RunsM (phA2 n a d) m
      (mkF nm sg
        (fun j => List.replicate (((List.range Q).map (jIdx a Q)).count j) tok ++ Sym.mark :: Z0 j)
        (fun j => Sym.mark :: X0 j)) m
      (mkF nm (Function.update sg 4 neg0) Z0
        (fun j => arrSyms (distI (jIdx a Q) (mulOut a Q ((List.range Q).map (blkOf s w))) j).flatten
          ++ Sym.mark :: X0 j))
      (3 * vol (w.take (Q * s)) + Q * (26 * s + 17) + 3 * n + 3) := by
  have hfbl : ((List.range Q).map (blkOf s w)).length = Q := by simp
  have hfb : ∀ b ∈ (List.range Q).map (blkOf s w), b.length = s := by
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    exact blkOf_length s w t (le_trans (Nat.mul_le_mul_right s (by omega)) hw)
  have hsumQ := sum_counts hcQ n ha
  have hflat : ((List.range Q).map (blkOf s w)).flatten = w.take (Q * s) := by
    rw [take_mul_flatMap w s Q, List.flatMap_def]
    rfl
  have h1 := runsM_cutP nm s r3 hr3 hnm3 Z0 X0 neg0 ((List.range Q).map (blkOf s w)) hfb
    (fun j => ((List.range Q).map (jIdx a Q)).count j) m n le_rfl (by rw [hsumQ, hfbl]) sg
    (fun j => List.replicate (((List.range Q).map (jIdx a Q)).count j) tok ++ Sym.mark :: Z0 j)
    (fun j => Sym.mark :: X0 j)
    (by rw [hsumQ, List.take_of_length_le (le_of_eq hfbl), hflat, hsg4])
    (fun j _ => rfl) (fun j _ => rfl)
  have h2 := runsM_popZ nm (Function.update sg 4 (Sym.mark :: neg0)) m
    (fun j => if j < n then arrSyms (cutL (fun j => ((List.range Q).map (jIdx a Q)).count j)
      ((List.range Q).map (blkOf s w)) j).flatten ++ Sym.mark :: X0 j else Sym.mark :: X0 j)
    Z0 n le_rfl
    (fun j => if j < n then Sym.mark :: Z0 j else
      List.replicate (((List.range Q).map (jIdx a Q)).count j) tok ++ Sym.mark :: Z0 j)
    (fun j hj => by simp [hj])
  have h3 := RunsM.pop (M := MU a d) NEG5 Sym.mark neg0 m
    (mkF (n := n) nm (Function.update sg 4 (Sym.mark :: neg0))
      (fun j => if j < n then Z0 j else if j < n then Sym.mark :: Z0 j else
        List.replicate (((List.range Q).map (jIdx a Q)).count j) tok ++ Sym.mark :: Z0 j)
      (fun j => if j < n then arrSyms (cutL (fun j => ((List.range Q).map (jIdx a Q)).count j)
        ((List.range Q).map (blkOf s w)) j).flatten ++ Sym.mark :: X0 j else Sym.mark :: X0 j))
    (by rw [mkF_sg, Function.update_self])
  rw [updF_sg, Function.update_idem] at h3
  refine RunsM.of_eq (h1.seq (h2.seq h3)) rfl rfl rfl ?_ ?_
  · refine mkF_ext rfl rfl (fun j hj => by simp [hj]) (fun j hj => ?_)
    simp only [hj, if_true]
    rw [mulA_cut hcQ _ hfbl]
  · rw [hsumQ, List.take_of_length_le (le_of_eq hfbl), hflat]
    omega

end CutP

end SubNLogN.Machine.K1.SMM
