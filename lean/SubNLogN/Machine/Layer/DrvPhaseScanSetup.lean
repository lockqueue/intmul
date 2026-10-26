/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseScanRec

/-!
# Layer driver phase scan: header copy, set-up, clean-up (`Machine/Layer/DrvPhaseScanSetup.lean`)

**Scope (honest summary).** `hdrCopy ps` copies the fields of the header
`hdrSyms fs` (stack `1`, restored through the stash `Hs`) onto the stacks `ps`, each above a
guard (`runs_hdrCopy`); `dropAll ps` removes them again (`runs_dropAll`). No `sorry`.
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-- The stacks after copying the fields `fs` onto the stacks `ps` (each above a guard). -/
def updF (S : PL → List Sym) : List PL → List ℕ → PL → List Sym
  | p :: ps, f :: fs => updF (Function.update S p (natSyms f ++ .mark :: S p)) ps fs
  | _, _ => S

theorem updF_apply_not_mem : ∀ (ps : List PL) (fs : List ℕ) (S : PL → List Sym) (k : PL),
    k ∉ ps → updF S ps fs k = S k
  | [], _, _, _, _ => by simp [updF]
  | _ :: _, [], _, _, _ => by simp [updF]
  | p :: ps, f :: fs, S, k, hk => by
    simp only [updF]
    rw [updF_apply_not_mem ps fs _ k (fun h => hk (List.mem_cons_of_mem _ h)),
      Function.update_of_ne (by rintro rfl; exact hk List.mem_cons_self)]

theorem updF_upd_comm : ∀ (ps : List PL) (fs : List ℕ) (S : PL → List Sym) (k : PL)
    (x : List Sym), k ∉ ps → updF (Function.update S k x) ps fs =
      Function.update (updF S ps fs) k x
  | [], _, _, _, _, _ => by simp [updF]
  | _ :: _, [], _, _, _, _ => by simp [updF]
  | p :: ps, f :: fs, S, k, x, hk => by
    simp only [updF]
    have hpk : p ≠ k := by rintro rfl; exact hk List.mem_cons_self
    rw [Function.update_of_ne hpk,
      Function.update_comm hpk.symm x (natSyms f ++ Sym.mark :: S p) S]
    exact updF_upd_comm ps fs _ k x (fun h => hk (List.mem_cons_of_mem _ h))

/-! ## Copying the header -/

/-- Copy the fields of the header onto the stacks `ps` (each above a new guard), stashing the
fields on `Hs` and restoring them. -/
def hdrCopy : List PL → Prog PL (fun _ => Sym) PReg
  | [] => skip
  | p :: ps => .seq (wk (pushC p .mark)) (.seq (wk (copyBlock sH p kTm))
      (.seq (wk (moveBlock sH kHs)) (.seq (wk (moveOne sH kHs)) (.seq (hdrCopy ps)
        (.seq (wk (moveOne kHs sH)) (wk (moveBlock kHs sH)))))))

theorem closed_hdrCopy : ∀ ps : List PL, (hdrCopy ps).Closed
  | [] => by simp [hdrCopy, skip, Prog.Closed, Prog.FreeBelow]
  | p :: ps => ⟨K1.Rot.closed_pushC_lift _ _ _, K1.Rot.closed_copyBlock_lift _ _ _ _,
      closed_moveBlock_lift _ _, closed_moveOne _ _, closed_hdrCopy ps, closed_moveOne _ _,
      closed_moveBlock_lift _ _⟩

/-- Cost of the header copy. -/
def hdrCost (fs : List ℕ) : ℕ := (fs.map fun f => 13 * bitLen f + 20).sum + 1

theorem runs_hdrCopy : ∀ (ps : List PL) (fs : List ℕ) (S : PL → List Sym) (rp : List Sym),
    ps.length = fs.length → (∀ p ∈ ps, p ≠ sH ∧ p ≠ kHs ∧ p ≠ kTm) →
    S sH = hdrSyms fs ++ rp → TermOK (S kHs) →
    Runs (hdrCopy ps) S (updF S ps fs) (fun _ => True) (hdrCost fs)
  | [], [], S, rp, _, _, _, _ => by simpa [hdrCopy, updF, hdrCost] using runs_skip S
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | p :: ps, f :: fs, S, rp, hl, hps, hH, hHs => by
    obtain ⟨hp1, hp2, hp3⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ ps, q ≠ sH ∧ q ≠ kHs ∧ q ≠ kTm :=
      fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hsH : sH ∉ ps := fun h => (hps' sH h).1 rfl
    have hHs' : kHs ∉ ps := fun h => (hps' kHs h).2.1 rfl
    have hH' : S sH = (encodeNat f).map Sym.bit ++ (Sym.mark :: (hdrSyms fs ++ rp)) := by
      rw [hH]; simp [hdrSyms, natSyms]
    set L := (encodeNat f).length with hL
    have r0 := K1.runs_wk_pushC pl p .mark S
    set S0 := Function.update S p (.mark :: S p) with hS0
    have r1 := runs_copyBlock (src := sH) (dst := p) (t := kTm) (Ne.symm hp1) (by simp) hp3
      (encodeNat f) (.mark :: (hdrSyms fs ++ rp)) S0 (termOK_mark _)
      (by rw [hS0, Function.update_of_ne (Ne.symm hp1)]; exact hH')
    set S1 := Function.update S p (natSyms f ++ .mark :: S p) with hS1
    have hS01 : Function.update S0 p ((encodeNat f).map Sym.bit ++ S0 p) = S1 := by
      simp [hS0, hS1, natSyms]
    rw [hS01] at r1
    have r2 := runs_moveBlock (src := sH) (dst := kHs) (by simp) (encodeNat f)
      (.mark :: (hdrSyms fs ++ rp)) S1 (termOK_mark _)
      (by rw [hS1, Function.update_of_ne (Ne.symm hp1)]; exact hH')
    have hS1H : S1 kHs = S kHs := by rw [hS1, Function.update_of_ne (Ne.symm hp2)]
    rw [hS1H] at r2
    set S2 := Function.update (Function.update S1 sH (.mark :: (hdrSyms fs ++ rp))) kHs
      ((encodeNat f).reverse.map Sym.bit ++ S kHs) with hS2
    have r3 := runs_moveOne (src := sH) (dst := kHs) (by simp) S2 .mark (hdrSyms fs ++ rp)
      (by simp [hS2])
    have hS2H : S2 kHs = (encodeNat f).reverse.map Sym.bit ++ S kHs := by simp [hS2]
    rw [hS2H] at r3
    set S3 := Function.update (Function.update S2 sH (hdrSyms fs ++ rp)) kHs
      (.mark :: ((encodeNat f).reverse.map Sym.bit ++ S kHs)) with hS3
    have r4 := runs_hdrCopy ps fs S3 rp (by simpa using hl) hps' (by simp [hS3])
      (by simp only [hS3, Function.update_self]; exact termOK_mark _)
    have h4H : updF S3 ps fs kHs = .mark :: ((encodeNat f).reverse.map Sym.bit ++ S kHs) := by
      rw [updF_apply_not_mem ps fs S3 kHs hHs']; simp [hS3]
    have h4s : updF S3 ps fs sH = hdrSyms fs ++ rp := by
      rw [updF_apply_not_mem ps fs S3 sH hsH]; simp [hS3]
    have r5 := runs_moveOne (src := kHs) (dst := sH) (by simp) (updF S3 ps fs) .mark
      ((encodeNat f).reverse.map Sym.bit ++ S kHs) h4H
    rw [h4s] at r5
    have r6 := runs_moveBlock (src := kHs) (dst := sH) (by simp) (encodeNat f).reverse (S kHs)
      (Function.update (Function.update (updF S3 ps fs) kHs
        ((encodeNat f).reverse.map Sym.bit ++ S kHs)) sH (.mark :: (hdrSyms fs ++ rp))) hHs
      (by simp)
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r0
      (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
      (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 r6)))))) ?_) (fun _ h => h) ?_
    · have hA_sH : updF S1 ps fs sH = S sH := by
        rw [updF_apply_not_mem ps fs S1 sH hsH, hS1, Function.update_of_ne (Ne.symm hp1)]
      have hA_Hs : updF S1 ps fs kHs = S kHs := by
        rw [updF_apply_not_mem ps fs S1 kHs hHs', hS1, Function.update_of_ne (Ne.symm hp2)]
      simp only [hS3, hS2, updF_upd_comm ps fs _ _ _ hsH, updF_upd_comm ps fs _ _ _ hHs']
      show _ = updF S1 ps fs
      funext k
      by_cases h1 : k = sH
      · subst h1
        simp only [Function.update_apply, if_true, if_neg (show (sH : PL) ≠ kHs by simp)]
        rw [hA_sH, List.reverse_reverse, hH']
      · by_cases h2 : k = kHs
        · subst h2
          simp only [Function.update_apply, if_true, if_neg (show (kHs : PL) ≠ sH by simp)]
          rw [hA_Hs]
        · simp only [Function.update_apply, if_neg h1, if_neg h2]
    · simp only [hdrCost, List.map_cons, List.sum_cons, List.length_reverse]
      rw [← hL]
      have : L = bitLen f := rfl
      omega

/-! ## Dropping the parameter counters -/

/-- Drop the counters on the stacks `ps` (with their guards). -/
def dropAll : List PL → Prog PL (fun _ => Sym) PReg
  | [] => skip
  | p :: ps => .seq (wk (K1.dropBits p)) (dropAll ps)

theorem closed_dropAll : ∀ ps : List PL, (dropAll ps).Closed
  | [] => by simp [dropAll, skip, Prog.Closed, Prog.FreeBelow]
  | p :: ps => ⟨K1.Rot.closed_dropBits_lift _ _, closed_dropAll ps⟩

/-- Cost of `dropAll`. -/
def dropCost (fs : List ℕ) : ℕ := (fs.map fun f => 2 * bitLen f + 2).sum + 1

theorem runs_dropAll : ∀ (ps : List PL) (fs : List ℕ) (X : PL → List Sym),
    ps.length = fs.length → ps.Nodup →
    Runs (dropAll ps) (updF X ps fs) X (fun _ => True) (dropCost fs)
  | [], [], X, _, _ => by simpa [dropAll, updF, dropCost] using runs_skip X
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | p :: ps, f :: fs, X, hl, hnd => by
    have hp : p ∉ ps := (List.nodup_cons.1 hnd).1
    have hnd' := (List.nodup_cons.1 hnd).2
    have h1 := K1.runs_wk_dropBits pl p (encodeNat f) .mark (X p)
      (updF X (p :: ps) (f :: fs)) rfl
      (by simp only [updF]; rw [updF_apply_not_mem ps fs _ p hp]; simp [natSyms])
    have h2 := runs_dropAll ps fs X (by simpa using hl) hnd'
    have he : Function.update (updF X (p :: ps) (f :: fs)) p (X p) = updF X ps fs := by
      simp only [updF]
      rw [← updF_upd_comm ps fs _ p _ hp, Function.update_idem, Function.update_eq_self]
    rw [he] at h1
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ h => h) ?_
    simp only [dropCost, List.map_cons, List.sum_cons]
    have : (encodeNat f).length = bitLen f := rfl
    omega

end SubNLogN.Machine.Layer.DrvPhaseScanAux
