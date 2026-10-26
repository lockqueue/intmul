/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarRowProg
import SubNLogN.Machine.CCore.LeafScalarRowVal

/-!
# Scalar row leaf: the static loops (`CCore/LeafScalarRowLoop.lean`)

**Scope (honest summary).** Exact safe runs of the loops of `CCore/LeafScalarRowProg.lean`, for
record arrays `encArr (P + Δ) addrs z` (`Contracts/Records.lean:77`) stored at width `w_g`:
* `safe_chain` (induction on the term list `τ`): the accumulator on `X` goes from `z0` to
  `z0 + Σ_{(c,s) ∈ τ} c · w s`, then moves onto role `u`;
* `safe_tgt`: one role `u` (move in, the chain);
* `safe_roles` (induction on a duplicate-free role list `L`), with the invariant that every source
  role (a role occurring in some term) still holds its input array; `safe_roles_all` for a list
  containing every role.
The halving of `c = ±1/2` is exact since the sources lie on a grid `G` with `G + 1 ≤ P + Δ`
(`LeafScalarRowVal.lean`). Lists are generic (never `List.finRange Wn` here). Everything is proved.
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Common
open SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Machine.CCore.LeafScalarRowVal

variable {Er : Type} [DecidableEq Er]

theorem len_carrSyms_encArr {α : Type} {r : ℕ} (w F : ℕ) (addrs : List α)
    (z : α → Fin r → ℂ) :
    (carrSyms w (encArr F addrs z)).length = addrs.length * (2 * w * r + 1) := by
  rw [length_carrSyms]
  simp only [encArr, List.map_map, Function.comp_def, List.length_map, List.length_finRange]
  induction addrs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem update_scP_X (t : CCoreRT) : Function.update (scP psS t) .X [Sym.mark] = scP psS t := by
  funext q
  by_cases h : q = .X
  · subst h; simp [scP]
  · simp [Function.update_apply, h]

/-- **The terms `τ` of role `u`**, then the move of `X` onto role `u` (role `u` holds only its
owned `mark` meanwhile; the sources of `τ` hold their input arrays). -/
theorem safe_chain {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (t : CCoreRT) {α : Type} {r : ℕ} (addrs : List α)
    (w : Fin Wn → α → Fin r → ℂ) {G : ℕ} (hG : G + 1 ≤ t.P + t.Δ)
    (hgrid : ∀ s x k, OnGrid G (w s x k))
    (hfit : ∀ s, CArrFits t.wg (encArr (t.P + t.Δ) addrs (w s))) (u : Fin Wn) :
    ∀ (τ : List (Coef × Fin Wn)) (z0 zf : α → Fin r → ℂ) (S0 : BL Er → List Sym),
      (∀ x k, OnGrid (t.P + t.Δ) (z0 x k)) →
      (∀ x k, zf x k = z0 x k + (τ.map fun p => p.1.val * w p.2 x k).sum) →
      KClean S0 → S0 (roleL u) = [Sym.mark] →
      (∀ p ∈ τ, S0 (roleL p.2) =
        carrSyms t.wg (encArr (t.P + t.Δ) addrs (w p.2)) ++ [Sym.mark]) →
      SafeRunsIn ccoreFramed [] (chainProg acc u τ)
        (stv S0 (Function.update (scP psS t) .X
          (carrSyms t.wg (encArr (t.P + t.Δ) addrs z0) ++ [Sym.mark])))
        (stv (Function.update S0 (roleL u)
          (carrSyms t.wg (encArr (t.P + t.Δ) addrs zf) ++ [Sym.mark])) (scP psS t))
        (fun _ => True)
        (τ.length * termCost t.wg (addrs.length * (2 * t.wg * r + 1)) Cacc +
          (8 * (addrs.length * (2 * t.wg * r + 1)) + 4))
  | [], z0, zf, S0, _, hzf, _, hu, _ => by
    have hz : zf = z0 := funext fun x => funext fun k => by rw [hzf x k]; simp
    rw [hz]
    have h := safe_mvOutX (Er := Er) Rr u S0
      (Function.update (scP psS t) .X
        (carrSyms t.wg (encArr (t.P + t.Δ) addrs z0) ++ [Sym.mark]))
      (carrSyms t.wg (encArr (t.P + t.Δ) addrs z0)) (mark_not_mem_arrSyms' _) hu
      (by simp [scP]) (by simp)
    refine SafeRunsIn.congr h ?_ ?_
    · rw [Function.update_idem, update_scP_X]
    · rw [len_carrSyms_encArr]; simp
  | (c, s) :: τ, z0, zf, S0, hz0, hzf, hcl, hu, hsrc => by
    have s1 := safe_term hacc t c s S0 hcl (encArr (t.P + t.Δ) addrs z0)
      (encArr (t.P + t.Δ) addrs (w s)) (cAligned_encArr _ _ _) (hfit s)
      (hsrc (c, s) List.mem_cons_self)
    rw [zipC_accC_encArr c addrs z0 (w s) hz0 (hgrid s) hG] at s1
    have ih := safe_chain hacc t addrs w hG hgrid hfit u τ
      (fun x k => z0 x k + c.val * w s x k) zf S0
      (fun x k => onGrid_acc c (hz0 x k) (hgrid s x k) hG)
      (fun x k => by simp only [hzf x k, List.map_cons, List.sum_cons]; ring)
      hcl hu (fun q hq => hsrc q (List.mem_cons_of_mem _ hq))
    refine SafeRunsIn.congr (SafeRunsIn.seq s1 ih) rfl ?_
    simp only [cvol, len_carrSyms_encArr, termCost, List.length_cons]
    apply le_of_eq
    ring

/-- **One role `u`** with terms `τ` (its sources are other roles holding their input arrays). -/
theorem safe_tgt {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (t : CCoreRT) {α : Type} {r : ℕ} (addrs : List α)
    (w : Fin Wn → α → Fin r → ℂ) {G : ℕ} (hG : G + 1 ≤ t.P + t.Δ)
    (hgrid : ∀ s x k, OnGrid G (w s x k))
    (hfit : ∀ s, CArrFits t.wg (encArr (t.P + t.Δ) addrs (w s))) (u : Fin Wn)
    (τ : List (Coef × Fin Wn)) (zf : α → Fin r → ℂ)
    (hzf : ∀ x k, zf x k = w u x k + (τ.map fun p => p.1.val * w p.2 x k).sum)
    (S0 : BL Er → List Sym) (hcl : KClean S0)
    (hu : S0 (roleL u) = carrSyms t.wg (encArr (t.P + t.Δ) addrs (w u)) ++ [Sym.mark])
    (hsrc : ∀ p ∈ τ, p.2 ≠ u ∧
      S0 (roleL p.2) = carrSyms t.wg (encArr (t.P + t.Δ) addrs (w p.2)) ++ [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (tgtProg acc u τ) (stv S0 (scP psS t))
      (stv (Function.update S0 (roleL u)
        (carrSyms t.wg (encArr (t.P + t.Δ) addrs zf) ++ [Sym.mark])) (scP psS t))
      (fun _ => True) (tgtCost t.wg (addrs.length * (2 * t.wg * r + 1)) Cacc τ.length) := by
  have s1 := safe_mvIn (Er := Er) Rr u S0 (scP psS t)
    (carrSyms t.wg (encArr (t.P + t.Δ) addrs (w u))) (mark_not_mem_arrSyms' _) hu
    (by simp [scP]) (by simp [scP])
  have hcl' : KClean (Function.update S0 (roleL u) [Sym.mark]) := fun e => by
    rw [Function.update_of_ne (by simp)]; exact hcl e
  have s2 := safe_chain hacc t addrs w hG hgrid hfit u τ (w u) zf
    (Function.update S0 (roleL u) [Sym.mark]) (fun x k => (hgrid u x k).mono (by omega)) hzf
    hcl' (by simp) (fun p hp => by
      rw [Function.update_of_ne (by simpa using (hsrc p hp).1)]; exact (hsrc p hp).2)
  rw [Function.update_idem] at s2
  refine SafeRunsIn.congr (SafeRunsIn.seq s1 s2) rfl ?_
  simp only [tgtCost, len_carrSyms_encArr]
  omega

/-- **The roles of a duplicate-free list `L`**, then `post`. Invariant: the roles of `L` and every
source role (a role occurring in some term) hold their input arrays; a source has no terms (V3), so
processing it does not change it. Role `u ∈ L` ends with `zf u`. -/
theorem safe_roles {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (t : CCoreRT) {α : Type} {r : ℕ} (addrs : List α)
    (w : Fin Wn → α → Fin r → ℂ) {G : ℕ} (hG : G + 1 ≤ t.P + t.Δ)
    (hgrid : ∀ s x k, OnGrid G (w s x k))
    (hfit : ∀ s, CArrFits t.wg (encArr (t.P + t.Δ) addrs (w s)))
    (T : Fin Wn → List (Coef × Fin Wn)) (hV3 : ∀ u c s, (c, s) ∈ T u → T s = [])
    (zf : Fin Wn → α → Fin r → ℂ)
    (hzf : ∀ u x k, zf u x k = w u x k + ((T u).map fun p => p.1.val * w p.2 x k).sum)
    (S : BL Er → List Sym) (hcl : KClean S) (post : Prog (BL Er) (fun _ => Sym) (σ Rr))
    (Tp : ℕ)
    (hpost : ∀ g, SafeRunsIn ccoreFramed [] post (stv (setRoles S g) (scP psS t))
      (setRoles S g) (fun _ => True) Tp) :
    ∀ (L : List (Fin Wn)) (g : Fin Wn → List Sym), L.Nodup →
      (∀ u ∈ L, g u = carrSyms t.wg (encArr (t.P + t.Δ) addrs (w u)) ++ [Sym.mark]) →
      (∀ u c s, (c, s) ∈ T u →
        g s = carrSyms t.wg (encArr (t.P + t.Δ) addrs (w s)) ++ [Sym.mark]) →
      SafeRunsIn ccoreFramed [] (rolesProg acc T post L) (stv (setRoles S g) (scP psS t))
        (setRoles S (fun u => if u ∈ L then
          carrSyms t.wg (encArr (t.P + t.Δ) addrs (zf u)) ++ [Sym.mark] else g u))
        (fun _ => True)
        ((L.map fun u => tgtCost t.wg (addrs.length * (2 * t.wg * r + 1)) Cacc
          (T u).length).sum + Tp)
  | [], g, _, _, _ => by
    refine SafeRunsIn.congr (hpost g) ?_ (by simp)
    exact congrArg (setRoles S) (funext fun u => by simp)
  | u :: L, g, hnd, hg, hgs => by
    have hu : u ∉ L := (List.nodup_cons.mp hnd).1
    have hnil : ∀ v, T v = [] → zf v = w v := fun v hv =>
      funext fun x => funext fun k => by rw [hzf v x k, hv]; simp
    have s1 := safe_tgt hacc t addrs w hG hgrid hfit u (T u) (zf u) (hzf u) (setRoles S g)
      (kClean_setRoles S hcl g) (hg u List.mem_cons_self)
      (fun p hp => ⟨fun h => by
          have h1 := hV3 u p.1 p.2 hp
          rw [h] at h1
          simp [h1] at hp,
        hgs u p.1 p.2 hp⟩)
    rw [update_setRoles] at s1
    have ih := safe_roles hacc t addrs w hG hgrid hfit T hV3 zf hzf S hcl post Tp hpost L
      (Function.update g u (carrSyms t.wg (encArr (t.P + t.Δ) addrs (zf u)) ++ [Sym.mark]))
      (List.nodup_cons.mp hnd).2
      (fun v hv => by
        rw [Function.update_of_ne (fun h : v = u => hu (h ▸ hv))]
        exact hg v (List.mem_cons_of_mem _ hv))
      (fun v c s hs => by
        by_cases h : s = u
        · have hTs : T s = [] := hV3 v c s hs
          rw [h] at hTs ⊢
          rw [Function.update_self, hnil u hTs]
        · rw [Function.update_of_ne h]
          exact hgs v c s hs)
    refine SafeRunsIn.congr (SafeRunsIn.seq s1 ih) ?_
      (by simp only [List.map_cons, List.sum_cons]; omega)
    congr 1
    funext v
    by_cases h : v = u
    · rw [h]; simp [hu]
    · simp [h, Function.update_of_ne h]

/-- `safe_roles` for a duplicate-free list containing every role, started from the input arrays
(`hS`): every role `u` ends with `fin u`, any list of symbols equal to the encoding of `zf u`
followed by the owned `mark` (`hfin`). -/
theorem safe_roles_all {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (t : CCoreRT) {α : Type} {r : ℕ} (addrs : List α)
    (w : Fin Wn → α → Fin r → ℂ) {G : ℕ} (hG : G + 1 ≤ t.P + t.Δ)
    (hgrid : ∀ s x k, OnGrid G (w s x k))
    (hfit : ∀ s, CArrFits t.wg (encArr (t.P + t.Δ) addrs (w s)))
    (T : Fin Wn → List (Coef × Fin Wn)) (hV3 : ∀ u c s, (c, s) ∈ T u → T s = [])
    (zf : Fin Wn → α → Fin r → ℂ)
    (hzf : ∀ u x k, zf u x k = w u x k + ((T u).map fun p => p.1.val * w p.2 x k).sum)
    (S : BL Er → List Sym) (hcl : KClean S)
    (hS : ∀ u, S (roleL u) = carrSyms t.wg (encArr (t.P + t.Δ) addrs (w u)) ++ [Sym.mark])
    (post : Prog (BL Er) (fun _ => Sym) (σ Rr)) (Tp : ℕ)
    (hpost : ∀ g, SafeRunsIn ccoreFramed [] post (stv (setRoles S g) (scP psS t))
      (setRoles S g) (fun _ => True) Tp)
    (L : List (Fin Wn)) (hnd : L.Nodup) (hall : ∀ u, u ∈ L) (fin : Fin Wn → List Sym)
    (hfin : ∀ u, fin u = carrSyms t.wg (encArr (t.P + t.Δ) addrs (zf u)) ++ [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (rolesProg acc T post L) (stv S (scP psS t)) (setRoles S fin)
      (fun _ => True)
      ((L.map fun u => tgtCost t.wg (addrs.length * (2 * t.wg * r + 1)) Cacc
        (T u).length).sum + Tp) := by
  have h := safe_roles hacc t addrs w hG hgrid hfit T hV3 zf hzf S hcl post Tp hpost L
    (fun u => S (roleL u)) hnd (fun u _ => hS u) (fun _ _ s _ => hS s)
  rw [setRoles_self S (fun u => S (roleL u)) (fun _ => rfl)] at h
  refine SafeRunsIn.congr h ?_ le_rfl
  exact congrArg (setRoles S) (funext fun u => by simp [hall u, hfin u])

end SubNLogN.Machine.CCore.LeafScalarRowAux
