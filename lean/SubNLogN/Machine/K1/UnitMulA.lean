/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulProg
import SubNLogN.Machine.K1.UnitNegFiber

/-!
# K5-unit, marks and the count phase (`K1/UnitMulA.lean`)

**Scope (honest summary).** Proved exact-stack specifications (no contract here):
* `runsM_pushZ`, `runsM_pushX`, `runsM_popZ`, `runsM_popX`: marks on the first `k` counters or
  streams;
* `runsM_actA1`: one count step of pass A (block `u` to the store, a token on `Z_{jIdx a Q u}`);
* `runsM_phA1`: phase 1 of pass A on one fiber (all `Q = q^b` count steps, by `recProg`).
Construction: [OAI26, §2.1, proof of Lemma 4] (the class of `u` is the residue `jIdx a Q u`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

section Ne

variable {n : ℕ}

theorem sg_ne_sg {i j : Fin 9} (h : i ≠ j) : (SG5 i : L5 n n) ≠ SG5 j := by
  intro e; apply h; simpa using e

theorem nm_ne_nm {i j : Fin 4} (h : i ≠ j) : (.inl i : L5 n n) ≠ .inl j := by
  intro e; apply h; simpa using e

theorem nm_ne_sg (i : Fin 4) (j : Fin 9) : (.inl i : L5 n n) ≠ SG5 j := by
  intro e; cases e

end Ne

section PushPop

variable {n a d : ℕ}

theorem runsM_pushZ (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (m : MU a d)
    (xF : ℕ → List Sym) : ∀ k, k ≤ n → ∀ zF : ℕ → List Sym,
      RunsM (forN (fun j => pushM (zst j)) k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm sg (fun j => if j < k then Sym.mark :: zF j else zF j) xF) (k + 1)
  | 0, _, zF => RunsM.of_eq (RunsM.skip m _) rfl rfl rfl
      (mkF_ext rfl rfl (fun j _ => by simp) (fun _ _ => rfl)) le_rfl
  | k + 1, hk, zF => by
    have h1 := RunsM.push (M := MU a d) (zst k) Sym.mark m (mkF (n := n) nm sg zF xF)
    rw [mkF_zst nm sg zF xF (by omega), updF_zst nm sg zF xF (by omega)] at h1
    have ih := runsM_pushZ nm sg m xF k (by omega) (Function.update zF k (Sym.mark :: zF k))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl
      (mkF_ext rfl rfl (fun j _ => ?_) (fun _ _ => rfl)) (by omega)
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [Function.update_of_ne hjk]
      by_cases hj : j < k
      · simp [hj, show j < k + 1 by omega]
      · simp [hj, show ¬ j < k + 1 by omega]

theorem runsM_pushX (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (m : MU a d)
    (zF : ℕ → List Sym) : ∀ k, k ≤ n → ∀ xF : ℕ → List Sym,
      RunsM (forN (fun j => pushM (xst j)) k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm sg zF (fun j => if j < k then Sym.mark :: xF j else xF j)) (k + 1)
  | 0, _, xF => RunsM.of_eq (RunsM.skip m _) rfl rfl rfl
      (mkF_ext rfl rfl (fun _ _ => rfl) (fun j _ => by simp)) le_rfl
  | k + 1, hk, xF => by
    have h1 := RunsM.push (M := MU a d) (xst k) Sym.mark m (mkF (n := n) nm sg zF xF)
    rw [mkF_xst nm sg zF xF (by omega), updF_xst nm sg zF xF (by omega)] at h1
    have ih := runsM_pushX nm sg m zF k (by omega) (Function.update xF k (Sym.mark :: xF k))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl
      (mkF_ext rfl rfl (fun _ _ => rfl) (fun j _ => ?_)) (by omega)
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [Function.update_of_ne hjk]
      by_cases hj : j < k
      · simp [hj, show j < k + 1 by omega]
      · simp [hj, show ¬ j < k + 1 by omega]

theorem runsM_popZ (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (m : MU a d)
    (xF Z0 : ℕ → List Sym) : ∀ k, k ≤ n → ∀ zF : ℕ → List Sym,
      (∀ j < k, zF j = Sym.mark :: Z0 j) →
      RunsM (forN (fun j => popM (zst j)) k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm sg (fun j => if j < k then Z0 j else zF j) xF) (k + 1)
  | 0, _, zF, _ => RunsM.of_eq (RunsM.skip m _) rfl rfl rfl
      (mkF_ext rfl rfl (fun j _ => by simp) (fun _ _ => rfl)) le_rfl
  | k + 1, hk, zF, hz => by
    have h1 := RunsM.pop (M := MU a d) (zst k) Sym.mark (Z0 k) m (mkF (n := n) nm sg zF xF)
      (by rw [mkF_zst nm sg zF xF (by omega)]; exact hz k (by omega))
    rw [updF_zst nm sg zF xF (by omega)] at h1
    have ih := runsM_popZ nm sg m xF Z0 k (by omega) (Function.update zF k (Z0 k))
      (fun j hj => by rw [Function.update_of_ne (by omega)]; exact hz j (by omega))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl
      (mkF_ext rfl rfl (fun j _ => ?_) (fun _ _ => rfl)) (by omega)
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [Function.update_of_ne hjk]
      by_cases hj : j < k
      · simp [hj, show j < k + 1 by omega]
      · simp [hj, show ¬ j < k + 1 by omega]

theorem runsM_popX (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (m : MU a d)
    (zF X0 : ℕ → List Sym) : ∀ k, k ≤ n → ∀ xF : ℕ → List Sym,
      (∀ j < k, xF j = Sym.mark :: X0 j) →
      RunsM (forN (fun j => popM (xst j)) k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm sg zF (fun j => if j < k then X0 j else xF j)) (k + 1)
  | 0, _, xF, _ => RunsM.of_eq (RunsM.skip m _) rfl rfl rfl
      (mkF_ext rfl rfl (fun _ _ => rfl) (fun j _ => by simp)) le_rfl
  | k + 1, hk, xF, hx => by
    have h1 := RunsM.pop (M := MU a d) (xst k) Sym.mark (X0 k) m (mkF (n := n) nm sg zF xF)
      (by rw [mkF_xst nm sg zF xF (by omega)]; exact hx k (by omega))
    rw [updF_xst nm sg zF xF (by omega)] at h1
    have ih := runsM_popX nm sg m zF X0 k (by omega) (Function.update xF k (X0 k))
      (fun j hj => by rw [Function.update_of_ne (by omega)]; exact hx j (by omega))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl
      (mkF_ext rfl rfl (fun _ _ => rfl) (fun j _ => ?_)) (by omega)
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [Function.update_of_ne hjk]
      by_cases hj : j < k
      · simp [hj, show j < k + 1 by omega]
      · simp [hj, show ¬ j < k + 1 by omega]

end PushPop

/-! ## The count phase -/

theorem count_range_succ (pA : ℕ → ℕ) (k j : ℕ) :
    ((List.range (k + 1)).map pA).count j =
      ((List.range k).map pA).count j + if pA k = j then 1 else 0 := by
  rw [List.range_succ, List.map_append, List.count_append, List.map_singleton,
    List.count_singleton]
  by_cases h : pA k = j <;> simp [h]

theorem zF_step (pA : ℕ → ℕ) (Z0 : ℕ → List Sym) (k : ℕ) :
    Function.update
      (fun j => List.replicate (((List.range k).map pA).count j) tok ++ Sym.mark :: Z0 j) (pA k)
      (tok :: (List.replicate (((List.range k).map pA).count (pA k)) tok ++ Sym.mark :: Z0 (pA k))) =
    fun j => List.replicate (((List.range (k + 1)).map pA).count j) tok ++ Sym.mark :: Z0 j := by
  funext j
  rw [count_range_succ]
  by_cases h : j = pA k
  · subst h
    rw [Function.update_self, if_pos rfl, List.replicate_succ, List.cons_append]
  · rw [Function.update_of_ne h, if_neg (Ne.symm h), Nat.add_zero]

/-- Count-phase state after `k` blocks (`pA` the class pattern). -/
def stC {n : ℕ} (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym)
    (pA : ℕ → ℕ) (s : ℕ) (w : List (List Bool)) (R neg0 : List Sym) (k : ℕ) :
    L5 n n → List Sym :=
  mkF (Function.update nm 0 (arrSyms (w.drop (k * s)) ++ R))
    (Function.update sg 4 ((arrSyms (w.take (k * s))).reverse ++ Sym.mark :: neg0))
    (fun j => List.replicate (((List.range k).map pA).count j) tok ++ Sym.mark :: Z0 j)
    (fun j => Sym.mark :: X0 j)

/-- Cost bound of one count step. -/
def actA1Cost (n s : ℕ) (blk : List (List Bool)) : ℕ := 3 * vol blk + 23 * s + n + 14

section Count

variable {n a d : ℕ}

theorem runsM_actA1 [NeZero a] (ha : a ≤ n) (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym)
    (Z0 X0 : ℕ → List Sym) (Q s : ℕ) (w : List (List Bool)) (R neg0 r3 : List Sym)
    (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3) (k : ℕ) (hk : (k + 1) * s ≤ w.length) :
    RunsM (actA1 n a d) (regU a d Q k 0) (stC (n := n) nm sg Z0 X0 (jIdx a Q) s w R neg0 k)
      (regU a d Q (k + 1) 0) (stC nm sg Z0 X0 (jIdx a Q) s w R neg0 (k + 1))
      (actA1Cost n s ((w.drop (k * s)).take s)) := by
  have hw' : s ≤ (w.drop (k * s)).length := by
    rw [List.length_drop]; rw [Nat.succ_mul] at hk; omega
  have hjn : jIdx a Q k < n := lt_of_lt_of_le (jIdx_lt k) ha
  have h1 := runsM_cdMvRec (M := MU a d) (ns := SC5) (cnt := CNT5) (tmp := TMP5) (src := SRC5)
    (dst := NEG5) (nm_ne_sg 3 2) (nm_ne_sg 3 3) (sg_ne_sg (by decide)) (nm_ne_sg 0 4)
    (nm_ne_sg 0 2) (sg_ne_sg (by decide)) (nm_ne_nm (by decide)) (nm_ne_sg 3 4) s r3 hr3
    (w.drop (k * s)) R hw' (regU a d Q k 0)
    (stC (n := n) nm sg Z0 X0 (jIdx a Q) s w R neg0 k)
    (by simp only [stC, mkF_nm, Function.update_self])
    (by simp only [stC, mkF_nm]; rw [Function.update_of_ne (by decide)]; exact hnm3)
  simp only [stC] at h1
  rw [mkF_sg, updF_nm, updF_sg] at h1
  refine RunsM.of_eq (h1.seq ((runsM_dispatch (sel := jA)
    (ps := fun j => (lift (Lib.pushC (zst j) tok) : PU n a d)) (fun o => jA_regU Q k 0 o) hjn
    (RunsM.push (M := MU a d) (zst (jIdx a Q k)) tok (regU a d Q k 0) _)).seq
    (RunsM.load (K := L5 n n) (incAf (a := a) (d := d)) (regU a d Q k 0) _))) rfl rfl
    (incAf_regU Q k 0) ?_ ?_
  · rw [mkF_zst _ _ _ _ hjn, updF_zst _ _ _ _ hjn]
    simp only [stC]
    refine mkF_ext ?_ ?_ (fun j _ => ?_) (fun _ _ => rfl)
    · rw [Function.update_idem, List.drop_drop, Nat.succ_mul]
    · rw [Function.update_idem, Function.update_self, Nat.succ_mul, List.take_add, arrSyms_append,
        List.reverse_append, List.append_assoc]
    · exact congrFun (zF_step (jIdx a Q) Z0 k) j
  · unfold actA1Cost
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

/-- **Phase 1 of pass A** on one fiber: marks, then the `Q = q^b` count steps. -/
theorem runsM_phA1 [NeZero a] (ha : a ≤ n) (q : ℕ) (hq : 2 ≤ q) (b : ℕ)
    (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym) (s : ℕ)
    (w : List (List Bool)) (R r3 D : List Sym) (hD : D.head? ≠ some tok) (hr3 : TermOK r3)
    (hw : q ^ b * s ≤ w.length) (hnm0 : nm 0 = arrSyms w ++ R) (hnm3 : nm 3 = natSyms s ++ r3)
    (hsg1 : sg 1 = List.replicate b tok ++ D) (u t : ℕ) :
    RunsM (phA1 q n a d) (regU a d (q ^ b) u t) (mkF nm sg zF xF) (regU a d (q ^ b) (q ^ b) 0)
      (mkF (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
        (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++ Sym.mark :: sg 4))
        (fun j => List.replicate (((List.range (q ^ b)).map (jIdx a (q ^ b))).count j) tok ++
          Sym.mark :: zF j)
        (fun j => Sym.mark :: xF j))
      (3 * vol (w.take (q ^ b * s)) + q ^ b * (23 * s + n + 25) + 2 * n + 4) := by
  have h0 := RunsM.load (K := L5 n n) (rstf (a := a) (d := d)) (regU a d (q ^ b) u t)
    (mkF (n := n) nm sg zF xF)
  rw [rstf_regU] at h0
  have h1 := RunsM.push (M := MU a d) NEG5 Sym.mark (regU a d (q ^ b) 0 0) (mkF (n := n) nm sg zF xF)
  rw [mkF_sg, updF_sg] at h1
  have h2 := runsM_pushZ nm (Function.update sg 4 (Sym.mark :: sg 4)) (regU a d (q ^ b) 0 0) xF n
    le_rfl zF
  have h3 := runsM_pushX nm (Function.update sg 4 (Sym.mark :: sg 4)) (regU a d (q ^ b) 0 0)
    (fun j => if j < n then Sym.mark :: zF j else zF j) n le_rfl xF
  have hrec := runsM_recProg q DEP5 (actA1 n a d) closed_actA1 D hD (q ^ b)
    (fun k => regU a d (q ^ b) k 0)
    (stC (n := n) nm (Function.update sg 1 D) zF xF (jIdx a (q ^ b)) s w R (sg 4))
    (fun k => actA1Cost n s ((w.drop (k * s)).take s))
    (fun k _ => by
      simp only [stC, mkF_sg]
      rw [Function.update_of_ne (by decide), Function.update_self])
    (fun k hk => runsM_actA1 ha nm (Function.update sg 1 D) zF xF (q ^ b) s w R (sg 4) r3 hr3
      hnm3 k (le_trans (Nat.mul_le_mul_right s (by omega)) hw))
    b 0 (Or.inl hq) (by omega)
  have e0 : Function.update (stC (n := n) nm (Function.update sg 1 D) zF xF (jIdx a (q ^ b)) s w R
      (sg 4) 0) DEP5 (List.replicate b tok ++ D) =
      mkF nm (Function.update sg 4 (Sym.mark :: sg 4))
        (fun j => if j < n then Sym.mark :: zF j else zF j)
        (fun j => if j < n then Sym.mark :: xF j else xF j) := by
    simp only [stC]
    rw [updF_sg]
    refine mkF_ext ?_ ?_ (fun j hj => ?_) (fun j hj => ?_)
    · rw [Nat.zero_mul, List.drop_zero, ← hnm0, Function.update_eq_self]
    · funext i
      fin_cases i <;> simp [hsg1, arrSyms_nil]
    · simp [hj]
    · simp [hj]
  have eN : Function.update (stC (n := n) nm (Function.update sg 1 D) zF xF (jIdx a (q ^ b)) s w R
      (sg 4) (0 + q ^ b)) DEP5 (List.replicate b tok ++ D) =
      mkF (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
        (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++ Sym.mark :: sg 4))
        (fun j => List.replicate (((List.range (q ^ b)).map (jIdx a (q ^ b))).count j) tok ++
          Sym.mark :: zF j)
        (fun j => Sym.mark :: xF j) := by
    simp only [stC, Nat.zero_add]
    rw [updF_sg]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    funext i
    fin_cases i <;> simp [hsg1]
  have hrec2 := RunsM.of_eq hrec rfl e0 (by rw [Nat.zero_add]) eN le_rfl
  refine RunsM.of_eq (h0.seq (h1.seq (h2.seq (h3.seq hrec2)))) rfl rfl rfl rfl ?_
  have hcs : csum (fun k => actA1Cost n s ((w.drop (k * s)).take s)) 0 (q ^ b) =
      3 * vol (w.take (q ^ b * s)) + 23 * s * q ^ b + n * q ^ b + 14 * q ^ b := by
    simp only [actA1Cost]
    rw [csum_add_fun, csum_add_fun, csum_add_fun, csum_mul, csum_vol_blk, csum_const, csum_const,
      csum_const, Nat.zero_mul, List.drop_zero]
  have hc : q ^ b * (23 * s + n + 25) = 23 * s * q ^ b + n * q ^ b + 14 * q ^ b + 11 * q ^ b := by
    ring
  rw [hcs]
  omega

end Count

end SubNLogN.Machine.K1.SMM
