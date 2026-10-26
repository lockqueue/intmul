/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulCut

/-!
# K5-unit, the merge phase (`K1/UnitMulB.lean`)

**Scope (honest summary).** Proved (no contract here):
* `perm_mul_mod`, `vol_catL_distI`: concatenating the residue classes permutes the blocks, so it
  keeps the volume;
* `runsM_actA2`: one merge step of pass A (the next block of `X_{jIdx a Q u}` onto `TMP25`);
* `runsM_phA3`: phase 3 of pass A on one fiber: the `Q` merge steps (by `recProg`), the stream
  marks are dropped and the output (in order) lands on `MID5`.
Construction: [OAI26, §2.1, proof of Lemma 4] (merge by the residue pattern).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem perm_mul_mod {c Q : ℕ} (hcQ : Nat.Coprime Q c) :
    ((List.range Q).map (fun t => c * t % Q)).Perm (List.range Q) := by
  have hnd : ((List.range Q).map (fun t => c * t % Q)).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro t1 ht1 t2 ht2 h
    simp only [List.mem_range] at ht1 ht2
    have h' : c * t1 ≡ c * t2 [MOD Q] := h
    have := Nat.ModEq.cancel_left_of_coprime hcQ.gcd_eq_one h'
    rw [Nat.ModEq, Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht2] at this
    exact this
  have hsub : (List.range Q).map (fun t => c * t % Q) ⊆ List.range Q := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx ⊢
    obtain ⟨t, ht, rfl⟩ := hx
    exact Nat.mod_lt _ (by omega)
  exact (hnd.subperm hsub).perm_of_length_le (by simp)

theorem map_getD_range {β : Type} (g : List β) (dflt : β) :
    (List.range g.length).map (fun i => g.getD i dflt) = g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

theorem vol_catL_distI {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (g : List (List (List Bool)))
    (hg : g.length = Q) : vol (catL c (distI (jIdx c Q) g)).flatten = vol g.flatten := by
  rw [catL_distI hcQ g hg, vol_flatten, vol_flatten, List.map_map]
  have e : (List.range Q).map (vol ∘ fun t => g.getD (c * t % Q) default) =
      ((List.range Q).map (fun t => c * t % Q)).map (fun i => vol (g.getD i [])) := by
    rw [List.map_map]; rfl
  rw [e, ((perm_mul_mod hcQ).map _).sum_eq]
  conv_rhs => rw [← map_getD_range g [], hg, List.map_map]
  rfl

theorem vol_mulOut {c Q : ℕ} [NeZero c] (hcQ : Nat.Coprime Q c) (f : List (List (List Bool)))
    (hf : f.length = Q) : vol (mulOut c Q f).flatten = vol f.flatten := by
  rw [← vol_catL_distI hcQ _ (length_mulOut c Q f), mulA_cat hcQ f hf]

theorem csum_getD {β : Type} (f : β → ℕ) (dflt : β) :
    ∀ g : List β, csum (fun k => f (g.getD k dflt)) 0 g.length = (g.map f).sum
  | [] => rfl
  | x :: g => by
    rw [List.length_cons, csum, ← csum_shift]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons]
    rw [csum_getD f dflt g]

theorem xA_step (pA : ℕ → ℕ) (g : List (List (List Bool))) (X0 : ℕ → List Sym) (k : ℕ)
    (hk : k < g.length) :
    Function.update
      (fun j => arrSyms (distI (fun x => pA (x + k)) (g.drop k) j).flatten ++ Sym.mark :: X0 j)
      (pA k) (arrSyms (distI (fun x => pA (x + (k + 1))) (g.drop (k + 1)) (pA k)).flatten ++
        Sym.mark :: X0 (pA k)) =
    fun j => arrSyms (distI (fun x => pA (x + (k + 1))) (g.drop (k + 1)) j).flatten ++
      Sym.mark :: X0 j := by
  funext j
  by_cases h : j = pA k
  · subst h
    rw [Function.update_self]
  · rw [Function.update_of_ne h, distI_drop_cons pA g k hk, if_neg (Ne.symm h), List.nil_append]

/-- Merge-phase state after `k` steps (`g` the output blocks, `pA` the class pattern). -/
def stM {n : ℕ} (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym)
    (pA : ℕ → ℕ) (g : List (List (List Bool))) (t0 : List Sym) (k : ℕ) : L5 n n → List Sym :=
  mkF nm (Function.update sg 5 ((arrSyms (g.take k).flatten).reverse ++ Sym.mark :: t0)) Z0
    (fun j => arrSyms (distI (fun x => pA (x + k)) (g.drop k) j).flatten ++ Sym.mark :: X0 j)

section Merge

variable {n a d : ℕ}

theorem runsM_actA2 [NeZero a] (ha : a ≤ n) (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym)
    (Z0 X0 : ℕ → List Sym) (Q s : ℕ) (g : List (List (List Bool))) (hg : ∀ b ∈ g, b.length = s)
    (t0 r3 : List Sym) (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3) (k : ℕ)
    (hk : k < g.length) :
    RunsM (actA2 n a d) (regU a d Q k 0) (stM (n := n) nm sg Z0 X0 (jIdx a Q) g t0 k)
      (regU a d Q (k + 1) 0) (stM nm sg Z0 X0 (jIdx a Q) g t0 (k + 1))
      (actA1Cost n s (g.getD k [])) := by
  have hjn : jIdx a Q k < n := lt_of_lt_of_le (jIdx_lt k) ha
  have hgk : g[k].length = s := hg _ (List.getElem_mem hk)
  have hsrc : (stM (n := n) nm sg Z0 X0 (jIdx a Q) g t0 k) (xst (jIdx a Q k)) =
      arrSyms (g[k] ++ (distI (fun x => jIdx a Q (x + (k + 1))) (g.drop (k + 1))
        (jIdx a Q k)).flatten) ++ Sym.mark :: X0 (jIdx a Q k) := by
    rw [stM, mkF_xst _ _ _ _ hjn]
    rw [distI_drop_cons _ g k hk, if_pos rfl, List.flatten_append, List.flatten_singleton]
  have h1 := runsM_cdMvRec (M := MU a d) (ns := SC5) (cnt := CNT5) (tmp := TMP5)
    (src := xst (jIdx a Q k)) (dst := TMP25) (nm_ne_sg 3 2) (nm_ne_sg 3 3) (sg_ne_sg (by decide))
    (xst_ne_sg hjn 5) (xst_ne_sg hjn 2) (sg_ne_sg (by decide)) (Ne.symm (xst_ne_nm hjn 3))
    (nm_ne_sg 3 5) s r3 hr3
    (g[k] ++ (distI (fun x => jIdx a Q (x + (k + 1))) (g.drop (k + 1)) (jIdx a Q k)).flatten)
    (Sym.mark :: X0 (jIdx a Q k)) (by rw [List.length_append, hgk]; omega) (regU a d Q k 0)
    (stM (n := n) nm sg Z0 X0 (jIdx a Q) g t0 k) hsrc (by rw [stM, mkF_nm]; exact hnm3)
  rw [List.drop_left' hgk, List.take_left' hgk] at h1
  refine RunsM.of_eq ((runsM_dispatch (sel := jA)
    (ps := fun j => (blkMv (xst j) TMP25 : PU n a d)) (fun o => jA_regU Q k 0 o) hjn h1).seq
    (RunsM.load (K := L5 n n) (incAf (a := a) (d := d)) (regU a d Q k 0) _)) rfl rfl
    (incAf_regU Q k 0) ?_ ?_
  · simp only [stM]
    rw [mkF_sg, updF_xst _ _ _ _ hjn, updF_sg]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => ?_)
    · rw [Function.update_idem, Function.update_self, List.take_add_one,
        List.getElem?_eq_getElem hk, Option.toList_some, List.flatten_append,
        List.flatten_singleton, arrSyms_append, List.reverse_append, List.append_assoc]
    · exact congrFun (xA_step (jIdx a Q) g X0 k hk) j
  · unfold actA1Cost
    rw [List.getD_eq_getElem _ _ hk]
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

/-- **Phase 3 of pass A** on one fiber: the `Q = q^b` merge steps; the output blocks `g`
(in order) land on `MID5`, the streams are restored. -/
theorem runsM_phA3 [NeZero a] (ha : a ≤ n) (q : ℕ) (hq : 2 ≤ q) (b : ℕ)
    (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym) (s : ℕ)
    (g : List (List (List Bool))) (hgl : g.length = q ^ b) (hg : ∀ blk ∈ g, blk.length = s)
    (r3 D : List Sym) (hD : D.head? ≠ some tok) (hr3 : TermOK r3)
    (hnm3 : nm 3 = natSyms s ++ r3) (hsg1 : sg 1 = List.replicate b tok ++ D) (u t : ℕ) :
    RunsM (phA3 q n a d) (regU a d (q ^ b) u t)
      (mkF nm sg Z0 (fun j => arrSyms (distI (jIdx a (q ^ b)) g j).flatten ++ Sym.mark :: X0 j))
      (regU a d (q ^ b) (q ^ b) 0)
      (mkF nm (Function.update sg 7 (arrSyms g.flatten ++ sg 7)) Z0 X0)
      (6 * vol g.flatten + q ^ b * (23 * s + n + 25) + n + 5) := by
  have h0 := RunsM.load (K := L5 n n) (rstf (a := a) (d := d)) (regU a d (q ^ b) u t)
    (mkF (n := n) nm sg Z0
      (fun j => arrSyms (distI (jIdx a (q ^ b)) g j).flatten ++ Sym.mark :: X0 j))
  rw [rstf_regU] at h0
  have h1 := RunsM.push (M := MU a d) TMP25 Sym.mark (regU a d (q ^ b) 0 0)
    (mkF (n := n) nm sg Z0
      (fun j => arrSyms (distI (jIdx a (q ^ b)) g j).flatten ++ Sym.mark :: X0 j))
  rw [mkF_sg, updF_sg] at h1
  have hrec := runsM_recProg q DEP5 (actA2 n a d) closed_actA2 D hD (q ^ b)
    (fun k => regU a d (q ^ b) k 0)
    (stM (n := n) nm (Function.update sg 1 D) Z0 X0 (jIdx a (q ^ b)) g (sg 5))
    (fun k => actA1Cost n s (g.getD k []))
    (fun k _ => by
      simp only [stM, mkF_sg]
      rw [Function.update_of_ne (by decide), Function.update_self])
    (fun k hk => runsM_actA2 ha nm (Function.update sg 1 D) Z0 X0 (q ^ b) s g hg (sg 5) r3 hr3
      hnm3 k (by omega))
    b 0 (Or.inl hq) (by omega)
  have e0 : Function.update (stM (n := n) nm (Function.update sg 1 D) Z0 X0 (jIdx a (q ^ b)) g
      (sg 5) 0) DEP5 (List.replicate b tok ++ D) =
      mkF nm (Function.update sg 5 (Sym.mark :: sg 5)) Z0
        (fun j => arrSyms (distI (jIdx a (q ^ b)) g j).flatten ++ Sym.mark :: X0 j) := by
    simp only [stM]
    rw [updF_sg]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => ?_)
    · funext i
      fin_cases i <;> simp [hsg1, arrSyms_nil]
    · simp only [Nat.add_zero, List.drop_zero]
  have eN : Function.update (stM (n := n) nm (Function.update sg 1 D) Z0 X0 (jIdx a (q ^ b)) g
      (sg 5) (0 + q ^ b)) DEP5 (List.replicate b tok ++ D) =
      mkF nm (Function.update sg 5 ((arrSyms g.flatten).reverse ++ Sym.mark :: sg 5)) Z0
        (fun j => Sym.mark :: X0 j) := by
    simp only [stM, Nat.zero_add]
    rw [updF_sg]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => ?_)
    · rw [List.take_of_length_le (le_of_eq hgl)]
      funext i
      fin_cases i <;> simp [hsg1]
    · rw [List.drop_of_length_le (le_of_eq hgl)]
      simp [distI, arrSyms_nil]
  have hrec2 := RunsM.of_eq hrec rfl e0 (by rw [Nat.zero_add]) eN le_rfl
  have h3 := runsM_popX nm (Function.update sg 5 ((arrSyms g.flatten).reverse ++ Sym.mark :: sg 5))
    (regU a d (q ^ b) (q ^ b) 0) Z0 X0 n le_rfl (fun j => Sym.mark :: X0 j) (fun j _ => rfl)
  have h4 := runsM_rwd (M := MU a d) (K := L5 n n) (src := TMP25) (dst := MID5)
    (sg_ne_sg (by decide)) ((arrSyms g.flatten).reverse) (sg 5)
    (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms _) (regU a d (q ^ b) (q ^ b) 0)
    (mkF (n := n) nm (Function.update sg 5 ((arrSyms g.flatten).reverse ++ Sym.mark :: sg 5)) Z0
      (fun j => if j < n then X0 j else Sym.mark :: X0 j))
    (by rw [mkF_sg, Function.update_self])
  rw [mkF_sg, updF_sg, updF_sg, Function.update_of_ne (by decide), List.reverse_reverse] at h4
  refine RunsM.of_eq (h0.seq (h1.seq (hrec2.seq (h3.seq h4)))) rfl rfl rfl ?_ ?_
  · refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j hj => by simp [hj])
    rw [Function.update_idem, Function.update_eq_self]
  · have hcs : csum (fun k => actA1Cost n s (g.getD k [])) 0 (q ^ b) =
        3 * vol g.flatten + 23 * s * q ^ b + n * q ^ b + 14 * q ^ b := by
      simp only [actA1Cost]
      rw [csum_add_fun, csum_add_fun, csum_add_fun, csum_mul, csum_const, csum_const, csum_const,
        ← hgl, csum_getD vol [] g, ← vol_flatten]
    have hc : q ^ b * (23 * s + n + 25) =
        23 * s * q ^ b + n * q ^ b + 14 * q ^ b + 11 * q ^ b := by ring
    rw [hcs, List.length_reverse, ← vol]
    omega

end Merge

end SubNLogN.Machine.K1.SMM
