/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulB

/-!
# K5-unit, pass D (`K1/UnitMulD.lean`)

**Scope (honest summary).** Proved exact-stack specifications (no contract here):
* `runsM_actD`: one distribute step (block `t` of `MID5` onto `X_{jIdx d Q t}`);
* `runsM_catP`: the streams `X_{k-1}, …, X_0` are rewound onto `CAT5` (their concatenation
  `catL`, stream `0` on top);
* `runsM_phD`: pass D on one fiber; the accumulator receives the concatenated classes
  `catL d (distI (jIdx d Q) g)` (reversed), all scratch is restored.
Construction: [OAI26, §2.1, proof of Lemma 4] (division by `d`: distribute by the class of `t`, concatenate).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem xD_step (pD : ℕ → ℕ) (g : List (List (List Bool))) (X0 : ℕ → List Sym) (k : ℕ)
    (hk : k < g.length) :
    Function.update
      (fun j => (arrSyms (distI pD (g.take k) j).flatten).reverse ++ Sym.mark :: X0 j)
      (pD k) ((arrSyms g[k]).reverse ++
        ((arrSyms (distI pD (g.take k) (pD k)).flatten).reverse ++ Sym.mark :: X0 (pD k))) =
    fun j => (arrSyms (distI pD (g.take (k + 1)) j).flatten).reverse ++ Sym.mark :: X0 j := by
  have ht : g.take (k + 1) = g.take k ++ [g[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hl : (g.take k).length = k := by rw [List.length_take]; omega
  funext j
  rw [ht, distI_append_single, hl]
  by_cases h : j = pD k
  · subst h
    rw [Function.update_self, if_pos rfl, List.flatten_append, List.flatten_singleton,
      arrSyms_append, List.reverse_append, List.append_assoc]
  · rw [Function.update_of_ne h, if_neg (Ne.symm h), List.append_nil]

/-- Distribute-phase state after `k` steps. -/
def stD {n : ℕ} (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym)
    (pD : ℕ → ℕ) (g : List (List (List Bool))) (mid0 : List Sym) (k : ℕ) : L5 n n → List Sym :=
  mkF nm (Function.update sg 7 (arrSyms (g.drop k).flatten ++ mid0)) Z0
    (fun j => (arrSyms (distI pD (g.take k) j).flatten).reverse ++ Sym.mark :: X0 j)

section Dist

variable {n a d : ℕ}

theorem runsM_actD [NeZero d] (hd : d ≤ n) (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym)
    (Z0 X0 : ℕ → List Sym) (Q s : ℕ) (g : List (List (List Bool))) (hg : ∀ b ∈ g, b.length = s)
    (mid0 r3 : List Sym) (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3) (k : ℕ)
    (hk : k < g.length) :
    RunsM (actD n a d) (regU a d Q 0 k) (stD (n := n) nm sg Z0 X0 (jIdx d Q) g mid0 k)
      (regU a d Q 0 (k + 1)) (stD nm sg Z0 X0 (jIdx d Q) g mid0 (k + 1))
      (actA1Cost n s (g.getD k [])) := by
  have hjn : jIdx d Q k < n := lt_of_lt_of_le (jIdx_lt k) hd
  have hgk : g[k].length = s := hg _ (List.getElem_mem hk)
  have hfl : (g.drop k).flatten = g[k] ++ (g.drop (k + 1)).flatten := by
    rw [List.drop_eq_getElem_cons hk, List.flatten_cons]
  have h1 := runsM_cdMvRec (M := MU a d) (ns := SC5) (cnt := CNT5) (tmp := TMP5)
    (src := MID5) (dst := xst (jIdx d Q k)) (nm_ne_sg 3 2) (nm_ne_sg 3 3) (sg_ne_sg (by decide))
    (Ne.symm (xst_ne_sg hjn 7)) (sg_ne_sg (by decide)) (xst_ne_sg hjn 2) (nm_ne_sg 3 7)
    (Ne.symm (xst_ne_nm hjn 3)) s r3 hr3 (g.drop k).flatten mid0
    (by rw [hfl, List.length_append, hgk]; omega) (regU a d Q 0 k)
    (stD (n := n) nm sg Z0 X0 (jIdx d Q) g mid0 k)
    (by rw [stD, mkF_sg, Function.update_self])
    (by rw [stD, mkF_nm]; exact hnm3)
  rw [hfl, List.drop_left' hgk, List.take_left' hgk] at h1
  refine RunsM.of_eq ((runsM_dispatch (sel := jD)
    (ps := fun j => (blkMv MID5 (xst j) : PU n a d)) (fun o => jD_regU Q 0 k o) hjn h1).seq
    (RunsM.load (K := L5 n n) (incDf (a := a) (d := d)) (regU a d Q 0 k) _)) rfl rfl
    (incDf_regU Q 0 k) ?_ ?_
  · simp only [stD]
    rw [mkF_xst _ _ _ _ hjn, updF_sg, updF_xst _ _ _ _ hjn]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => ?_)
    · rw [Function.update_idem]
    · exact congrFun (xD_step (jIdx d Q) g X0 k hk) j
  · unfold actA1Cost
    rw [List.getD_eq_getElem _ _ hk]
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

theorem runsM_catP (nm : Fin 4 → List Sym) (zF X0 : ℕ → List Sym)
    (Y : ℕ → List (List (List Bool))) (m : MU a d) :
    ∀ k, k ≤ n → ∀ (sg : Fin 9 → List Sym) (xF : ℕ → List Sym),
      (∀ j < k, xF j = (arrSyms (Y j).flatten).reverse ++ Sym.mark :: X0 j) →
      RunsM (forN (fun j => rwd (xst j) CAT5) k : PU n a d) m (mkF nm sg zF xF) m
        (mkF nm (Function.update sg 6 (arrSyms (catL k Y).flatten ++ sg 6)) zF
          (fun j => if j < k then X0 j else xF j))
        (3 * vol (catL k Y).flatten + 2 * k + 1)
  | 0, _, sg, xF, _ => by
    refine RunsM.of_eq (RunsM.skip m _) rfl rfl rfl ?_ (by simp)
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => by simp)
    simp [catL, arrSyms_nil]
  | k + 1, hk, sg, xF, hx => by
    have hkn : k < n := by omega
    have h1 := runsM_rwd (M := MU a d) (K := L5 n n) (src := xst k) (dst := CAT5)
      (xst_ne_sg hkn 6) ((arrSyms (Y k).flatten).reverse) (X0 k)
      (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms _) m (mkF (n := n) nm sg zF xF)
      (by rw [mkF_xst _ _ _ _ hkn]; exact hx k (by omega))
    rw [mkF_sg, updF_xst _ _ _ _ hkn, updF_sg, List.reverse_reverse] at h1
    have ih := runsM_catP nm zF X0 Y m k (by omega)
      (Function.update sg 6 (arrSyms (Y k).flatten ++ sg 6)) (Function.update xF k (X0 k))
      (fun j hj => by rw [Function.update_of_ne (show j ≠ k by omega)]; exact hx j (by omega))
    refine RunsM.of_eq (h1.seq ih) rfl rfl rfl ?_ ?_
    · refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j _ => ?_)
      · rw [Function.update_idem, Function.update_self, catL_succ, List.flatten_append,
          arrSyms_append, List.append_assoc]
      · by_cases hjk : j = k
        · subst hjk; simp
        · by_cases hj : j < k
          · simp [hj, show j < k + 1 by omega]
          · simp [hj, show ¬ j < k + 1 by omega, Function.update_of_ne hjk]
    · rw [List.length_reverse, ← vol, catL_succ, List.flatten_append, vol_append]
      omega

/-- **Pass D** on one fiber (`MID5` holds the blocks `g`): distribute by the class of `t`, then
concatenate; the accumulator receives `catL d (distI (jIdx d Q) g)`, reversed. -/
theorem runsM_phD [NeZero d] (hd : d ≤ n) (q : ℕ) (hq : 2 ≤ q) (b : ℕ)
    (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (Z0 X0 : ℕ → List Sym) (s : ℕ)
    (g : List (List (List Bool))) (hgl : g.length = q ^ b) (hg : ∀ blk ∈ g, blk.length = s)
    (mid0 r3 D : List Sym) (hD : D.head? ≠ some tok) (hr3 : TermOK r3)
    (hnm3 : nm 3 = natSyms s ++ r3) (hsg1 : sg 1 = List.replicate b tok ++ D)
    (hsg7 : sg 7 = arrSyms g.flatten ++ mid0) (u t : ℕ) :
    RunsM (phD q n a d) (regU a d (q ^ b) u t) (mkF nm sg Z0 X0) (regU a d (q ^ b) 0 (q ^ b))
      (mkF nm (Function.update (Function.update sg 7 mid0) 0
        ((arrSyms (catL d (distI (jIdx d (q ^ b)) g)).flatten).reverse ++ sg 0)) Z0 X0)
      (3 * vol g.flatten + 6 * vol (catL d (distI (jIdx d (q ^ b)) g)).flatten +
        q ^ b * (23 * s + n + 25) + 3 * n + 7) := by
  have h0 := RunsM.load (K := L5 n n) (rstf (a := a) (d := d)) (regU a d (q ^ b) u t)
    (mkF (n := n) nm sg Z0 X0)
  rw [rstf_regU] at h0
  have h1 := runsM_pushX nm sg (regU a d (q ^ b) 0 0) Z0 n le_rfl X0
  have h2 := RunsM.push (M := MU a d) CAT5 Sym.mark (regU a d (q ^ b) 0 0)
    (mkF (n := n) nm sg Z0 (fun j => if j < n then Sym.mark :: X0 j else X0 j))
  rw [mkF_sg, updF_sg] at h2
  have hrec := runsM_recProg q DEP5 (actD n a d) closed_actD D hD (q ^ b)
    (fun k => regU a d (q ^ b) 0 k)
    (stD (n := n) nm (Function.update (Function.update sg 1 D) 6 (Sym.mark :: sg 6)) Z0 X0
      (jIdx d (q ^ b)) g mid0)
    (fun k => actA1Cost n s (g.getD k []))
    (fun k _ => by
      simp only [stD, mkF_sg]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
    (fun k hk => runsM_actD hd nm (Function.update (Function.update sg 1 D) 6 (Sym.mark :: sg 6))
      Z0 X0 (q ^ b) s g hg mid0 r3 hr3 hnm3 k (by omega))
    b 0 (Or.inl hq) (by omega)
  have e0 : Function.update (stD (n := n) nm (Function.update (Function.update sg 1 D) 6
      (Sym.mark :: sg 6)) Z0 X0 (jIdx d (q ^ b)) g mid0 0) DEP5 (List.replicate b tok ++ D) =
      mkF nm (Function.update sg 6 (Sym.mark :: sg 6)) Z0
        (fun j => if j < n then Sym.mark :: X0 j else X0 j) := by
    simp only [stD]
    rw [updF_sg]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j hj => ?_)
    · funext i
      fin_cases i <;> simp [hsg1, hsg7]
    · simp [hj, distI, arrSyms_nil]
  have eN : Function.update (stD (n := n) nm (Function.update (Function.update sg 1 D) 6
      (Sym.mark :: sg 6)) Z0 X0 (jIdx d (q ^ b)) g mid0 (0 + q ^ b)) DEP5
      (List.replicate b tok ++ D) =
      mkF nm (Function.update (Function.update sg 6 (Sym.mark :: sg 6)) 7 mid0) Z0
        (fun j => (arrSyms (distI (jIdx d (q ^ b)) g j).flatten).reverse ++ Sym.mark :: X0 j) := by
    simp only [stD, Nat.zero_add]
    rw [updF_sg, List.drop_of_length_le (le_of_eq hgl), List.take_of_length_le (le_of_eq hgl)]
    refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    funext i
    fin_cases i <;> simp [hsg1, arrSyms_nil]
  have hrec2 := RunsM.of_eq hrec rfl e0 (by rw [Nat.zero_add]) eN le_rfl
  have hcat := runsM_catP nm Z0 X0 (distI (jIdx d (q ^ b)) g) (regU a d (q ^ b) 0 (q ^ b)) n le_rfl
    (Function.update (Function.update sg 6 (Sym.mark :: sg 6)) 7 mid0)
    (fun j => (arrSyms (distI (jIdx d (q ^ b)) g j).flatten).reverse ++ Sym.mark :: X0 j)
    (fun j _ => rfl)
  have hnil : catL n (distI (jIdx d (q ^ b)) g) = catL d (distI (jIdx d (q ^ b)) g) := by
    rw [show n = d + (n - d) by omega]
    exact catL_nil_tail _ d (fun j hj => distI_jIdx_ge _ j hj) (n - d)
  rw [hnil] at hcat
  have h5 := runsM_rwd (M := MU a d) (K := L5 n n) (src := CAT5) (dst := ACC5)
    (sg_ne_sg (by decide)) (arrSyms (catL d (distI (jIdx d (q ^ b)) g)).flatten) (sg 6)
    (mark_not_mem_arrSyms _) (regU a d (q ^ b) 0 (q ^ b))
    (mkF (n := n) nm (Function.update (Function.update (Function.update sg 6 (Sym.mark :: sg 6)) 7
      mid0) 6 (arrSyms (catL d (distI (jIdx d (q ^ b)) g)).flatten ++
        Function.update (Function.update sg 6 (Sym.mark :: sg 6)) 7 mid0 6)) Z0
      (fun j => if j < n then X0 j else
        (arrSyms (distI (jIdx d (q ^ b)) g j).flatten).reverse ++ Sym.mark :: X0 j))
    (by rw [mkF_sg, Function.update_self, Function.update_of_ne (by decide),
      Function.update_self])
  rw [mkF_sg, updF_sg, updF_sg] at h5
  refine RunsM.of_eq (h0.seq (h1.seq (h2.seq (hrec2.seq (hcat.seq h5))))) rfl rfl rfl ?_ ?_
  · refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun j hj => by simp [hj])
    funext i
    fin_cases i <;> simp
  · have hcs : csum (fun k => actA1Cost n s (g.getD k [])) 0 (q ^ b) =
        3 * vol g.flatten + 23 * s * q ^ b + n * q ^ b + 14 * q ^ b := by
      simp only [actA1Cost]
      rw [csum_add_fun, csum_add_fun, csum_add_fun, csum_mul, csum_const, csum_const, csum_const,
        ← hgl, csum_getD vol [] g, ← vol_flatten]
    have hc : q ^ b * (23 * s + n + 25) =
        23 * s * q ^ b + n * q ^ b + 14 * q ^ b + 11 * q ^ b := by ring
    rw [hcs, ← vol]
    omega

end Dist

end SubNLogN.Machine.K1.SMM
