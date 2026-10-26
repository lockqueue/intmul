/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulD

/-!
# K5-unit, one fiber (`K1/UnitMulFib.lean`)

**Scope (honest summary).** Proved exact-stack specification for a single fiber (no contract here):
* `runsM_fibU`: one fiber of `Q = q^b` blocks of `s` records; the accumulator receives
  `unitFib Q s a d w` (block `t` = input block `d·t·a⁻¹ mod Q`), reversed; cost at most
  `(230 + 12·n)·vol` of the fiber (`n = max a d`, a compile-time constant).
  (The multi-fiber loop `loopM_fibU` for `unitOutAll` and the depth-token setup `runsM_setupU`
  are proved in `K1/UnitMulLoop.lean`.)
Construction: [OAI26, §2.1, proof of Lemma 4]; paper: Fact 3.3(4) (`fact:oai-streams`)
and Lemma A.4 (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

section Fiber

variable {n a d : ℕ}

/-- **One fiber** of the unit kernel. -/
theorem runsM_fibU [NeZero a] [NeZero d] (ha : a ≤ n) (hd : d ≤ n) (q : ℕ) (hq : 2 ≤ q) (b : ℕ)
    (hca : Nat.Coprime (q ^ b) a) (hcd : Nat.Coprime (q ^ b) d)
    (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym) (s : ℕ) (hs : 1 ≤ s)
    (w : List (List Bool)) (R r3 D : List Sym) (hD : D.head? ≠ some tok) (hr3 : TermOK r3)
    (hw : q ^ b * s ≤ w.length) (hnm0 : nm 0 = arrSyms w ++ R) (hnm3 : nm 3 = natSyms s ++ r3)
    (hsg1 : sg 1 = List.replicate b tok ++ D) (u t : ℕ) :
    RunsM (fibU q n a d) (regU a d (q ^ b) u t) (mkF nm sg zF xF) (regU a d (q ^ b) 0 (q ^ b))
      (mkF (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
        (Function.update sg 0 ((arrSyms (unitFib (q ^ b) s a d w)).reverse ++ sg 0)) zF xF)
      ((230 + 12 * n) * vol (w.take (q ^ b * s))) := by
  have hfbl : ((List.range (q ^ b)).map (blkOf s w)).length = q ^ b := by simp
  have hfb : ∀ blk ∈ (List.range (q ^ b)).map (blkOf s w), blk.length = s := by
    intro blk hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    exact blkOf_length s w t (le_trans (Nat.mul_le_mul_right s (by omega)) hw)
  have hflat : ((List.range (q ^ b)).map (blkOf s w)).flatten = w.take (q ^ b * s) := by
    rw [take_mul_flatMap w s (q ^ b), List.flatMap_def]
    rfl
  set g := mulOut a (q ^ b) ((List.range (q ^ b)).map (blkOf s w)) with hgdef
  have hgl : g.length = q ^ b := length_mulOut _ _ _
  have hg : ∀ blk ∈ g, blk.length = s := by
    intro blk hb
    rw [hgdef, mulOut] at hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨u', hu', rfl⟩ := hb
    have hk : ((a : ZMod (q ^ b))⁻¹).val * u' % q ^ b < q ^ b := Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem _ _ (by rw [hfbl]; exact hk)]
    exact hfb _ (List.getElem_mem _)
  have hnm3' : (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R)) 3 = natSyms s ++ r3 := by
    rw [Function.update_of_ne (by decide)]; exact hnm3
  have hA1 := runsM_phA1 (d := d) ha q hq b nm sg zF xF s w R r3 D hD hr3 hw hnm0 hnm3 hsg1 u t
  have hA2 := runsM_phA2 (d := d) ha (q ^ b) hca
    (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
    (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++ Sym.mark :: sg 4)) zF xF s r3
    hr3 hnm3' w hw (sg 4) (regU a d (q ^ b) (q ^ b) 0) (Function.update_self _ _ _)
  have hA3 := runsM_phA3 (d := d) ha q hq b
    (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
    (Function.update (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++
      Sym.mark :: sg 4)) 4 (sg 4)) zF xF s g hgl hg r3 D hD hr3 hnm3'
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hsg1)
    (q ^ b) 0
  have hDp := runsM_phD (a := a) hd q hq b
    (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
    (Function.update (Function.update (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++
      Sym.mark :: sg 4)) 4 (sg 4)) 7 (arrSyms g.flatten ++
      Function.update (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++
        Sym.mark :: sg 4)) 4 (sg 4) 7)) zF xF s g hgl hg
    (Function.update (Function.update sg 4 ((arrSyms (w.take (q ^ b * s))).reverse ++
      Sym.mark :: sg 4)) 4 (sg 4) 7) r3 D hD hr3 hnm3'
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hsg1)
    (Function.update_self _ _ _) (q ^ b) 0
  refine RunsM.of_eq (hA1.seq (hA2.seq (hA3.seq hDp))) rfl rfl rfl ?_ ?_
  · refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    rw [hgdef, unitFib_eq (q ^ b) s a d hcd w]
    funext i
    fin_cases i <;> simp
  · rw [vol_catL_distI hcd g hgl, hgdef, vol_mulOut hca _ hfbl, hflat]
    have hV1 : q ^ b * s ≤ vol (w.take (q ^ b * s)) := by
      have := length_le_vol (w.take (q ^ b * s))
      rw [List.length_take, Nat.min_eq_left hw] at this
      exact this
    have hQs : q ^ b ≤ q ^ b * s := Nat.le_mul_of_pos_right _ hs
    have hQ1 : 1 ≤ q ^ b := Nat.one_le_pow _ _ (by omega)
    have hnQ : n * q ^ b ≤ n * vol (w.take (q ^ b * s)) := Nat.mul_le_mul_left n (by omega)
    have hnV : n ≤ n * vol (w.take (q ^ b * s)) := Nat.le_mul_of_pos_right n (by omega)
    have e1 : q ^ b * (23 * s + n + 25) = 23 * (q ^ b * s) + n * q ^ b + 25 * q ^ b := by ring
    have e2 : q ^ b * (26 * s + 17) = 26 * (q ^ b * s) + 17 * q ^ b := by ring
    have e3 : (230 + 12 * n) * vol (w.take (q ^ b * s)) =
        230 * vol (w.take (q ^ b * s)) + 12 * (n * vol (w.take (q ^ b * s))) := by ring
    omega

end Fiber

end SubNLogN.Machine.K1.SMM
