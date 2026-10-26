import WP.W9c.BlockPackFin

/-!
# WP.W9c.BlockPackAll — `bpProg` meets the stack specification of `W9c_blockPack`

`ht_bp`: from any host stacks with the contract's preconditions, `bpProg` reaches exactly the
contract's final stacks within `costBP …` steps. `partP`/`partN` are the routed parts of the
`n = (v.take W).length` numbers read; their packs `P⁺`, `P⁻` differ by the signed pack of the
quantized block (`pack_sub`, `aP_sub_aN`).
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability IntMul

/-- Positive parts of the numbers read. -/
def partP (p_in q W : ℕ) (v : List ℤ) : List ℕ := (v.take (v.take W).length).map (aP p_in q)

/-- Negative parts of the numbers read. -/
def partN (p_in q W : ℕ) (v : List ℤ) : List ℕ := (v.take (v.take W).length).map (aN p_in q)

theorem length_partP (p_in q W : ℕ) (v : List ℤ) : (partP p_in q W v).length = (v.take W).length := by
  have hnv : (v.take W).length ≤ v.length := by rw [List.length_take]; exact min_le_right _ _
  rw [partP, List.length_map, List.length_take, Nat.min_eq_left hnv]

theorem length_partN (p_in q W : ℕ) (v : List ℤ) : (partN p_in q W v).length = (v.take W).length := by
  have hnv : (v.take W).length ≤ v.length := by rw [List.length_take]; exact min_le_right _ _
  rw [partN, List.length_map, List.length_take, Nat.min_eq_left hnv]

/-- The two packs differ by the signed pack of the quantized block. -/
theorem packs_sub (k p_in q W : ℕ) (v : List ℤ) :
    ((packNat (2 ^ k) (partP p_in q W v) : ℕ) : ℤ) - ((packNat (2 ^ k) (partN p_in q W v) : ℕ) : ℤ) =
      packSignedKronecker ((2 ^ k : ℕ) : ℤ) ((v.take W).map (gQuantizeCoordToScale p_in q)) := by
  rw [partP, partN, take_take_length, pack_sub]
  congr 1
  exact List.map_congr_left (fun x _ => aP_sub_aN p_in q x)

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- **The whole program on host stacks.** -/
theorem ht_bp (hK : K.OK C) (r : HS) (k p_in q W B : ℕ) (v : List ℤ) (rx rk ra rb rW : List Sym)
    (hk1 : 1 ≤ k) (hvB : ∀ x ∈ v, bitLen x.natAbs ≤ B) (hrx : EndOK rx) (hrk : TermOK rk)
    (hra : TermOK ra) (hrb : TermOK rb) (hrW : TermOK rW)
    (hx : r.x = listSyms v ++ rx) (hk : r.k = natSyms k ++ rk) (hp : r.p = natSyms p_in ++ ra)
    (hq : r.q = natSyms q ++ rb) (hw : r.w = natSyms W ++ rW) :
    HT ρ r.f (bpProg K)
      ((r.set kX (listSyms (v.drop W) ++ rx)).set kD
        (intSyms (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
          ((v.take W).map (gQuantizeCoordToScale p_in q))) ++ r.d)).f
      (costBP C B k p_in q W (v.take W).length (packNat (2 ^ k) (partP p_in q W v))
        (packNat (2 ^ k) (partN p_in q W v))) := by
  obtain ⟨x0, k0, p0, q0, w0, d0, cw0, cp0, cn0, tp0, tn0, u0, sh0, sg0⟩ := r
  dsimp only at hx hk hp hq hw
  subst hx hk hp hq hw
  let r : HS := ⟨listSyms v ++ rx, natSyms k ++ rk, natSyms p_in ++ ra, natSyms q ++ rb,
    natSyms W ++ rW, d0, cw0, cp0, cn0, tp0, tn0, u0, sh0, sg0⟩
  have s1 := ht_setup (ρ := ρ) hK r k p_in q W v rx rW hrW rfl rfl
  have s2 := ht_mainLoop (ρ := ρ) hK r k p_in q W B v rx rk ra rb hvB hk1 hrx hrk hra hrb rfl rfl
    rfl
  -- drop the counter
  let st := stMain r k p_in q W v rx (v.take W).length
  have s3 : HT ρ st.f (cDrop K kCW) (st.set kCW (Sym.mark :: cw0)).f
      (C * (bitLen (W - (v.take W).length) + 1)) :=
    ht_drop hK st kCW (W - (v.take W).length) (Sym.mark :: cw0) (termOK_mark _) rfl
  have s4 : HT ρ (st.set kCW (Sym.mark :: cw0)).f (popS kCW)
      ((st.set kCW (Sym.mark :: cw0)).set kCW cw0).f 1 :=
    ht_pop _ kCW Sym.mark cw0 rfl
  let q1 := (st.set kCW (Sym.mark :: cw0)).set kCW cw0
  -- Horner passes
  let q2 := (q1.set kCP (natSyms (packNat (2 ^ k) (partP p_in q W v)) ++ Sym.mark :: cp0)).set
    kTP tp0
  have s5 : HT ρ q1.f (hornerP K true) q2.f
      ((v.take W).length * (C * (2 * (B + k + p_in + q + 2)) + 3) + 3) := by
    have h := ht_horner (ρ := ρ) hK true q1 k (chain k (partP p_in q W v)).1
      (chain k (partP p_in q W v)).2 (2 * (B + k + p_in + q + 2)) (Sym.mark :: cp0) tp0 rk
      (termOK_mark _) hrk rfl (chunk_lt k _) (by omega)
    rw [stH_full, hval_chain, length_chain, length_partP] at h
    exact h
  let q3 := (q2.set kCN (natSyms (packNat (2 ^ k) (partN p_in q W v)) ++ Sym.mark :: cn0)).set
    kTN tn0
  have s6 : HT ρ q2.f (hornerP K false) q3.f
      ((v.take W).length * (C * (2 * (B + k + p_in + q + 2)) + 3) + 3) := by
    have h := ht_horner (ρ := ρ) hK false q2 k (chain k (partN p_in q W v)).1
      (chain k (partN p_in q W v)).2 (2 * (B + k + p_in + q + 2)) (Sym.mark :: cn0) tn0 rk
      (termOK_mark _) hrk rfl (chunk_lt k _) (by omega)
    rw [stH_full, hval_chain, length_chain, length_partN] at h
    exact h
  -- subtract and restore
  let f1 := q3.set kCP (Sym.pos :: (natSyms (packNat (2 ^ k) (partP p_in q W v)) ++
    Sym.mark :: cp0))
  let f2 := f1.set kCN (Sym.pos :: (natSyms (packNat (2 ^ k) (partN p_in q W v)) ++
    Sym.mark :: cn0))
  let f3 := f2.set kD (intSyms (((packNat (2 ^ k) (partP p_in q W v) : ℕ) : ℤ) -
    ((packNat (2 ^ k) (partN p_in q W v) : ℕ) : ℤ)) ++ d0)
  let f4 := f3.set kCP (natSyms (packNat (2 ^ k) (partP p_in q W v)) ++ Sym.mark :: cp0)
  let f5 := f4.set kCN (natSyms (packNat (2 ^ k) (partN p_in q W v)) ++ Sym.mark :: cn0)
  let f6 := f5.set kCP (Sym.mark :: cp0)
  let f7 := f6.set kCP cp0
  let f8 := f7.set kCN (Sym.mark :: cn0)
  let f9 := f8.set kCN cn0
  let f10 := f9.set kU u0
  let f11 := f10.set kSH sh0
  have t1 : HT ρ q3.f (pushS kCP Sym.pos) f1.f 1 := ht_push q3 kCP Sym.pos
  have t2 : HT ρ f1.f (pushS kCN Sym.pos) f2.f 1 := ht_push f1 kCN Sym.pos
  have t3 : HT ρ f2.f (cSubI K kCP kCN kD) f3.f
      (C * (bitLen (packNat (2 ^ k) (partP p_in q W v)) +
        bitLen (packNat (2 ^ k) (partN p_in q W v)) + 1)) :=
    ht_subI hK f2 kCP kCN kD (by decide) _ _ (Sym.mark :: cp0) (Sym.mark :: cn0)
      (termOK_mark _) (termOK_mark _) (intSyms_natCast' _ _) (intSyms_natCast' _ _)
  have t4 : HT ρ f3.f (popS kCP) f4.f 1 := ht_pop f3 kCP Sym.pos _ rfl
  have t5 : HT ρ f4.f (popS kCN) f5.f 1 := ht_pop f4 kCN Sym.pos _ rfl
  have t6 : HT ρ f5.f (cDrop K kCP) f6.f (C * (bitLen (packNat (2 ^ k) (partP p_in q W v)) + 1)) :=
    ht_drop hK f5 kCP _ (Sym.mark :: cp0) (termOK_mark _) rfl
  have t7 : HT ρ f6.f (popS kCP) f7.f 1 := ht_pop f6 kCP Sym.mark cp0 rfl
  have t8 : HT ρ f7.f (cDrop K kCN) f8.f (C * (bitLen (packNat (2 ^ k) (partN p_in q W v)) + 1)) :=
    ht_drop hK f7 kCN _ (Sym.mark :: cn0) (termOK_mark _) rfl
  have t9 : HT ρ f8.f (popS kCN) f9.f 1 := ht_pop f8 kCN Sym.mark cn0 rfl
  have t10 : HT ρ f9.f (popS kU) f10.f 1 := ht_pop f9 kU Sym.mark u0 rfl
  have t11 : HT ρ f10.f (popS kSH) f11.f 1 := ht_pop f10 kSH Sym.mark sh0 rfl
  have fin := HT.seq t1 (HT.seq t2 (HT.seq t3 (HT.seq t4 (HT.seq t5 (HT.seq t6 (HT.seq t7
    (HT.seq t8 (HT.seq t9 (HT.seq t10 t11)))))))))
  have hall := HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 (HT.seq s6 fin)))))
  refine hall.of_eq ?_ ?_
  · rw [← packs_sub, ← drop_take_length v W]
    rfl
  · have hm := Nat.mul_le_mul_left C (Nat.add_le_add_right
      (bitLen_mono (Nat.sub_le W (v.take W).length)) 1)
    unfold costBP
    omega

#assert_std_axioms length_partP length_partN packs_sub ht_bp

end WP.W9c.BlockPack
