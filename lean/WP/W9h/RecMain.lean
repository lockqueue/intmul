import WP.W9h.RecLoops

/-!
# WP.W9h.RecMain — **`W9_reconstruct`** from the W3 contracts

`HT_recProg`: the host program maps `OA = hdrSyms cs ++ rA` to
`natSyms (reconstructChunksTree b cs) ++ rA`, everything else restored, at cost
`(C+1)·recTot …`. `W9_reconstruct_holds`: transported to `BLoc` (`runs_of_HT`), with
`recTot ≤ 100·(|cs|·(b + wD + K0 + 1) + rootHdrLen + 1)`.
-/

namespace WP.W9h

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem rootHdrLen_eq (b K0 k1 k2 : ℕ) :
    rootHdrLen b K0 k1 k2 = bitLen b + bitLen K0 + bitLen k1 + bitLen k2 + 4 := by
  simp [rootHdrLen, hdrSyms, length_natSyms]
  omega

theorem HT.pre_eq {a b : ℕ} {σ : Type} {ρ : List (Prog (Loc a b) (fun _ => Sym) σ)}
    {B B0 B' : Loc a b → List Sym} {p : Prog (Loc a b) (fun _ => Sym) σ} {T : ℕ}
    (h : HT ρ B0 p B' T) (e : B = B0) : HT ρ B p B' T := e ▸ h

/-- The final carry has at most `|cs|·(wD + K0 + 1)` bits. -/
theorem bitLen_carry_le (b K0 wD : ℕ) (cs : List ℕ) (hK0 : cs.length ≤ 2 ^ K0)
    (hwD : ∀ c ∈ cs, bitLen c ≤ wD) : bitLen (carryRun b 0 cs).2 ≤ cs.length * (wD + K0 + 1) := by
  rcases cs with _ | ⟨x, xs⟩
  · simp [carryRun, bitLen_zero]
  · have h := bitLen_sum_le (s := (carryRun b 0 (x :: xs)).2) (x :: xs) hwD hK0
      (by have := carryRun_snd_le b 0 (x :: xs); omega)
    simp only [List.length_cons]
    nlinarith

/-- Cost factor of the reconstruct program. -/
def recTot (b K0 k1 k2 wD n R : ℕ) : ℕ :=
  (bitLen b + 1 + 1) + (4 * bitLen k1 + 2 * bitLen k2 + 5 +
    (6 * (bitLen b + bitLen K0 + bitLen k1) + 43)) + 2 +
  (n * (6 * wD + 4 * K0 + 2 * b + 8 + 4) + 2) + (2 * bitLen R + 2) + (n * (2 * b + 2 + 4) + 2) +
  (bitLen b + 1 + 5)

namespace Kit

variable {K : Kit} {C : ℕ} (hK : K.Spec C)
include hK

set_option maxHeartbeats 400000 in
theorem HT_recProg (B : H → List Sym) (b K0 k1 k2 wD : ℕ) (cs : List ℕ) (rA r0 : List Sym)
    (hlen : cs.length = k1 + k2) (hK0 : k1 + k2 ≤ 2 ^ K0) (hwD : ∀ c ∈ cs, bitLen c ≤ wD)
    (hrA : TermOK rA) (hc0 : B hC0 = hdrSyms [b, K0, k1, k2] ++ r0)
    (hoa : B hOA = hdrSyms cs ++ rA) :
    HT [] B K.recProg (Function.update B hOA (natSyms (reconstructChunksTree b cs) ++ rA))
      ((C + 1) * recTot b K0 k1 k2 wD cs.length (carryRun b 0 cs).2) := by
  rw [hdrSyms_four] at hc0
  have hn : k2 + k1 = cs.length := by omega
  have hA := HT_recFetchB hK B b _ hc0
  have hB := HT_recCount hK (Function.update B rB (natSyms b ++ Sym.mark :: B rB)) b K0 k1 k2 r0
    (by simp [hc0])
  have hL1 := HT_pass1 hK B b K0 wD cs rA (by omega) hwD
  have hM := HT_recMid hK (rs1 B b cs rA 0) (carryRun b 0 cs).2 (B rCR) (by simp [rs1])
  have hL2 := HT_pass2 hK B b cs rA hrA
  have hP := HT_recPost hK (rs2 B b cs rA 0) b (B rCT) (B rCT2) (B rB) (B rCR) (B rT)
    (by simp [rs2, natSyms_zero]) (by simp [rs2, natSyms_zero]) (by simp [rs2, natSyms_zero])
    (by simp [rs2, natSyms_zero]) (by simp [rs2, natSyms_zero])
  refine (HT.seq hA <| HT.seq hB <| HT.seq (HT_recInit (K := K) _) <|
    HT.seq (HT.pre_eq hL1 ?_) <| HT.seq hM <| HT.seq (HT.pre_eq hL2 ?_) hP).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = hOA
    · subst e1; simp [rs1, hoa]
    by_cases e2 : k = rCT
    · subst e2; simp [rs1, hn]
    by_cases e3 : k = rCT2
    · subst e3; simp [rs1, hn]
    by_cases e4 : k = rCR
    · subst e4; simp [rs1, carryRun, natSyms_zero]
    by_cases e5 : k = rL
    · subst e5; simp [rs1, carryRun, hdrSyms]
    by_cases e6 : k = rB
    · subst e6; simp [rs1]
    by_cases e7 : k = rT
    · subst e7; simp [rs1]
    simp [rs1, e1, e2, e3, e4, e5, e6, e7]
  · have w1 : (carryRun b 0 cs).1.drop cs.length = [] :=
      List.drop_eq_nil_of_le (by rw [length_carryRun])
    have w2 : (carryRun b 0 cs).1.take cs.length = (carryRun b 0 cs).1 :=
      List.take_of_length_le (by rw [length_carryRun])
    funext k
    by_cases e1 : k = hOA
    · subst e1; simp [rs1, rs2, w1, horner, hdrSyms]
    by_cases e2 : k = rCT
    · subst e2; simp [rs1, rs2, natSyms_zero]
    by_cases e3 : k = rL
    · subst e3; simp [rs1, rs2, w2]
    by_cases e4 : k = rB
    · subst e4; simp [rs1, rs2]
    by_cases e5 : k = rCT2
    · subst e5; simp [rs1, rs2]
    by_cases e6 : k = rT
    · subst e6; simp [rs1, rs2]
    by_cases e7 : k = rCR
    · subst e7; simp [rs1, rs2]
    simp [rs1, rs2, e1, e2, e3, e4, e5, e6, e7]
  · funext k
    by_cases e1 : k = hOA
    · subst e1; simp [rs2, horner_carryRun_zero]
    by_cases e2 : k = rL
    · subst e2; simp [rs2, hdrSyms]
    by_cases e3 : k = rB
    · subst e3; simp [rs2]
    by_cases e4 : k = rCT
    · subst e4; simp [rs2]
    by_cases e5 : k = rCT2
    · subst e5; simp [rs2]
    by_cases e6 : k = rCR
    · subst e6; simp [rs2]
    by_cases e7 : k = rT
    · subst e7; simp [rs2]
    simp [rs2, e1, e2, e3, e4, e5, e6, e7]
  · simp only [recTot]
    ring_nf
    omega

end Kit

/-- **`W9_reconstruct`** from the `W3_all` arithmetic contracts. -/
theorem W9_reconstruct_holds (h3 : W3_all) : W9_reconstruct := by
  obtain ⟨K, C, hK⟩ := exists_kit h3
  refine ⟨100 * (C + 1), fun _ => ⟨nS, K.Reg, K.recProg.mapStk eH, by norm_num [w9Scratch],
    K.finite_Reg, K.nonempty_Reg, closed_mapStk_eH K.recProg_closed, ?_⟩⟩
  intro b K0 k1 k2 wD cs σ rA r0 hlen hK0 hwD hrA hc0 hoa
  apply runs_of_HT
  rw [toH_update]
  refine (Kit.HT_recProg hK (toH σ) b K0 k1 k2 wD cs rA r0 hlen hK0 hwD hrA hc0 hoa).mono ?_
  have hR := bitLen_carry_le b K0 wD cs (by omega) hwD
  have hT : recTot b K0 k1 k2 wD cs.length (carryRun b 0 cs).2 ≤
      100 * (cs.length * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1) := by
    rw [rootHdrLen_eq]
    simp only [recTot]
    ring_nf at hR ⊢
    omega
  calc (C + 1) * recTot b K0 k1 k2 wD cs.length (carryRun b 0 cs).2
      ≤ (C + 1) * (100 * (cs.length * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1)) :=
        Nat.mul_le_mul_left _ hT
    _ = 100 * (C + 1) * (cs.length * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1) := by ring

#assert_std_axioms rootHdrLen_eq HT.pre_eq bitLen_carry_le Kit.HT_recProg W9_reconstruct_holds

end WP.W9h
