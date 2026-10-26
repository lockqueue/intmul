import WP.W9sp.Phases

/-!
# WP.W9sp.Main — `W9_splitPack` (R3)

`prog K = floorsP; hdrP; loopP; emitP; cleanP` over the host stacks `Loc 12 24`, transported to
`BLoc 24` by `eH` (`runs_of_HT`). Value: after `2^K0` iterations `sO` holds the reversed symbols of
`(4a_j, 4b_j)_{j < 2^K0}` (`packSyms`), the transfer puts them on `S` in order above
`symNode · symLevel`, which is `streamSyms [rootPackV …]` (`streamSyms_pack`); `OA`, `OB` end at
`A / 2^(b·2^K0) = 0` (`div_pow_eq_zero`), i.e. `rA`, `rB`. Cost: `O(C·(2^K0·(b+1) + hdr))`
(`cost_le`), with the counter amortised (`loopCost_amort`).
-/

namespace WP.W9sp

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability IntMul

variable (K : Kit)

/-- The splitPack program over the host stacks. -/
def prog : Prog H (fun _ => Sym) K.Reg :=
  (floorsP K).seq ((hdrP K).seq ((loopP K).seq ((emitP K).seq (cleanP K))))

theorem prog_closed : (prog K).Closed :=
  ⟨floorsP_closed K, hdrP_closed K, loopP_closed K, emitP_closed K, cleanP_closed K⟩

/-- The initial record. -/
def W.of (σ : H → List Sym) : W := ⟨σ hS, σ hC0, σ hOA, σ hOB, σ sB, σ sN, σ sT, σ sO⟩

theorem toB_of (σ : H → List Sym) : (W.of σ).toB σ = σ := toB_self σ

/-- Final cost constant. -/
def Cf (C : ℕ) : ℕ := 20 * C + 100

theorem cost_le (C b K0 N h bb bk LC L k1 k2 : ℕ) (hbb : bb + 1 ≤ h) (hbk : bk ≤ h)
    (hK0 : K0 + 1 ≤ N) (hLC : LC ≤ C * (2 * N + (K0 + 1)) + N * (cbody C b + C + 1) + 1)
    (hL : L ≤ N * (2 * b + 8)) :
    (1 + (1 + (1 + 1))) + ((C * (bb + 1) + ((3 * bb + 6) + (1 + (C * (K0 + bk + 1) +
      (3 * bb + 6))))) + ((C + LC) + ((1 + (1 + (3 * L + 2))) + (C * (bb + 1) + (1 + (1 + 1)))))) ≤
    Cf C * (b * (k1 + k2) + N * (b + 1) + h + 1) := by
  have hNX : N ≤ N * (b + 1) := Nat.le_mul_of_pos_right N (Nat.succ_pos b)
  have hNbX : N * b ≤ N * (b + 1) := Nat.mul_le_mul_left N (Nat.le_succ b)
  have g1 : C * (bb + 1) ≤ C * h := Nat.mul_le_mul_left C hbb
  have g2 : C * (K0 + bk + 1) ≤ C * (N * (b + 1)) + C * h := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left C (by omega)
  have g3 : C * (2 * N + (K0 + 1)) ≤ 3 * (C * (N * (b + 1))) := by
    rw [← Nat.mul_left_comm]
    exact Nat.mul_le_mul_left C (by omega)
  have e4 : N * (cbody C b + C + 1) = 4 * (C * (N * b)) + 9 * (C * N) + 6 * (N * b) + 25 * N := by
    unfold cbody
    ring
  have g5 : C * (N * b) ≤ C * (N * (b + 1)) := Nat.mul_le_mul_left C hNbX
  have g6 : C * N ≤ C * (N * (b + 1)) := Nat.mul_le_mul_left C hNX
  have e7 : N * (2 * b + 8) = 2 * (N * b) + 8 * N := by ring
  have e8 : Cf C * (b * (k1 + k2) + N * (b + 1) + h + 1) = 20 * (C * (b * (k1 + k2))) +
      20 * (C * (N * (b + 1))) + 20 * (C * h) + 20 * C + 100 * (b * (k1 + k2)) +
      100 * (N * (b + 1)) + 100 * h + 100 := by
    unfold Cf
    ring
  rw [e8]
  omega

theorem rootHdrLen_eq (b K0 k1 k2 : ℕ) :
    rootHdrLen b K0 k1 k2 = bitLen b + 1 + (bitLen K0 + 1 + (bitLen k1 + 1 + (bitLen k2 + 1))) := by
  simp only [rootHdrLen, hdrSyms, List.flatMap_cons, List.flatMap_nil, List.length_append,
    length_natSyms, List.length_singleton, List.length_nil]

/-- **`W9_splitPack` holds**, from the frozen W3 contracts (`W3_all`; used: copy, drop, splitAt,
shlConst 2, shlVar, isZero, dec, and the decrement amortisation). -/
theorem W9_splitPack_holds (h3 : W3_all) : W9_splitPack := by
  obtain ⟨K, C, hK⟩ := exists_kit h3
  refine ⟨Cf C, fun _ => ⟨nS, K.Reg, (prog K).mapStk eH, by decide, K.finite_Reg, K.nonempty_Reg,
    closed_mapStk_eH (prog_closed K), ?_⟩⟩
  intro b K0 k1 k2 A B σ rA rB r0 hA hB hk hrA hrB hxA hxB hxC
  have hc00 : toH σ hC0 =
      natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: (hdrSyms [k1, k2] ++ r0)) := by
    rw [toH_C0, hxC, hdrSyms_four]
  have hoa0 : toH σ hOA = natSyms A ++ rA := by rw [toH_OA, hxA]
  have hob0 : toH σ hOB = natSyms B ++ rB := by rw [toH_OB, hxB]
  have hk1 : k1 ≤ 2 ^ K0 := by omega
  have hk2 : k2 ≤ 2 ^ K0 := by omega
  have hchain := HT.seq (HT.floors K (toH σ) (W.of (toH σ)))
    (HT.seq ((HT.hdr K hK (toH σ) _ b K0 (hdrSyms [k1, k2] ++ r0) (by exact hc00)
        (by exact TermOK.cons rfl _) (by exact TermOK.cons rfl _)).of_eq
        (by
          refine congrArg (W.toB (toH σ)) ?_
          simp only [W.of, Wl, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.one_mul,
            packSyms_zero, List.reverse_nil, List.nil_append, hc00, hoa0, hob0]) le_rfl)
    (HT.seq (HT.mainLoop K hK (toH σ) b (2 ^ K0) A B rA rB hrA hrB)
    (HT.seq (HT.emit K (toH σ) _ ((packSyms b A B (2 ^ K0)).reverse) (toH σ sO)
        (mark_not_mem_packSyms b A B (2 ^ K0)) (by simp [Wl]))
      (HT.cleanup K hK (toH σ) _ b (toH σ sB) (toH σ sN) (toH σ sT) (by rfl)
        (by simp [Wl, natSyms_zero_sp]) (by rfl)))))
  rw [toB_of] at hchain
  have hLC := loopCost_amort hK.amort C C (cbody C b) (fun _ => cbody C b) (2 ^ K0)
    (fun _ _ => le_rfl)
  rw [bitLen_two_pow] at hLC
  beta_reduce at hLC
  have hL : ((packSyms b A B (2 ^ K0)).reverse).length ≤ 2 ^ K0 * (2 * b + 8) := by
    rw [List.length_reverse]
    exact length_packSyms_le b A B (2 ^ K0)
  have hh := rootHdrLen_eq b K0 k1 k2
  refine runs_of_HT (hchain.of_eq ?_ (cost_le C b K0 (2 ^ K0) (rootHdrLen b K0 k1 k2) (bitLen b)
    (bitLen K0) _ _ k1 k2 (by omega) (by omega) Nat.lt_two_pow_self hLC hL))
  rw [toH_update, toH_update, toH_update, finOf_S, finOf_OA, finOf_OB]
  conv_rhs => rw [← toB_of (toH σ)]
  rw [upd_OA, upd_OB, upd_S]
  refine congrArg (W.toB (toH σ)) ?_
  simp only [W.of, Wl, Nat.sub_zero, div_pow_eq_zero hA hk1, div_pow_eq_zero hB hk2,
    natSyms_zero_sp, List.nil_append, List.reverse_reverse, streamSyms_pack hA hB, toH_S]

#assert_std_axioms prog_closed toB_of cost_le rootHdrLen_eq W9_splitPack_holds

end WP.W9sp
