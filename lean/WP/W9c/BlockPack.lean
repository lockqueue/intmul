import WP.W9c.BlockPackAll

/-!
# WP.W9c.BlockPack — piece A of the W9 spread kernel: `W9c_blockPack`

**Main theorem** `w9c_blockPack_holds`: the frozen contract `W9c_blockPack` (WP/W9c/Iface.lean),
from the W3 contracts that are not proved in the frozen contracts package, taken as hypotheses
(discharged at assembly): `W3_dropNat`, `W3_addNat`, `W3_subNat`, `W3_shlVar`, `W3_shrVar`,
`W3_shrConst`, `W3_splitAt`, `W3_concatAt`, `W3_subInt`, and the pure `W3_dec_amortised`. Copy,
increment, decrement and compare come from the proved `w3_copyNat`, `w3_incNat`, `w3_decNat`,
`w3_cmpNat`.

The program `bpProg` (`WP.W9c.BlockPackFin`) reads `n = min(W, |v|)` numbers, quantizes each in
place (`gQuant_eq`), routes its magnitude to the positive or negative unsigned carry chain at radix
`2^k` (chunks pushed, carries kept), rebuilds both chain values by a Horner pass with
`W3_concatAt` (cost independent of the accumulator), and pushes their difference with one
`W3_subInt`. Scratch: 8 stacks. Cost: `costBP_le` turns the composed cost into
`C·(n·(B + k + p_in + q + 1) + bitLen W + 1)` (counter decrements amortised by
`W3_dec_amortised`).
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability IntMul

theorem sum_range_split (n A C : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map fun i => A + C * g i).sum = n * A + C * ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- The arithmetic of the cost bound, over plain variables. -/
theorem cost_arith (C U E n w a b Sm Sf : ℕ) (hSf : Sf = n * (40 * (C * U) + 43) + C * Sm)
    (hdec : Sm ≤ 2 * n + w) (hPP : a ≤ n * E) (hPN : b ≤ n * E) (hU : U ≤ 4 * E) (hU4 : 4 ≤ U) :
    (C * (w + 1) + 7) + ((2 + (Sf + 1)) + ((C * (w + 1) + 1) + ((n * (C * U + 3) + 3) +
      ((n * (C * U + 3) + 3) + (C * (a + b + 1) + C * (a + 1) + C * (b + 1) + 9))))) ≤
      (300 * C + 300) * (n * E + w + 1) := by
  have f1 : n * (C * U) ≤ 4 * (C * (n * E)) :=
    calc n * (C * U) ≤ n * (C * (4 * E)) := Nat.mul_le_mul_left n (Nat.mul_le_mul_left C hU)
      _ = 4 * (C * (n * E)) := by ring
  have f2 : n ≤ n * E := Nat.le_mul_of_pos_right n (by omega)
  have f3 : C * n ≤ C * (n * E) := Nat.mul_le_mul_left C f2
  have f4 : C * a ≤ C * (n * E) := Nat.mul_le_mul_left C hPP
  have f5 : C * b ≤ C * (n * E) := Nat.mul_le_mul_left C hPN
  have f6 : C * Sm ≤ C * (2 * n + w) := Nat.mul_le_mul_left C hdec
  have z1 := Nat.zero_le (C * (n * E))
  have z2 := Nat.zero_le (n * E)
  have z3 := Nat.zero_le (C * w)
  subst hSf
  linarith

/-- **Cost bound** for the composed cost of `bpProg`. -/
theorem costBP_le (C B k p_in q W n PP PN : ℕ)
    (hdec : ((List.range n).map fun i => zerosLead (encodeNat (W - i)) + 1).sum ≤
      2 * n + bitLen W)
    (hPP : bitLen PP ≤ n * (B + k + p_in + q + 1))
    (hPN : bitLen PN ≤ n * (B + k + p_in + q + 1)) :
    costBP C B k p_in q W n PP PN ≤
      (300 * C + 300) * (n * (B + k + p_in + q + 1) + bitLen W + 1) := by
  have hfun : (fun i => 40 * (C * (2 * (B + k + p_in + q + 2))) + 40 +
      C * (zerosLead (encodeNat (W - i)) + 1) + 2 + 1) =
      (fun i => (40 * (C * (2 * (B + k + p_in + q + 2))) + 43) +
        C * (zerosLead (encodeNat (W - i)) + 1)) := by
    funext i
    omega
  have e1 := (congrArg (fun f => ((List.range n).map f).sum) hfun).trans
    (sum_range_split n _ C (fun i => zerosLead (encodeNat (W - i)) + 1))
  unfold costBP
  exact cost_arith C (2 * (B + k + p_in + q + 2)) (B + k + p_in + q + 1) n (bitLen W)
    (bitLen PP) (bitLen PN) _ _ e1 hdec hPP hPN (by omega) (by omega)

theorem bitLen_pack_le (k p_in q W B : ℕ) (v : List ℤ) (f : ℤ → ℕ) (hk1 : 1 ≤ k)
    (hf : ∀ y ∈ v, f y < 2 ^ (B + q)) :
    bitLen (packNat (2 ^ k) ((v.take (v.take W).length).map f)) ≤
      (v.take W).length * (B + k + p_in + q + 1) := by
  have hnv : (v.take W).length ≤ v.length := by rw [List.length_take]; exact min_le_right _ _
  have hlen : ((v.take (v.take W).length).map f).length = (v.take W).length := by
    rw [List.length_map, List.length_take, Nat.min_eq_left hnv]
  have h := packNat_lt k (B + q) hk1 ((v.take (v.take W).length).map f)
    (mem_map_take_lt (i := (v.take W).length) hf)
  rw [hlen] at h
  have h2 := bitLen_le_of_lt h
  have h3 : (v.take W).length * (k + (B + q)) ≤ (v.take W).length * (B + k + p_in + q + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Piece A of the W9 spread kernel.** -/
theorem w9c_blockPack_holds (hdrop : W3_dropNat) (hadd : W3_addNat) (hsub : W3_subNat)
    (hshl : W3_shlVar) (hshr : W3_shrVar) (hshr1 : W3_shrConst) (hsplit : W3_splitAt)
    (hcat : W3_concatAt) (hsubI : W3_subInt) (hdecA : W3_dec_amortised) : W9c_blockPack := by
  obtain ⟨c1, h1⟩ := exists_inst w3_copyNat
  obtain ⟨I1, s1⟩ := h1 ()
  obtain ⟨c2, h2⟩ := exists_inst hdrop
  obtain ⟨I2, s2⟩ := h2 ()
  obtain ⟨c3, h3⟩ := exists_inst w3_incNat
  obtain ⟨I3, s3⟩ := h3 ()
  obtain ⟨c4, h4⟩ := exists_inst w3_decNat
  obtain ⟨I4, s4⟩ := h4 ()
  obtain ⟨c5, h5⟩ := exists_inst w3_cmpNat
  obtain ⟨I5, s5⟩ := h5 ()
  obtain ⟨c6, h6⟩ := exists_inst hadd
  obtain ⟨I6, s6⟩ := h6 ()
  obtain ⟨c7, h7⟩ := exists_inst hsub
  obtain ⟨I7, s7⟩ := h7 ()
  obtain ⟨c8, h8⟩ := exists_inst hshl
  obtain ⟨I8, s8⟩ := h8 ()
  obtain ⟨c9, h9⟩ := exists_inst hshr
  obtain ⟨I9, s9⟩ := h9 ()
  obtain ⟨c10, h10⟩ := exists_inst hshr1
  obtain ⟨I10, s10⟩ := h10 1
  obtain ⟨c11, h11⟩ := exists_inst hsplit
  obtain ⟨I11, s11⟩ := h11 ()
  obtain ⟨c12, h12⟩ := exists_inst hcat
  obtain ⟨I12, s12⟩ := h12 ()
  obtain ⟨c13, h13⟩ := exists_inst hsubI
  obtain ⟨I13, s13⟩ := h13 ()
  obtain ⟨C0, hC0⟩ : ∃ C0, C0 = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 +
      c13 := ⟨_, rfl⟩
  let K : Kit := ⟨I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13⟩
  have hK : K.OK C0 :=
    { copy := SpecCopy.mono (by omega) s1
      drop := SpecDrop.mono (by omega) s2
      inc := SpecInc.mono (by omega) s3
      dec := SpecDec.mono (by omega) s4
      cmp := SpecCmpNat.mono (by omega) s5
      add := SpecAdd.mono (by omega) s6
      sub := SpecSub.mono (by omega) s7
      shl := SpecShlVar.mono (by omega) s8
      shr := SpecShrVar.mono (by omega) s9
      shr1 := SpecShrConst.mono (by omega) s10
      split := SpecSplit.mono (by omega) s11
      cat := SpecCat.mono (by omega) s12
      subI := SpecSubInt.mono (by omega) s13 }
  refine ⟨300 * C0 + 300, fun _ => ⟨8, K.Reg, fun _ => (), bpProg K, by norm_num, K.finite,
    K.nonempty, bpProg_closed K, ?_⟩⟩
  intro k p_in q W B v rx rk ra rb rW S hk1 hvB hrx hrk hra hrb hrW hS0 hS1 hS2 hS3 hS4
  have hS := HS.of_fun S
  rw [hS, HS.update_eq_set, HS.update_eq_set]
  refine HT.runs ((ht_bp hK _ k p_in q W B v rx rk ra rb rW hk1 hvB hrx hrk hra hrb hrW hS0 hS1
    hS2 hS3 hS4).mono ?_)
  exact costBP_le C0 B k p_in q W _ _ _ (hdecA W _ (List.length_take_le W v))
    (bitLen_pack_le k p_in q W B v _ hk1 (aP_lt p_in q B v hvB))
    (bitLen_pack_le k p_in q W B v _ hk1 (aN_lt p_in q B v hvB))

#assert_std_axioms sum_range_split cost_arith costBP_le bitLen_pack_le w9c_blockPack_holds

end WP.W9c.BlockPack
