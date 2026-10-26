/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulLoop
import SubNLogN.Machine.K1.UnitNeg

/-!
# K5-unit, the contract (`K1/UnitMul.lean`)

**Scope (honest summary).** Proves `k5UnitMulMix_holds : K5UnitMulMixStmt q a d` for every
`q a d` (`SubNLogN/Machine/Contracts/Streams.lean` §5): if `a` and `d` are coprime to `q`, then in
the shape `[np] × [q^b] × [s]` the record at `(p, t, z)` moves to `(p, a·t·d⁻¹ mod q^b, z)`
(`unitMixInvAddr`); cost `C·(V + 1)` with `C = 300 + 12·max a d` for `q ≥ 2` and `C = 10` for
`q ≤ 1`.
* `q ≥ 2`: `mulProg q (max a d) a d`. An empty input reads no counter. Otherwise the setup pushes
  `b` depth tokens and computes `q^b mod a`, `q^b mod d` (`O(b)`, absorbed since
  `V ≥ q^b ≥ 2^b`); every fiber is transformed (`runsM_fibU`: pass A multiplies by `a` by
  residue classes, pass D divides by `d`); the accumulator is rewound onto the destination.
* `q ≤ 1`: then `q^b ≤ 1` and the permutation is the identity; `idProg5` copies the array.
No hypothesis beyond the contract's (`Nat.Coprime a q`, `Nat.Coprime d q`) is used.
Construction: [OAI26, §2.1, proof of Lemma 4];
paper: Fact 3.3(4) (`fact:oai-streams`) and Lemma A.4 (`lem:transfer-streams`).
Implementation note: the depth recursion `recProg` uses `Prog.fix`/`recur` (unary depth `b`);
all stack families and registers are indexed by the compile-time `q, a, d` only.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem unitMixInvAddr_id (Q s a d y : ℕ) (hQ : Q = 1) : unitMixInvAddr Q s a d y = y := by
  subst hQ
  rw [unitMixInvAddr]
  simp only [Nat.mul_one, Nat.mod_one, Nat.zero_mul, Nat.add_zero]
  exact Nat.div_add_mod' y s

/-- **K5-unit holds** (`K5UnitMulMixStmt q a d`, `SubNLogN/Machine/Contracts/Streams.lean` §5),
for every `q a d`. Construction: [OAI26, §2.1, proof of Lemma 4]; paper:
Lemma A.4 (`lem:transfer-streams`). -/
theorem k5UnitMulMix_holds' (q a d : ℕ) : K5UnitMulMixStmt q a d := by
  intro hca hcd
  by_cases hq : 2 ≤ q
  · have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hca
      omega
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hcd
      omega
    have : NeZero a := ⟨ha0⟩
    have : NeZero d := ⟨hd0⟩
    have ha : a ≤ max a d := le_max_left a d
    have hd : d ≤ max a d := le_max_right a d
    refine ⟨300 + 12 * max a d, fun _ => ⟨E5 (max a d) (max a d), inferInstance, inferInstance,
      Option Sym × MU a d, mulProg q (max a d) a d, inferInstance, ⟨(none, 0)⟩,
      closed_mulProg q, ?_⟩⟩
    intro np b s v rest r2 r3 S hv hR hr2 hr3 hS0 hS2 hS3
    have hcaQ : Nat.Coprime (q ^ b) a := (Nat.Coprime.pow_right b hca).symm
    have hcdQ : Nat.Coprime (q ^ b) d := (Nat.Coprime.pow_right b hcd).symm
    rw [mk5_eta S] at hS0 hS2 hS3 ⊢
    set nm : Fin 4 → List Sym := fun i => S (.inl i) with hnm
    set sg : Fin 9 → List Sym := fun j => S (.inr (.inl j)) with hsg
    set zs : Fin (max a d) → List Sym := fun j => S (.inr (.inr (.inl j)))
    set xs : Fin (max a d) → List Sym := fun j => S (.inr (.inr (.inr j)))
    simp only [mk5_nm] at hS0 hS2 hS3
    obtain ⟨zF, hzF⟩ : ∃ zF : ℕ → List Sym, (fun i : Fin (max a d) => zF i.val) = zs :=
      ⟨fun j => if h : j < max a d then zs ⟨j, h⟩ else [], funext fun i => dif_pos i.isLt⟩
    obtain ⟨xF, hxF⟩ : ∃ xF : ℕ → List Sym, (fun i : Fin (max a d) => xF i.val) = xs :=
      ⟨fun j => if h : j < max a d then xs ⟨j, h⟩ else [], funext fun i => dif_pos i.isLt⟩
    have hmk : mk5 nm sg zs xs = mkF (n := max a d) nm sg zF xF := by rw [← hzF, ← hxF]
    rw [hmk]
    refine runs_of_forall_runsM fun m => ?_
    have h1 := RunsM.push (M := MU a d) ACC5 Sym.mark m (mkF (n := max a d) nm sg zF xF)
    rw [mkF_sg, updF_sg] at h1
    by_cases hv0 : v = []
    · subst hv0
      have h2 := runsM_peekIte_neg (k := SRC5) (P := mainU q (max a d) a d) (m := m)
        (S := mkF (n := max a d) nm (Function.update sg 0 (Sym.mark :: sg 0)) zF xF)
        (by rw [mkF_nm, hS0, arrSyms_nil, List.nil_append]; exact testO_recStart_of_blkTerm hR)
      have h3 := runsM_rwd (M := MU a d) (K := L5 (max a d) (max a d)) (src := ACC5)
        (dst := DST5) (Ne.symm (nm_ne_sg 1 0)) [] (sg 0) (by simp) m
        (mkF (n := max a d) nm (Function.update sg 0 (Sym.mark :: sg 0)) zF xF)
        (by rw [mkF_sg, Function.update_self]; rfl)
      refine ⟨m, RunsM.of_eq (h1.seq (h2.seq h3)) rfl rfl rfl ?_ (by simp; omega)⟩
      have h0 : nm 0 = rest := by rw [hS0]; rfl
      simp only [mkF_nm, updF_sg, updF_nm]
      refine mkF_ext ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      · funext i
        fin_cases i <;> simp [h0, permByInv, arrSyms_nil]
      · funext j
        fin_cases j <;> simp
    · have hlen : 0 < v.length := List.length_pos_iff.mpr hv0
      have hs : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · rw [hv, h, Nat.mul_zero] at hlen; omega
        · exact h
      have hnp : 1 ≤ np := by
        rcases Nat.eq_zero_or_pos np with h | h
        · rw [hv, h, Nat.zero_mul, Nat.zero_mul] at hlen; omega
        · exact h
      have hQ1 : 1 ≤ q ^ b := Nat.one_le_pow _ _ (by omega)
      have hu := runsM_setupU (n := max a d) (a := a) (d := d) q b r2 hr2 m
        (mkF nm (Function.update sg 0 (Sym.mark :: sg 0)) zF xF) (by rw [mkF_nm]; exact hS2)
      rw [mkF_sg, updF_sg, Function.update_of_ne (by decide)] at hu
      obtain ⟨m', hloop⟩ := loopM_fibU ha hd q hq b s hs hcaQ hcdQ r3 hr3 rest hR nm zF xF
        (Sym.mark :: sg 1) (by simp [tok]) hS3 np v
        (Function.update (Function.update sg 0 (Sym.mark :: sg 0)) 1
          (List.replicate b tok ++ Sym.mark :: sg 1)) 0 0 (by rw [hv]; ring) (by simp)
      have hl := runsM_whileTop' hloop
      rw [show Function.update nm 0 (arrSyms v ++ rest) = nm by
        rw [← hS0, Function.update_eq_self]] at hl
      have h2 := runsM_peekIte_pos (k := SRC5) (P := mainU q (max a d) a d)
        (by rw [mkF_nm, hS0]; exact testO_recStart_arr v rest hv0)
        (hu.seq (hl.seq (runsM_clearDep (M := MU a d) DEP5 b (sg 1) m' _ ?_)))
      · refine ⟨m', RunsM.of_eq (h1.seq (h2.seq (runsM_rwd (M := MU a d)
          (K := L5 (max a d) (max a d)) (src := ACC5) (dst := DST5) (Ne.symm (nm_ne_sg 1 0))
          ((arrSyms (unitOutAll (q ^ b) s a d v np)).reverse) (sg 0)
          (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms _) m' _ ?_))) rfl rfl rfl ?_ ?_⟩
        · rw [updF_sg, mkF_sg, Function.update_of_ne (by decide : (0 : Fin 9) ≠ 1),
            Function.update_self, Function.update_of_ne (by decide : (0 : Fin 9) ≠ 1),
            Function.update_self]
        · rw [unitOutAll_eq (q ^ b) s a d np hQ1 v hv]
          simp only [updF_sg, updF_nm, mkF_nm, List.reverse_reverse]
          refine mkF_ext ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
          · funext i
            fin_cases i <;> simp
          · funext j
            fin_cases j <;> simp
        · have hV : np * q ^ b * s ≤ vol v := by rw [← hv]; exact length_le_vol v
          have hb2 : b < 2 ^ b := Nat.lt_two_pow_self
          have hbq : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
          have hQs : q ^ b ≤ np * q ^ b * s := by
            calc q ^ b = 1 * q ^ b * 1 := by ring
              _ ≤ np * q ^ b * s := Nat.mul_le_mul (Nat.mul_le_mul_right _ hnp) hs
          have hnpV : np ≤ np * q ^ b * s := by
            calc np = np * 1 * 1 := by ring
              _ ≤ np * q ^ b * s := Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ1) hs
          have hi := incSeqCost_le 6 8 b
          have hbl := bitLen_le_self b
          have hvo : vol (unitOutAll (q ^ b) s a d v np) = vol v := by
            rw [vol_unitOutAll (q ^ b) s a d hcaQ hcdQ np v,
              List.take_of_length_le (by rw [hv]; ring_nf; omega)]
          have e1 : (300 + 12 * max a d) * (vol v + 1) =
              300 * vol v + 300 + 12 * (max a d * vol v) + 12 * max a d := by ring
          have e2 : (230 + 12 * max a d) * vol v = 230 * vol v + 12 * (max a d * vol v) := by
            ring
          rw [List.length_reverse, ← vol, hvo]
          omega
      · rw [mkF_sg, Function.update_of_ne (by decide), Function.update_self]
  · refine ⟨10, fun _ => ⟨E5 0 0, inferInstance, inferInstance, Option Sym × Bool, idProg5,
      inferInstance, ⟨(none, false)⟩, closed_idProg5, ?_⟩⟩
    intro np b s v rest r2 r3 S hv hR hr2 hr3 hS0 hS2 hS3
    have hid : permByInv (unitMixInvAddr (q ^ b) s a d) v = v := by
      refine permByInv_id_of _ v fun y hy => ?_
      rcases Nat.lt_or_ge q 1 with h | h
      · have hq0 : q = 0 := by omega
        subst hq0
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb
          exact unitMixInvAddr_id _ s a d y (by simp)
        · rw [hv, zero_pow (by omega), Nat.mul_zero, Nat.zero_mul] at hy
          omega
      · have hq1 : q = 1 := by omega
        subst hq1
        exact unitMixInvAddr_id _ s a d y (by simp)
    rw [hid]
    have h1 := runs_of_runsM_all (fun m => RunsM.push (M := Bool) (K := L5 0 0) ACC5 Sym.mark m S)
    have h2 := runs_mvArr (M := Bool) (src := SRC5) (dst := ACC5) (by decide) v rest hR
      (Function.update S ACC5 (Sym.mark :: S ACC5))
      (by rw [Function.update_of_ne (by decide)]; exact hS0)
    have h3 := runs_of_runsM_all (fun m => runsM_rwd (M := Bool) (src := ACC5) (dst := DST5)
      (by decide) (arrSyms v).reverse (S ACC5)
      (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms v) m
      (Function.update (Function.update (Function.update S ACC5 (Sym.mark :: S ACC5)) SRC5 rest)
        ACC5 ((arrSyms v).reverse ++ Function.update S ACC5 (Sym.mark :: S ACC5) ACC5))
      (by simp))
    refine runs_of_eq (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 h3)) rfl ?_ ?_
    · funext k
      simp only [Function.update_apply, List.reverse_reverse]
      split_ifs <;> simp_all
    · rw [List.length_reverse, ← vol]
      omega

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1

/-- **K5-unit holds** (deliverable; `K5UnitMulMixStmt q a d`, Contracts/Streams.lean §5), for
every `q a d`. Alias of `SubNLogN.Machine.K1.SMM.k5UnitMulMix_holds'`, see there. Construction
[OAI26, §2.1, proof of Lemma 4]; paper: Lemma A.4 (`lem:transfer-streams`). -/
theorem k5UnitMulMix_holds (q a d : ℕ) : K5UnitMulMixStmt q a d := SMM.k5UnitMulMix_holds' q a d

end SubNLogN.Machine.K1
