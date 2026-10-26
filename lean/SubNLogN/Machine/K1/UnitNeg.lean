/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitNegFiber
import SubNLogN.Machine.K1.UnitNegMath

/-!
# K5-neg, the contract (`K1/UnitNeg.lean`)

**Scope (honest summary).** Proves `k5Neg_holds : K5NegStmt q` for every `q`
(`SubNLogN/Machine/Contracts/Streams.lean` §5): in the shape `[np] × [q^b] × [s]` the record at
`(p, t, z)` moves to `(p, -t mod q^b, z)`; cost `C·(V + 1)`.
* `q ≥ 2`: `negProg q`. An empty input reads no counter. Otherwise the depth stack receives `b`
  tokens (`O(b)`, absorbed since `V ≥ q^b ≥ 2^b`), every fiber is negated (`runsM_negFiber`), and
  the accumulator is rewound onto the destination.
* `q ≤ 1`: then `q^b ≤ 1` and the permutation is the identity; `idProg5` copies the array.
Construction: [OAI26, §2.1, proof of Lemma 4]; paper: Lemma A.4 (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

section Loop

variable {K M : Type} [DecidableEq K]

theorem runsM_peekIte_pos {k : K} {P : KP K M} {m m' : M} {S S' : K → List Sym} {T : ℕ}
    (hc : testO isRecStart (S k).head? = true) (h : RunsM P m S m' S' T) :
    RunsM (.seq (peekO k) (.ite (fun r => testO isRecStart r.1) P Lib.skip)) m S m' S' (T + 2) := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h ((S k).head?)
  exact ⟨o', 1 + (t + 1), by omega, Eval.seq (Eval.peek _ _ _ _ _) (Eval.ite_true hc e)⟩

theorem runsM_peekIte_neg {k : K} {P : KP K M} {m : M} {S : K → List Sym}
    (hc : testO isRecStart (S k).head? = false) :
    RunsM (.seq (peekO k) (.ite (fun r => testO isRecStart r.1) P Lib.skip)) m S m S 3 := by
  intro o
  exact ⟨_, 1 + (1 + 1), le_rfl, Eval.seq (Eval.peek _ _ _ _ _)
    (Eval.ite_false hc (Lib.skip_eval _ _))⟩

end Loop

section Fibers

variable (q : ℕ) (hq : 2 ≤ q) (b s : ℕ) (hs : 1 ≤ s) (r3 : List Sym) (hr3 : TermOK r3)
  (R : List Sym) (hR : BlkTerm R) (nm : Fin 4 → List Sym) (zs xs : Fin 0 → List Sym)
  (D : List Sym) (hD : D.head? ≠ some tok) (hnm3 : nm 3 = natSyms s ++ r3)

include hq hs hr3 hR hD hnm3 in
theorem loopM_negFibers :
    ∀ (n : ℕ) (w : List (List Bool)) (sg : Fin 9 → List Sym) (m : Bool),
      w.length = n * (q ^ b * s) → sg 1 = List.replicate b tok ++ D →
      ∃ m', LoopM SRC5 isRecStart (negFiber q) m
        (mk5 (Function.update nm 0 (arrSyms w ++ R)) sg zs xs) m'
        (mk5 (Function.update nm 0 R)
          (Function.update sg 0 ((arrSyms (negOutAll (q ^ b) s w n)).reverse ++ sg 0)) zs xs)
        (110 * vol w + 2 * n + 1)
  | 0, w, sg, m, hw, _ => by
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hw0
    refine ⟨m, (LoopM.congr (LoopM.stop ?_) ?_).mono (by simp)⟩
    · rw [mk5_nm, Function.update_self, arrSyms_nil, List.nil_append]
      exact testO_recStart_of_blkTerm hR
    · refine mk5_ext ?_ ?_ rfl rfl
      · rw [arrSyms_nil, List.nil_append]
      · simp [negOutAll]
  | n + 1, w, sg, m, hw, hsg1 => by
    have hlen : q ^ b * s ≤ w.length := by
      rw [hw, Nat.succ_mul]
      omega
    have h1 := runsM_negFiber (Function.update nm 0 (arrSyms w ++ R)) zs xs s r3 q hq b hs hr3 w R
      hlen sg D hD (Function.update_self _ _ _)
      (by rw [Function.update_of_ne (by decide)]; exact hnm3) hsg1 m
    rw [Function.update_idem] at h1
    have hdl : (w.drop (q ^ b * s)).length = n * (q ^ b * s) := by
      rw [List.length_drop, hw, Nat.succ_mul]
      omega
    obtain ⟨m', ih⟩ := loopM_negFibers n (w.drop (q ^ b * s))
      (Function.update sg 0 ((arrSyms (negFib (q ^ b) s w)).reverse ++ sg 0)) false hdl
      (by rw [Function.update_of_ne (by decide)]; exact hsg1)
    have hc : testO isRecStart ((mk5 (Function.update nm 0 (arrSyms w ++ R)) sg zs xs) SRC5).head? =
        true := by
      obtain ⟨p, w', rfl⟩ : ∃ p w', w = p :: w' := by
        cases w with
        | nil =>
          have hQ : 0 < q ^ b * s := Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) hs
          simp at hw
          have : 0 < (n + 1) * (q ^ b * s) := Nat.mul_pos (Nat.succ_pos n) hQ
          omega
        | cons p w' => exact ⟨p, w', rfl⟩
      rw [mk5_nm, Function.update_self, arrSyms_cons, List.append_assoc]
      exact testO_recStart _ _
    refine ⟨m', ((LoopM.step hc h1 ih).congr ?_).mono ?_⟩
    · refine mk5_ext rfl ?_ rfl rfl
      rw [Function.update_idem, Function.update_self, negOutAll_succ, arrSyms_append,
        List.reverse_append, List.append_assoc]
    · have hv : vol w = vol (w.take (q ^ b * s)) + vol (w.drop (q ^ b * s)) := by
        rw [← vol_append, List.take_append_drop]
      omega

end Fibers

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem negMixInvAddr_id_of_le_one (Q s y : ℕ) (hQ : Q = 1) : negMixInvAddr Q s y = y := by
  subst hQ
  rw [negMixInvAddr]
  simp only [Nat.mul_one, Nat.mod_one, Nat.zero_mul, Nat.add_zero]
  exact Nat.div_add_mod' y s

theorem testO_recStart_arr (v : List (List Bool)) (R : List Sym) (hv : v ≠ []) :
    testO isRecStart (arrSyms v ++ R).head? = true := by
  obtain ⟨p, v', rfl⟩ := List.exists_cons_of_ne_nil hv
  rw [arrSyms_cons, List.append_assoc]
  exact testO_recStart _ _

theorem vol_negFib (Q s : ℕ) (hQ : 1 ≤ Q) (f : List (List Bool)) :
    vol (negFib Q s f) = vol (f.take (Q * s)) := by
  rw [negFib, vol_append, vol_revBlocks]
  have h : blkOf s f 0 = (f.take (Q * s)).take s := by
    rw [blkOf, Nat.zero_mul, List.drop_zero, List.take_take,
      Nat.min_eq_left (Nat.le_mul_of_pos_left s hQ)]
  rw [h, ← vol_append, List.take_append_drop]

theorem vol_negOutAll (Q s : ℕ) (hQ : 1 ≤ Q) :
    ∀ (n : ℕ) (w : List (List Bool)), vol (negOutAll Q s w n) = vol (w.take (n * (Q * s)))
  | 0, w => by simp [negOutAll]
  | n + 1, w => by
    rw [negOutAll_succ, vol_append, vol_negFib Q s hQ, vol_negOutAll Q s hQ n (w.drop (Q * s)),
      Nat.succ_mul, Nat.add_comm (n * (Q * s)) (Q * s), List.take_add, vol_append]

/-- **K5-neg holds** (`K5NegStmt q`, `SubNLogN/Machine/Contracts/Streams.lean` §5), for every `q`.
Construction: [OAI26, §2.1, proof of Lemma 4]; paper: Lemma A.4 (`lem:transfer-streams`). -/
theorem k5Neg_holds' (q : ℕ) : K5NegStmt q := by
  by_cases hq : 2 ≤ q
  · refine ⟨170, fun _ => ⟨E5 0 0, inferInstance, inferInstance, Option Sym × Bool, negProg q,
      inferInstance, ⟨(none, false)⟩, closed_negProg q, ?_⟩⟩
    intro np b s v rest r2 r3 S hv hR hr2 hr3 hS0 hS2 hS3
    rw [mk5_eta S] at hS0 hS2 hS3 ⊢
    set nm : Fin 4 → List Sym := fun i => S (.inl i) with hnm
    set sg : Fin 9 → List Sym := fun j => S (.inr (.inl j)) with hsg
    set zs : Fin 0 → List Sym := fun j => S (.inr (.inr (.inl j)))
    set xs : Fin 0 → List Sym := fun j => S (.inr (.inr (.inr j)))
    simp only [mk5_nm] at hS0 hS2 hS3
    refine runs_of_forall_runsM fun m => ?_
    have h1 := RunsM.push (M := Bool) ACC5 Sym.mark m (mk5 nm sg zs xs)
    rw [upd5_sg, mk5_sg] at h1
    by_cases hv0 : v = []
    · subst hv0
      have h2 := runsM_peekIte_neg (k := SRC5) (P := negMain q) (m := m)
        (S := mk5 nm (Function.update sg 0 (Sym.mark :: sg 0)) zs xs)
        (by rw [mk5_nm, hS0, arrSyms_nil, List.nil_append]; exact testO_recStart_of_blkTerm hR)
      have h3 := runsM_rwd (M := Bool) (K := L5 0 0) (src := ACC5) (dst := DST5) (by decide) [] (sg 0)
        (by simp) m (mk5 nm (Function.update sg 0 (Sym.mark :: sg 0)) zs xs) (by simp)
      refine ⟨m, RunsM.of_eq (h1.seq (h2.seq h3)) rfl rfl rfl ?_ (by simp)⟩
      simp only [upd5_sg, upd5_nm, mk5_nm, Function.update_idem, Function.update_self,
        List.reverse_nil, List.nil_append, permByInv, List.length_nil, List.range_zero,
        List.map_nil, arrSyms_nil]
      refine mk5_ext ?_ ?_ rfl rfl
      · have h0 : nm 0 = rest := by rw [hS0]; rfl
        rw [← h0]
        simp only [Function.update_eq_self]
      · simp only [Function.update_eq_self]
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
      have hu := runsM_unaryB (M := Bool) (bc := BC5) (cnt := CNT5) (tmp := TMP5) (dk := DEP5)
        (by decide) (by decide) (by decide) (by decide) (by decide) b r2 hr2 m
        (mk5 nm (Function.update sg 0 (Sym.mark :: sg 0)) zs xs) (by rw [mk5_nm]; exact hS2)
      rw [upd5_sg, mk5_sg, Function.update_of_ne (by decide)] at hu
      obtain ⟨m', hloop⟩ := loopM_negFibers q hq b s hs r3 hr3 rest hR nm zs xs
        (Sym.mark :: sg 1) (by simp [tok]) hS3 np v
        (Function.update (Function.update sg 0 (Sym.mark :: sg 0)) 1
          (List.replicate b tok ++ Sym.mark :: sg 1)) m (by rw [hv]; ring) (by simp)
      have hl := runsM_whileTop' hloop
      rw [show Function.update nm 0 (arrSyms v ++ rest) = nm by
        rw [← hS0, Function.update_eq_self]] at hl
      have h2 := runsM_peekIte_pos (k := SRC5) (P := negMain q)
        (by rw [mk5_nm, hS0]; exact testO_recStart_arr v rest hv0)
        (hu.seq (hl.seq (runsM_clearDep (M := Bool) DEP5 b (sg 1) m' _ ?_)))
      · refine ⟨m', RunsM.of_eq (h1.seq (h2.seq (runsM_rwd (M := Bool) (K := L5 0 0)
          (src := ACC5) (dst := DST5) (by decide) ((arrSyms (negOutAll (q ^ b) s v np)).reverse)
          (sg 0) (by rw [List.mem_reverse]; exact mark_not_mem_arrSyms _) m' _ ?_))) rfl rfl rfl
          ?_ ?_⟩
        · rw [upd5_sg, mk5_sg, Function.update_of_ne (by decide : (0 : Fin 9) ≠ 1),
            Function.update_self, Function.update_of_ne (by decide : (0 : Fin 9) ≠ 1),
            Function.update_self]
        · rw [negOutAll_eq (q ^ b) s np hQ1 hs v hv]
          simp only [upd5_sg, upd5_nm, mk5_nm, mk5_sg, List.reverse_reverse]
          refine mk5_ext ?_ ?_ rfl rfl
          · funext i
            fin_cases i <;> simp [Function.update_apply]
          · funext j
            fin_cases j <;> simp [Function.update_apply]
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
          have hvo : vol (negOutAll (q ^ b) s v np) = vol v := by
            rw [vol_negOutAll (q ^ b) s hQ1 np v, List.take_of_length_le (by rw [hv]; ring_nf; omega)]
          rw [List.length_reverse, ← vol, hvo]
          omega
      · simp [Function.update_apply]
  · refine ⟨10, fun _ => ⟨E5 0 0, inferInstance, inferInstance, Option Sym × Bool, idProg5,
      inferInstance, ⟨(none, false)⟩, closed_idProg5, ?_⟩⟩
    intro np b s v rest r2 r3 S hv hR hr2 hr3 hS0 hS2 hS3
    have hid : permByInv (negMixInvAddr (q ^ b) s) v = v := by
      refine permByInv_id_of _ v fun y hy => ?_
      rcases Nat.lt_or_ge q 1 with h | h
      · have hq0 : q = 0 := by omega
        subst hq0
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb
          exact negMixInvAddr_id_of_le_one _ s y (by simp)
        · rw [hv, zero_pow (by omega), Nat.mul_zero, Nat.zero_mul] at hy
          omega
      · have hq1 : q = 1 := by omega
        subst hq1
        exact negMixInvAddr_id_of_le_one _ s y (by simp)
    rw [hid]
    have h1 := runs_of_runsM_all (fun m => RunsM.push (M := Bool) (K := L5 0 0) ACC5 Sym.mark m S)
    have h2 := runs_mvArr (M := Bool) (src := SRC5) (dst := ACC5) (by decide) v rest hR
      (Function.update S ACC5 (Sym.mark :: S ACC5)) (by rw [Function.update_of_ne (by decide)]; exact hS0)
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

/-- **K5-neg holds** (deliverable; `K5NegStmt q`, Contracts/Streams.lean §5), for every `q`. Alias
of `SubNLogN.Machine.K1.SMM.k5Neg_holds'`, see there. Construction: [OAI26, §2.1, proof of Lemma 4];
paper: Lemma A.4 (`lem:transfer-streams`). -/
theorem k5Neg_holds (q : ℕ) : K5NegStmt q := SMM.k5Neg_holds' q

end SubNLogN.Machine.K1
