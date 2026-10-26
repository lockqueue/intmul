/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulFib

/-!
# K5-unit, the fiber loop and the setup (`K1/UnitMulLoop.lean`)

**Scope (honest summary).** Proved (no contract here):
* `vol_unitFib`, `vol_unitOutAll`: the output keeps the volume;
* `loopM_fibU`: all `np` fibers (`unitOutAll`), cost `(230 + 12·n)·vol + 2·np + 1`;
* `runsM_setupU`: `b` depth tokens (countdown of the counter `b`), the register gets
  `(q^b mod a, q^b mod d, 0, 0)`.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem vol_unitFib (Q s a d : ℕ) [NeZero a] [NeZero d] (hca : Nat.Coprime Q a)
    (hcd : Nat.Coprime Q d) (w : List (List Bool)) :
    vol (unitFib Q s a d w) = vol (w.take (Q * s)) := by
  have hfbl : ((List.range Q).map (blkOf s w)).length = Q := by simp
  rw [← unitFib_eq Q s a d hcd w, vol_catL_distI hcd _ (length_mulOut _ _ _),
    vol_mulOut hca _ hfbl, take_mul_flatMap w s Q, List.flatMap_def]
  rfl

theorem vol_unitOutAll (Q s a d : ℕ) [NeZero a] [NeZero d] (hca : Nat.Coprime Q a)
    (hcd : Nat.Coprime Q d) :
    ∀ (np : ℕ) (w : List (List Bool)), vol (unitOutAll Q s a d w np) = vol (w.take (np * (Q * s)))
  | 0, w => by simp [unitOutAll]
  | np + 1, w => by
    rw [unitOutAll_succ, vol_append, vol_unitFib Q s a d hca hcd,
      vol_unitOutAll Q s a d hca hcd np (w.drop (Q * s)), Nat.succ_mul,
      Nat.add_comm (np * (Q * s)) (Q * s), List.take_add, vol_append]

section Loop

variable {n a d : ℕ}

theorem loopM_fibU [NeZero a] [NeZero d] (ha : a ≤ n) (hd : d ≤ n) (q : ℕ) (hq : 2 ≤ q)
    (b s : ℕ) (hs : 1 ≤ s) (hca : Nat.Coprime (q ^ b) a) (hcd : Nat.Coprime (q ^ b) d)
    (r3 : List Sym) (hr3 : TermOK r3) (R : List Sym) (hR : BlkTerm R) (nm : Fin 4 → List Sym)
    (zF xF : ℕ → List Sym) (D : List Sym) (hD : D.head? ≠ some tok)
    (hnm3 : nm 3 = natSyms s ++ r3) :
    ∀ (np : ℕ) (w : List (List Bool)) (sg : Fin 9 → List Sym) (u t : ℕ),
      w.length = np * (q ^ b * s) → sg 1 = List.replicate b tok ++ D →
      ∃ m', LoopM SRC5 isRecStart (fibU q n a d) (regU a d (q ^ b) u t)
        (mkF (Function.update nm 0 (arrSyms w ++ R)) sg zF xF) m'
        (mkF (Function.update nm 0 R)
          (Function.update sg 0 ((arrSyms (unitOutAll (q ^ b) s a d w np)).reverse ++ sg 0)) zF xF)
        ((230 + 12 * n) * vol w + 2 * np + 1)
  | 0, w, sg, u, t, hw, _ => by
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hw0
    refine ⟨regU a d (q ^ b) u t, (LoopM.congr (LoopM.stop ?_) ?_).mono (by simp)⟩
    · rw [mkF_nm, Function.update_self, arrSyms_nil, List.nil_append]
      exact testO_recStart_of_blkTerm hR
    · refine mkF_ext ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      · rw [arrSyms_nil, List.nil_append]
      · simp [unitOutAll]
  | np + 1, w, sg, u, t, hw, hsg1 => by
    have hlen : q ^ b * s ≤ w.length := by
      rw [hw, Nat.succ_mul]
      omega
    have h1 := runsM_fibU ha hd q hq b hca hcd (Function.update nm 0 (arrSyms w ++ R)) sg zF xF s
      hs w R r3 D hD hr3 hlen (Function.update_self _ _ _)
      (by rw [Function.update_of_ne (by decide)]; exact hnm3) hsg1 u t
    rw [Function.update_idem] at h1
    have hdl : (w.drop (q ^ b * s)).length = np * (q ^ b * s) := by
      rw [List.length_drop, hw, Nat.succ_mul]
      omega
    obtain ⟨m', ih⟩ := loopM_fibU ha hd q hq b s hs hca hcd r3 hr3 R hR nm zF xF D hD hnm3 np
      (w.drop (q ^ b * s))
      (Function.update sg 0 ((arrSyms (unitFib (q ^ b) s a d w)).reverse ++ sg 0)) 0 (q ^ b) hdl
      (by rw [Function.update_of_ne (by decide)]; exact hsg1)
    have hc : testO isRecStart ((mkF (n := n) (Function.update nm 0 (arrSyms w ++ R)) sg zF xF)
        SRC5).head? = true := by
      obtain ⟨p, w', rfl⟩ : ∃ p w', w = p :: w' := by
        cases w with
        | nil =>
          have hQ : 0 < q ^ b * s := Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) hs
          simp at hw
          have : 0 < (np + 1) * (q ^ b * s) := Nat.mul_pos (Nat.succ_pos np) hQ
          omega
        | cons p w' => exact ⟨p, w', rfl⟩
      rw [mkF_nm, Function.update_self, arrSyms_cons, List.append_assoc]
      exact testO_recStart _ _
    refine ⟨m', ((LoopM.step hc h1 ih).congr ?_).mono ?_⟩
    · refine mkF_ext rfl ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      rw [Function.update_idem, Function.update_self, unitOutAll_succ, arrSyms_append,
        List.reverse_append, List.append_assoc]
    · have hv : vol w = vol (w.take (q ^ b * s)) + vol (w.drop (q ^ b * s)) := by
        rw [← vol_append, List.take_append_drop]
      have e : (230 + 12 * n) * vol w = (230 + 12 * n) * vol (w.take (q ^ b * s)) +
          (230 + 12 * n) * vol (w.drop (q ^ b * s)) := by rw [hv, Nat.mul_add]
      omega

theorem runsM_setupU (q b : ℕ) (Rb : List Sym) (hRb : TermOK Rb) (m : MU a d)
    (S : L5 n n → List Sym) (hb : S BC5 = natSyms b ++ Rb) :
    RunsM (setupU q n a d) m S (regU a d (q ^ b) 0 0)
      (Function.update S DEP5 (List.replicate b tok ++ Sym.mark :: S DEP5))
      (incSeqCost 6 8 b + 4 * b + 7 * bitLen b + 14) := by
  have h0 := RunsM.load (K := L5 n n) (initf (a := a) (d := d)) m S
  rw [initf_eq q] at h0
  have h1 := RunsM.push (M := MU a d) DEP5 Sym.mark (regU a d (q ^ 0) 0 0) S
  set St : ℕ → L5 n n → List Sym := fun i =>
    Function.update S DEP5 (List.replicate i tok ++ Sym.mark :: S DEP5) with hSt
  have key := runsM_cdMove (M := MU a d) (nm_ne_sg 2 2) (nm_ne_sg 2 3) (sg_ne_sg (by decide))
    (.seq (lift (Lib.pushC DEP5 tok)) (ldU (mulQf q))) b Rb (S CNT5) hRb
    (fun i => regU a d (q ^ i) 0 0) St (fun _ => 2)
    (by rw [hSt]; simp only []; rw [Function.update_of_ne (nm_ne_sg 2 1)]; exact hb)
    (by rw [hSt]; simp only []; rw [Function.update_of_ne (sg_ne_sg (by decide))])
    (by rw [hSt]; simp only []; rw [Function.update_of_ne (sg_ne_sg (by decide))])
    ?_
  · have e0 : St 0 = Function.update S DEP5 (Sym.mark :: S DEP5) := by rw [hSt]; simp
    rw [e0] at key
    refine RunsM.of_eq (h0.seq (h1.seq key)) rfl rfl rfl (by rw [hSt]) ?_
    rw [csum_const]
    omega
  · intro i _ X
    have h := (RunsM.push (M := MU a d) DEP5 tok (regU a d (q ^ i) 0 0)
      (Function.update (St i) CNT5 X)).seq
      (RunsM.load (K := L5 n n) (mulQf (a := a) (d := d) q) (regU a d (q ^ i) 0 0) _)
    refine RunsM.of_eq h rfl rfl (mulQf_regU q i) ?_ le_rfl
    rw [hSt]
    simp only []
    funext k
    simp only [Function.update_apply, List.replicate_succ]
    split_ifs <;> simp_all

end Loop

end SubNLogN.Machine.K1.SMM
