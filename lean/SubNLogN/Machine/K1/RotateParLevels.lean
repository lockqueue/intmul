/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateParFiber

/-!
# K1, K4-ctl-par (`K1/RotateParLevels.lean`): the nested loops, routine with parameters

**Scope (honest summary).** The `Runs` rules of the four loop levels of the controlled rotation
(`runs_lvN2Q`, `runs_lvC2Q`, `runs_lvN1Q`, `runs_lvC1Q`; no `sorry`) for the *unchanged* level
programs `lvN2` … `lvC1` (`K1/RotateLevels.lean`) run with a routine satisfying `OffSpecQ` (offset
`off p1 p2 b c1 c2`, cost `Co·(b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1)^J`). They are
the proofs of `runs_lvN2` … `runs_lvC1` with the parameter slots `rP1, rP2` carried as invariants
(hypotheses `hP1, hP2` on the base state) and the cost constants taken at `2·cb` (`fib_cost_leP`;
hypotheses `p1, p2 ≤ cb·b`). Paper: Fact 3.3(4) (`fact:oai-streams`) and
Lemma A.4 (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

section LevelsQ

variable {Eo Ro : Type} [DecidableEq Eo]

/-- `runs_lvN2` for a routine with parameters (`OffSpecQ`; offset `off p1 p2 b c1 c2`); the
parameter slots `rP1, rP2` are read by the routine and never written. -/
theorem runs_lvN2Q {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (q cb b1 n1 b2 n2 b s p1 p2 : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b)
    (hv : v.length = NF * (s * q ^ b)) (hoffQ : ∀ c1 c2, off p1 p2 b c1 c2 < q ^ b)
    (B : RotL (Fin 2 ⊕ Eo) → List Sym) (c0 c1 c2 : ℕ) (rb r1 r2 rs rn2 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hr2 : TermOK r2) (hrs : TermOK rs)
    (hrn2 : TermOK rn2) (hbS : B rB = natSyms b ++ rb) (hC1 : B rC1 = natSyms c1 ++ r1)
    (hC2 : B rC2 = natSyms c2 ++ r2) (hsS : B rS = natSyms s ++ rs)
    (hN2 : B rN2 = natSyms n2 ++ rn2) (hc1 : c1 < q ^ b1) (hc2 : c2 < q ^ b2)
    (hc0 : c0 + n2 ≤ NF)
    (hctl : ∀ i < n2, offAt (q ^ b1) n1 (q ^ b2) n2 (off p1 p2 b) (c0 + i) = off p1 p2 b c1 c2)
    (r8 r9 : List Sym) (hr8 : TermOK r8) (hr9 : TermOK r9) (hp1 : p1 ≤ cb * b)
    (hp2 : p2 ≤ cb * b) (hP1 : B rP1 = natSyms p1 ++ r8) (hP2 : B rP2 = natSyms p2 ++ r9)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvN2 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + n2) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 n2)).reverse ++ U0))
      (fun _ => True) (lvK1 q (2 * cb) J Co * volR q b s v c0 n2) := by
  set F := s * q ^ b with hF
  have hlen : ∀ j, j < n2 → (chunk F (c0 + j) v).length = q ^ b * s := fun j hj => by
    rw [length_chunk (by rw [hv]; exact Nat.mul_le_mul_right _ (by omega)), hF, Nat.mul_comm]
  set St : ℕ → RotL (Fin 2 ⊕ Eo) → List Sym := fun j => fst B (arrSyms (v.drop ((c0 + j) * F)) ++ rest)
    O0 H0 H20 ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 j)).reverse ++ U0) with hSt
  have r := runs_nLoop (rlO (Ro := Ro)) (ns := rN2) (Kc := rN2c) (t := rTm) (by simp) (by simp)
    (by simp) (fibProg q Po) St n2 rn2 hrn2
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hN2])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun j => Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J + fibK q * vol (chunk F (c0 + j) v))
    (fun j hj => by
      have hpre : Function.update (St j) rN2c
          (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c) =
          fst (Function.update B rN2c (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c))
            (arrSyms (chunk F (c0 + j) v ++ v.drop ((c0 + j + 1) * F)) ++ rest) O0 H0 H20
            ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 j)).reverse ++ U0) := by
        rw [← drop_chunk]
        simp only [hSt]
        rw [fst_upd_comm] <;> simp
      rw [hpre]
      have hm := runs_fib_fstQ hO q hq
        (Function.update B rN2c (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c))
        (chunk F (c0 + j) v) (v.drop ((c0 + j + 1) * F)) rest b c1 c2 s p1 p2 rb r1 r2 rs r8 r9 hrb hr1
        hr2 hrs hr8 hr9 hs1 (hlen j hj) (hoffQ c1 c2) (by simp [hbS]) (by simp [hC1])
        (by simp [hC2]) (by simp [hsS]) (by simp [hP1]) (by simp [hP2]) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 j)).reverse ++ U0)
      refine WP.W9comp.runs_congr hm ?_
      have hG : gOut q b1 n1 b2 n2 b s (off p1 p2) v (c0 + j) =
          rotB (q ^ b) s (off p1 p2 b c1 c2) (chunk F (c0 + j) v) := by
        simp only [gOut, hctl j hj, ← hF]
      simp only [hSt]
      rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        outR_add, outR_one, hG, arrSyms_append, List.reverse_append, List.append_assoc,
        Nat.add_assoc])
  have h0 : St 0 = fst B (arrSyms (v.drop (c0 * F)) ++ rest) O0 H0 H20 U0 := by
    simp [hSt, outR_zero, arrSyms_nil]
  rw [h0] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  -- cost
  have hsum : ((List.range n2).map fun j =>
      Co * (b + bitLen c1 + bitLen c2 + bitLen p1 + bitLen p2 + 1) ^ J + fibK q * vol (chunk F (c0 + j) v)).sum ≤
      fibK0 q (2 * cb) J Co * volR q b s v c0 n2 := by
    simp only [volR, ← hF]
    rw [listSum_range, listSum_range, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj =>
      fib_cost_leP q cb J Co b b1 b2 c1 c2 p1 p2 s hq hc1 hc2 hb1 hb2 hp1 hp2 _ hs1
        (hlen j (Finset.mem_range.1 hj))
  have hge := volR_ge q b s v c0 n2 NF hv hc0
  have hF1 : 1 ≤ F := Nat.mul_pos hs1 (Nat.pow_pos (by omega : 0 < q))
  have hn2V : n2 ≤ volR q b s v c0 n2 := le_trans (Nat.le_mul_of_pos_right _ hF1) hge
  have hbn := bitLen_le_self' n2
  unfold lvK1
  rw [Nat.add_mul]
  omega

/-- `runs_lvC2` for a routine with parameters (`OffSpecQ`). -/
theorem runs_lvC2Q {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s p1 p2 : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b)
    (hv : v.length = NF * (s * q ^ b)) (hoffQ : ∀ c1 c2, off p1 p2 b c1 c2 < q ^ b)
    (B : RotL (Fin 2 ⊕ Eo) → List Sym) (c0 c1 : ℕ) (rb r1 rs rn2 rb2 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hrs : TermOK rs) (hrn2 : TermOK rn2)
    (hrb2 : TermOK rb2) (hbS : B rB = natSyms b ++ rb) (hC1 : B rC1 = natSyms c1 ++ r1)
    (hsS : B rS = natSyms s ++ rs) (hN2 : B rN2 = natSyms n2 ++ rn2)
    (hB2 : B rB2 = natSyms b2 ++ rb2) (hc1 : c1 < q ^ b1) (hc0 : c0 + q ^ b2 * n2 ≤ NF)
    (hctl : ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off p1 p2 b) (c0 + k * n2 + i) = off p1 p2 b c1 k)
    (r8 r9 : List Sym) (hr8 : TermOK r8) (hr9 : TermOK r9) (hp1 : p1 ≤ cb * b)
    (hp2 : p2 ≤ cb * b) (hP1 : B rP1 = natSyms p1 ++ r8) (hP2 : B rP2 = natSyms p2 ++ r9)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvC2 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + q ^ b2 * n2) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 (q ^ b2 * n2))).reverse ++ U0))
      (fun _ => True) (lvK2 q (2 * cb) J Co * volR q b s v c0 (q ^ b2 * n2)) := by
  set F := s * q ^ b with hF
  set G := gOut q b1 n1 b2 n2 b s (off p1 p2) v with hG
  set St : ℕ → RotL (Fin 2 ⊕ Eo) → List Sym := fun k =>
    fst (Function.update B rC2 (natSyms k ++ Sym.mark :: B rC2))
      (arrSyms (v.drop ((c0 + k * n2) * F)) ++ rest) O0 H0 H20
      ((arrSyms (outR G c0 (k * n2))).reverse ++ U0) with hSt
  have hSt0L : St 0 rL2 = B rL2 := by
    simp only [hSt]
    rw [fst_apply_ne] <;> simp
  -- push the guard of `C2`: counter `0`
  have y1 : Runs (rwk (Ro := Ro) (pushC rC2 .mark))
      (fst B (arrSyms (v.drop (c0 * F)) ++ rest) O0 H0 H20 U0) (St 0) (fun _ => True) 1 := by
    refine WP.W9comp.runs_congr (runs_wk_pushC rlO rC2 Sym.mark _) ?_
    simp only [hSt]
    rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [outR_zero, arrSyms_nil, natSyms, encodeNat_zero]
  -- the enumeration of `c2`
  have y2 := runs_powLoop (rlO (Ro := Ro)) q (bs := rB2) (L := rL2) (Kc := rKb) (t := rTm)
    (by simp) (by simp) (by simp) (by simp) (by simp) (leafC2 q Po)
    ⟨closed_lvN2 q hPoC, closed_inc_lift _ _⟩ St b2 rb2 hrb2
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hB2])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun k => lvK1 q (2 * cb) J Co * volR q b s v (c0 + k * n2) n2 + (6 * ones (encodeNat k) + 9))
    (fun k hk => by
      have hkn : c0 + k * n2 + n2 ≤ NF := by
        have : (k + 1) * n2 ≤ q ^ b2 * n2 := Nat.mul_le_mul_right _ hk
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hm1 := runs_lvN2Q hO q cb b1 n1 b2 n2 b s p1 p2 v rest NF hq hs1 hn2 hb1 hb2 hv hoffQ
        (Function.update (Function.update B rC2 (natSyms k ++ Sym.mark :: B rC2)) rL2
          (Sym.mark :: B rL2))
        (c0 + k * n2) c1 k rb r1 (Sym.mark :: B rC2) rs rn2 hrb hr1 (TermOK.cons rfl _) hrs
        hrn2 (by simp [hbS]) (by simp [hC1]) (by simp) (by simp [hsS]) (by simp [hN2]) hc1 hk
        hkn (fun i hi => hctl k hk i hi) r8 r9 hr8 hr9 hp1 hp2 (by simp [hP1]) (by simp [hP2])
        O0 H0 H20 ((arrSyms (outR G c0 (k * n2))).reverse ++ U0)
      have hm2 := runs_wk_inc (rlO (Ro := Ro)) (k := rC2) (t := rTm) (by simp) k
        (Sym.mark :: B rC2)
        (fst (Function.update (Function.update B rC2 (natSyms k ++ Sym.mark :: B rC2)) rL2
          (Sym.mark :: B rL2)) (arrSyms (v.drop ((c0 + k * n2 + n2) * F)) ++ rest) O0 H0 H20
          ((arrSyms (outR G (c0 + k * n2) n2)).reverse ++
            ((arrSyms (outR G c0 (k * n2))).reverse ++ U0)))
        (TermOK.cons rfl _) (by rw [fst_apply_ne] <;> simp)
      have hpre : Function.update (St k) rL2 (Sym.mark :: St 0 rL2) =
          fst (Function.update (Function.update B rC2 (natSyms k ++ Sym.mark :: B rC2)) rL2
            (Sym.mark :: B rL2)) (arrSyms (v.drop ((c0 + k * n2) * F)) ++ rest) O0 H0 H20
            ((arrSyms (outR G c0 (k * n2))).reverse ++ U0) := by
        rw [hSt0L]
        simp only [hSt]
        rw [fst_upd_comm] <;> simp
      rw [hpre]
      refine WP.W9comp.runs_congr (WP.W9comp.runs_seq hm1 hm2) ?_
      rw [hSt0L]
      simp only [hSt]
      rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        Nat.succ_mul, outR_add, arrSyms_append, List.reverse_append, List.append_assoc,
        ← Nat.add_assoc]
      congr 1
      funext k'
      simp only [Function.update_apply]
      split_ifs <;> simp_all)
  -- drop the counter `c2` and its guard
  have y3 := runs_wk_dropBits (rlO (Ro := Ro)) rC2 (encodeNat (q ^ b2)) Sym.mark (B rC2)
    (St (q ^ b2)) rfl (by simp only [hSt]; rw [fst_apply_ne] <;> simp [natSyms])
  have hfin : Function.update (St (q ^ b2)) rC2 (B rC2) =
      fst B (arrSyms (v.drop ((c0 + q ^ b2 * n2) * F)) ++ rest) O0 H0 H20
        ((arrSyms (outR G c0 (q ^ b2 * n2))).reverse ++ U0) := by
    simp only [hSt]
    rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      Function.update_idem, Function.update_eq_self]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq y1 (WP.W9comp.runs_seq y2
    (WP.W9comp.runs_congr y3 hfin))) (fun _ h => h) ?_
  -- cost
  exact lvC_cost_arith q (2 * cb) b b2 n2 s v c0 NF hq hs1 hn2 (cb_le2 hb2) hv hc0 (lvK1 q (2 * cb) J Co)

/-- `runs_lvN1` for a routine with parameters (`OffSpecQ`). -/
theorem runs_lvN1Q {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s p1 p2 : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hv : v.length = NF * (s * q ^ b))
    (hoffQ : ∀ c1 c2, off p1 p2 b c1 c2 < q ^ b)
    (B : RotL (Fin 2 ⊕ Eo) → List Sym) (c0 c1 : ℕ) (rb r1 rs rn2 rb2 rn1 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hrs : TermOK rs) (hrn2 : TermOK rn2)
    (hrb2 : TermOK rb2) (hrn1 : TermOK rn1) (hbS : B rB = natSyms b ++ rb)
    (hC1 : B rC1 = natSyms c1 ++ r1) (hsS : B rS = natSyms s ++ rs)
    (hN2 : B rN2 = natSyms n2 ++ rn2) (hB2 : B rB2 = natSyms b2 ++ rb2)
    (hN1 : B rN1 = natSyms n1 ++ rn1) (hc1 : c1 < q ^ b1)
    (hc0 : c0 + n1 * (q ^ b2 * n2) ≤ NF)
    (hctl : ∀ y < n1, ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off p1 p2 b) (c0 + y * (q ^ b2 * n2) + k * n2 + i) = off p1 p2 b c1 k)
    (r8 r9 : List Sym) (hr8 : TermOK r8) (hr9 : TermOK r9) (hp1 : p1 ≤ cb * b)
    (hp2 : p2 ≤ cb * b) (hP1 : B rP1 = natSyms p1 ++ r8) (hP2 : B rP2 = natSyms p2 ++ r9)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvN1 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + n1 * (q ^ b2 * n2)) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0 (n1 * (q ^ b2 * n2)))).reverse ++ U0))
      (fun _ => True) (lvK3 q (2 * cb) J Co * volR q b s v c0 (n1 * (q ^ b2 * n2))) := by
  set F := s * q ^ b with hF
  set m := q ^ b2 * n2 with hm
  set G := gOut q b1 n1 b2 n2 b s (off p1 p2) v with hG
  set St : ℕ → RotL (Fin 2 ⊕ Eo) → List Sym := fun j => fst B (arrSyms (v.drop ((c0 + j * m) * F)) ++ rest)
    O0 H0 H20 ((arrSyms (outR G c0 (j * m))).reverse ++ U0) with hSt
  have r := runs_nLoop (rlO (Ro := Ro)) (ns := rN1) (Kc := rN1c) (t := rTm) (by simp) (by simp)
    (by simp) (lvC2 q Po) St n1 rn1 hrn1
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hN1])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun j => lvK2 q (2 * cb) J Co * volR q b s v (c0 + j * m) m)
    (fun j hj => by
      have hjm : c0 + j * m + m ≤ NF := by
        have : (j + 1) * m ≤ n1 * m := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hpre : Function.update (St j) rN1c
          (natSyms (n1 - (j + 1)) ++ Sym.mark :: St 0 rN1c) =
          fst (Function.update B rN1c (natSyms (n1 - (j + 1)) ++ Sym.mark :: St 0 rN1c))
            (arrSyms (v.drop ((c0 + j * m) * F)) ++ rest) O0 H0 H20
            ((arrSyms (outR G c0 (j * m))).reverse ++ U0) := by
        simp only [hSt]
        rw [fst_upd_comm] <;> simp
      rw [hpre]
      have hm1 := runs_lvC2Q hO hPoC q cb b1 n1 b2 n2 b s p1 p2 v rest NF hq hs1 hn2 hb1 hb2 hv hoffQ
        (Function.update B rN1c (natSyms (n1 - (j + 1)) ++ Sym.mark :: St 0 rN1c))
        (c0 + j * m) c1 rb r1 rs rn2 rb2 hrb hr1 hrs hrn2 hrb2 (by simp [hbS]) (by simp [hC1])
        (by simp [hsS]) (by simp [hN2]) (by simp [hB2]) hc1 hjm
        (fun k hk i hi => hctl j hj k hk i hi) r8 r9 hr8 hr9 hp1 hp2 (by simp [hP1])
        (by simp [hP2]) O0 H0 H20
        ((arrSyms (outR G c0 (j * m))).reverse ++ U0)
      refine WP.W9comp.runs_congr hm1 ?_
      simp only [hSt]
      rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        Nat.succ_mul, outR_add, arrSyms_append, List.reverse_append, List.append_assoc,
        ← Nat.add_assoc])
  have h0 : St 0 = fst B (arrSyms (v.drop (c0 * F)) ++ rest) O0 H0 H20 U0 := by
    simp [hSt, outR_zero, arrSyms_nil]
  rw [h0] at r
  refine WP.W9comp.runs_mono r (fun _ h => h) ?_
  have hsum : ((List.range n1).map fun j => lvK2 q (2 * cb) J Co * volR q b s v (c0 + j * m) m).sum =
      lvK2 q (2 * cb) J Co * volR q b s v c0 (n1 * m) := by
    rw [← volR_mul, listSum_range, listSum_range, Finset.mul_sum]
  rw [hsum]
  have hge := volR_ge q b s v c0 (n1 * m) NF hv hc0
  rw [← hF] at hge
  have hF1 : 1 ≤ F := Nat.mul_pos hs1 (Nat.pow_pos (by omega : 0 < q))
  have hm1 : 1 ≤ m := Nat.mul_pos (Nat.pow_pos (by omega : 0 < q)) hn2
  have hn1V : n1 ≤ volR q b s v c0 (n1 * m) := by
    have h1 : n1 ≤ n1 * m := Nat.le_mul_of_pos_right _ hm1
    have h2 : n1 * m ≤ n1 * m * F := Nat.le_mul_of_pos_right _ hF1
    omega
  have hbn := bitLen_le_self' n1
  unfold lvK3
  rw [Nat.add_mul]
  omega

/-- `runs_lvC1` for a routine with parameters (`OffSpecQ`). -/
theorem runs_lvC1Q {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s p1 p2 : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hv : v.length = NF * (s * q ^ b))
    (hoffQ : ∀ c1 c2, off p1 p2 b c1 c2 < q ^ b)
    (B : RotL (Fin 2 ⊕ Eo) → List Sym) (c0 : ℕ) (rb rs rn2 rb2 rn1 rb1 : List Sym)
    (hrb : TermOK rb) (hrs : TermOK rs) (hrn2 : TermOK rn2) (hrb2 : TermOK rb2)
    (hrn1 : TermOK rn1) (hrb1 : TermOK rb1) (hbS : B rB = natSyms b ++ rb)
    (hsS : B rS = natSyms s ++ rs) (hN2 : B rN2 = natSyms n2 ++ rn2)
    (hB2 : B rB2 = natSyms b2 ++ rb2) (hN1 : B rN1 = natSyms n1 ++ rn1)
    (hB1 : B rB1 = natSyms b1 ++ rb1)
    (hc0 : c0 + q ^ b1 * (n1 * (q ^ b2 * n2)) ≤ NF)
    (hctl : ∀ x1 < q ^ b1, ∀ y < n1, ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off p1 p2 b)
        (c0 + x1 * (n1 * (q ^ b2 * n2)) + y * (q ^ b2 * n2) + k * n2 + i) = off p1 p2 b x1 k)
    (r8 r9 : List Sym) (hr8 : TermOK r8) (hr9 : TermOK r9) (hp1 : p1 ≤ cb * b)
    (hp2 : p2 ≤ cb * b) (hP1 : B rP1 = natSyms p1 ++ r8) (hP2 : B rP2 = natSyms p2 ++ r9)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvC1 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + q ^ b1 * (n1 * (q ^ b2 * n2))) * (s * q ^ b))) ++ rest)
        O0 H0 H20 ((arrSyms (outR (gOut q b1 n1 b2 n2 b s (off p1 p2) v) c0
          (q ^ b1 * (n1 * (q ^ b2 * n2))))).reverse ++ U0))
      (fun _ => True) (lvK4 q (2 * cb) J Co * volR q b s v c0 (q ^ b1 * (n1 * (q ^ b2 * n2)))) := by
  set F := s * q ^ b with hF
  set m := n1 * (q ^ b2 * n2) with hm
  set G := gOut q b1 n1 b2 n2 b s (off p1 p2) v with hG
  set St : ℕ → RotL (Fin 2 ⊕ Eo) → List Sym := fun k =>
    fst (Function.update B rC1 (natSyms k ++ Sym.mark :: B rC1))
      (arrSyms (v.drop ((c0 + k * m) * F)) ++ rest) O0 H0 H20
      ((arrSyms (outR G c0 (k * m))).reverse ++ U0) with hSt
  have hSt0L : St 0 rL1 = B rL1 := by
    simp only [hSt]
    rw [fst_apply_ne] <;> simp
  have hm1 : 1 ≤ m := Nat.mul_pos hn1 (Nat.mul_pos (Nat.pow_pos (by omega : 0 < q)) hn2)
  have y1 : Runs (rwk (Ro := Ro) (pushC rC1 .mark))
      (fst B (arrSyms (v.drop (c0 * F)) ++ rest) O0 H0 H20 U0) (St 0) (fun _ => True) 1 := by
    refine WP.W9comp.runs_congr (runs_wk_pushC rlO rC1 Sym.mark _) ?_
    simp only [hSt]
    rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [outR_zero, arrSyms_nil, natSyms, encodeNat_zero]
  have y2 := runs_powLoop (rlO (Ro := Ro)) q (bs := rB1) (L := rL1) (Kc := rKb) (t := rTm)
    (by simp) (by simp) (by simp) (by simp) (by simp) (leafC1 q Po)
    ⟨closed_lvN1 q hPoC, closed_inc_lift _ _⟩ St b1 rb1 hrb1
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hB1])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun k => lvK3 q (2 * cb) J Co * volR q b s v (c0 + k * m) m + (6 * ones (encodeNat k) + 9))
    (fun k hk => by
      have hkm : c0 + k * m + n1 * (q ^ b2 * n2) ≤ NF := by
        have : (k + 1) * m ≤ q ^ b1 * m := Nat.mul_le_mul_right _ hk
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hm1' := runs_lvN1Q hO hPoC q cb b1 n1 b2 n2 b s p1 p2 v rest NF hq hs1 hn1 hn2 hb1 hb2 hv
        hoffQ
        (Function.update (Function.update B rC1 (natSyms k ++ Sym.mark :: B rC1)) rL1
          (Sym.mark :: B rL1))
        (c0 + k * m) k rb (Sym.mark :: B rC1) rs rn2 rb2 rn1 hrb (TermOK.cons rfl _) hrs hrn2
        hrb2 hrn1 (by simp [hbS]) (by simp) (by simp [hsS]) (by simp [hN2]) (by simp [hB2])
        (by simp [hN1]) hk hkm (fun y hy k' hk' i hi => hctl k hk y hy k' hk' i hi) r8 r9 hr8 hr9
        hp1 hp2 (by simp [hP1]) (by simp [hP2]) O0 H0 H20
        ((arrSyms (outR G c0 (k * m))).reverse ++ U0)
      have hm2 := runs_wk_inc (rlO (Ro := Ro)) (k := rC1) (t := rTm) (by simp) k
        (Sym.mark :: B rC1)
        (fst (Function.update (Function.update B rC1 (natSyms k ++ Sym.mark :: B rC1)) rL1
          (Sym.mark :: B rL1)) (arrSyms (v.drop ((c0 + k * m + m) * F)) ++ rest) O0 H0 H20
          ((arrSyms (outR G (c0 + k * m) m)).reverse ++
            ((arrSyms (outR G c0 (k * m))).reverse ++ U0)))
        (TermOK.cons rfl _) (by rw [fst_apply_ne] <;> simp)
      have hpre : Function.update (St k) rL1 (Sym.mark :: St 0 rL1) =
          fst (Function.update (Function.update B rC1 (natSyms k ++ Sym.mark :: B rC1)) rL1
            (Sym.mark :: B rL1)) (arrSyms (v.drop ((c0 + k * m) * F)) ++ rest) O0 H0 H20
            ((arrSyms (outR G c0 (k * m))).reverse ++ U0) := by
        rw [hSt0L]
        simp only [hSt]
        rw [fst_upd_comm] <;> simp
      rw [hpre]
      refine WP.W9comp.runs_congr (WP.W9comp.runs_seq hm1' hm2) ?_
      rw [hSt0L]
      simp only [hSt]
      rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        Nat.succ_mul, outR_add, arrSyms_append, List.reverse_append, List.append_assoc,
        ← Nat.add_assoc]
      congr 1
      funext k'
      simp only [Function.update_apply]
      split_ifs <;> simp_all)
  have y3 := runs_wk_dropBits (rlO (Ro := Ro)) rC1 (encodeNat (q ^ b1)) Sym.mark (B rC1)
    (St (q ^ b1)) rfl (by simp only [hSt]; rw [fst_apply_ne] <;> simp [natSyms])
  have hfin : Function.update (St (q ^ b1)) rC1 (B rC1) =
      fst B (arrSyms (v.drop ((c0 + q ^ b1 * m) * F)) ++ rest) O0 H0 H20
        ((arrSyms (outR G c0 (q ^ b1 * m))).reverse ++ U0) := by
    simp only [hSt]
    rw [fst_upd_comm _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      Function.update_idem, Function.update_eq_self]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq y1 (WP.W9comp.runs_seq y2
    (WP.W9comp.runs_congr y3 hfin))) (fun _ h => h) ?_
  exact lvC_cost_arith q (2 * cb) b b1 m s v c0 NF hq hs1 hm1 (cb_le2 hb1) hv hc0 (lvK3 q (2 * cb) J Co)

end LevelsQ

end SubNLogN.Machine.K1.Rot
