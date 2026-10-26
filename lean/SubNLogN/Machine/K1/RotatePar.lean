/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateParLevels
import SubNLogN.Machine.K1.Rotate
import SubNLogN.Machine.K1.RotateParSpec

/-!
# K1, K4-ctl-par (`K1/RotatePar.lean`): the parameterized controlled rotation, proved

**Result.** `SubNLogN.Machine.K1.k4RotateCtlPar_holds q cb J off : K4RotateCtlParStmt q cb J off`
for all `q cb J off` (statement: `SubNLogN/Machine/K1/RotateParSpec.lean`; paper:
Fact 3.3(4) (`fact:oai-streams`) and Lemma A.4 (`lem:transfer-streams`)). The statement is
itself an implication from its premises (`2 ≤ q`, an offset routine `K4OffsetCtlParStmt off J`,
reduced offsets `off k1 k2 b c1 c2 < q^b`); nothing else is assumed (no `sorry`).

## Program (`rotParProg`)
The K4-ctl kernel `rotProg` (`K1/Rotate.lean`, unchanged) run with the relabeled parameterized
routine `relP Po` (`K1/RotateParFiber.lean`), whose two parameter stacks sit in the routine-scratch
slots `rP1, rP2`; the whole kernel is relabeled along the bijection `embT` onto the statement's
layout `KLoc (Fin 10) _`, where the two slots become the named stacks `8, 9`.

## Cost
As for K4-ctl; the routine's cost `Co·(b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1)^J` is
absorbed by the fiber volume `≥ 2^b` using `b1, b2, k1, k2 ≤ cb·b` (`fib_cost_leP`). The total is
`≤ rotC q (2·cb) J Co · (V + 1)`, a constant depending only on `q, cb, J` and the routine's `Co`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

section TopQ

variable {Eo Ro : Type} [DecidableEq Eo]

/-- **The kernel's run** (`runs_rot`) with a routine with parameters (`OffSpecQ`): offset
`off p1 p2 b c1 c2`, parameters in the slots `rP1, rP2` (restored). -/
theorem runs_rotQ {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) (Fin 2 ⊕ Eo)) (fun _ => Sym) Ro} (hO : OffSpecQ off J Co Po)
    (hPoC : Po.Closed) (q cb : ℕ) (hq : 2 ≤ q) (p1 p2 : ℕ)
    (hoffQ : ∀ b c1 c2, off p1 p2 b c1 c2 < q ^ b)
    (np b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest r2 r3 r4 r5 r6 r7 r8 r9 : List Sym)
    (S : RotL (Fin 2 ⊕ Eo) → List Sym)
    (hlen : v.length = np * q ^ b1 * n1 * q ^ b2 * n2 * q ^ b * s) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hp1 : p1 ≤ cb * b) (hp2 : p2 ≤ cb * b)
    (hrest : BlkTerm rest) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6) (hr7 : TermOK r7)
    (hr8 : TermOK r8) (hr9 : TermOK r9)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hS2 : S (.inl 2) = natSyms b1 ++ r2)
    (hS3 : S (.inl 3) = natSyms n1 ++ r3) (hS4 : S (.inl 4) = natSyms b2 ++ r4)
    (hS5 : S (.inl 5) = natSyms n2 ++ r5) (hS6 : S (.inl 6) = natSyms b ++ r6)
    (hS7 : S (.inl 7) = natSyms s ++ r7)
    (hS8 : S rP1 = natSyms p1 ++ r8) (hS9 : S rP2 = natSyms p2 ++ r9) :
    Runs (rotProg q Po) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off p1 p2 b)) v) ++
          S (.inl 1)))
      (fun _ => True) (rotC q (2 * cb) J Co * (vol v + 1)) := by
  set F := s * q ^ b with hF
  set M := q ^ b1 * (n1 * (q ^ b2 * n2)) with hM
  set G := gOut q b1 n1 b2 n2 b s (off p1 p2) v with hG
  have hv : v.length = (np * M) * F := by rw [hlen, hM, hF]; ring
  set out := permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off p1 p2 b)) v with hout
  set nb := if v = [] then 0 else np with hnb
  have hpos : v ≠ [] → 1 ≤ np ∧ 1 ≤ n1 ∧ 1 ≤ n2 ∧ 1 ≤ s := by
    intro hne
    have h : 0 < v.length := List.length_pos_of_ne_nil hne
    rw [hlen] at h
    refine ⟨Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_,
      Nat.pos_of_ne_zero ?_⟩ <;> rintro rfl <;> simp at h
  have hMF : v ≠ [] → 1 ≤ M * F := by
    intro hne
    obtain ⟨-, hn1, hn2, hs1⟩ := hpos hne
    have hq0 : 0 < q := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hq0) (Nat.mul_pos hn1
      (Nat.mul_pos (Nat.pow_pos hq0) hn2))) (Nat.mul_pos hs1 (Nat.pow_pos hq0))
  -- the end of the loop: nothing left, all outputs staged
  have hdrop : v.drop (nb * M * F) = [] := by
    by_cases hne : v = []
    · simp [hne]
    · simp only [hnb, hne, if_false]
      apply List.drop_eq_nil_of_le
      rw [hv]
  have houtR : outR G 0 (nb * M) = out := by
    by_cases hne : v = []
    · simp only [hnb, hne, if_true, Nat.zero_mul, outR_zero, hout]
      simp [permByInv]
    · simp only [hnb, hne, if_false, hout]
      rw [permByInv_rotCtl (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off p1 p2 b) (hoffQ b) v (np * M) hv]
      simp [outR, hG, gOut]
  -- 1. guard on `U`
  have t1 : Runs (rwk (Ro := Ro) (pushC rU .mark)) S
      (fst S (arrSyms v ++ rest) (S rO) (S rH) (S rH2) (Sym.mark :: S rU)) (fun _ => True) 1 := by
    refine WP.W9comp.runs_congr (runs_wk_pushC rlO rU Sym.mark S) ?_
    funext k
    simp only [fst, Function.update_apply]
    split_ifs <;> simp_all
  -- 2. the first test
  have t2 := triple_peek_fst (τ := Ro) (rSrc : RotL (Fin 2 ⊕ Eo))
    (fst S (arrSyms v ++ rest) (S rO) (S rH) (S rH2) (Sym.mark :: S rU))
  -- 3. the loop over the blocks of `M` fibers
  set St : ℕ → List Unit → Unit → RotL (Fin 2 ⊕ Eo) → List Sym := fun x _ _ =>
    fst S (arrSyms (v.drop (x * M * F)) ++ rest) (S rO) (S rH) (S rH2)
      ((arrSyms (outR G 0 (x * M))).reverse ++ Sym.mark :: S rU) with hSt
  have hloop := triple_loop_list (c := fun r : RotR Ro => isRecTop r.1)
    (body := .seq (lvC1 q Po) (rwk (peekR rSrc)))
    St (fun vs r => isRecTop r.1 = !vs.isEmpty) (fun _ _ _ => ())
    (fun x _ => lvK4 q (2 * cb) J Co * volR q b s v (x * M) M + 1)
    (fun x vs => x + vs.length = nb)
    (fun x a vs h => by simp only [List.length_cons] at h; omega)
    (fun r hr => by rw [hr]; rfl)
    (fun a vs r hr => by rw [hr]; rfl)
    (fun x a vs g hok => by
      have hxnb : x < nb := by simp only [List.length_cons] at hok; omega
      have hne : v ≠ [] := by
        intro h
        simp [hnb, h] at hxnb
      have hnbnp : nb = np := by simp [hnb, hne]
      obtain ⟨hnp, hn1, hn2, hs1⟩ := hpos hne
      have hc0 : x * M + M ≤ np * M := by
        have : (x + 1) * M ≤ np * M := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        exact this
      have hm := runs_lvC1Q hO hPoC q cb b1 n1 b2 n2 b s p1 p2 v rest (np * M) hq hs1 hn1 hn2 hb1 hb2
        hv (hoffQ b) S (x * M) r6 r7 r5 r4 r3 r2 hr6 hr7 hr5 hr4 hr3 hr2 hS6 hS7 hS5 hS4 hS3
        hS2 hc0
        (fun k1 hk1 y hy k hk i hi => by
          have := offAt_idx (q ^ b1) n1 (q ^ b2) n2 (off p1 p2 b) (p := x) hk1 hy hk hi
          rw [← this]
          congr 1
          rw [hM]
          ring)
        r8 r9 hr8 hr9 hp1 hp2 hS8 hS9
        (S rO) (S rH) (S rH2) ((arrSyms (outR G 0 (x * M))).reverse ++ Sym.mark :: S rU)
      have hpost : fst S (arrSyms (v.drop ((x * M + M) * F)) ++ rest) (S rO) (S rH) (S rH2)
          ((arrSyms (outR G (x * M) M)).reverse ++
            ((arrSyms (outR G 0 (x * M))).reverse ++ Sym.mark :: S rU)) = St (x + 1) vs () := by
        simp only [hSt]
        rw [Nat.succ_mul, outR_add, Nat.zero_add, arrSyms_append, List.reverse_append,
          List.append_assoc]
      rw [hpost] at hm
      have hp := triple_peek_fst (τ := Ro) (rSrc : RotL (Fin 2 ⊕ Eo)) (St (x + 1) vs ())
      refine Triple.conseq (runs_seq_triple hm hp) (fun s hs => hs.1) (fun s hs => ⟨hs.1, ?_⟩)
        le_rfl
      rw [hs.2]
      simp only [hSt, fst_src]
      rcases vs with _ | ⟨a', vs'⟩
      · -- last block: the source is exhausted
        have hx1 : x + 1 = np := by simp only [List.length_cons, List.length_nil] at hok; omega
        rw [hx1, List.drop_eq_nil_of_le (by rw [hv])]
        exact isRecTop_nil hrest
      · -- another block follows
        have hlt : (x + 1) * M * F < v.length := by
          simp only [List.length_cons] at hok
          rw [hv]
          have h1 := hMF hne
          have h2 : (x + 1) * (M * F) < np * (M * F) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa [Nat.mul_assoc] using h2
        obtain ⟨p, l, hpl⟩ : ∃ p l, v.drop ((x + 1) * M * F) = p :: l := by
          cases h : v.drop ((x + 1) * M * F) with
          | nil =>
            have := List.drop_eq_nil_iff.1 h
            omega
          | cons p l => exact ⟨p, l, rfl⟩
        rw [hpl]
        simpa using isRecTop_cons p l rest)
    (List.replicate nb ()) 0 () (by simp)
  -- normalize the loop's start and end states
  have hSt0 : St 0 (List.replicate nb ()) () =
      fst S (arrSyms v ++ rest) (S rO) (S rH) (S rH2) (Sym.mark :: S rU) := by
    simp [hSt, outR_zero, arrSyms_nil]
  have hStE : St (0 + (List.replicate nb ()).length) []
      (foldG (fun _ _ _ => ()) 0 (List.replicate nb ()) ()) =
      fst S (arrSyms [] ++ rest) (S rO) (S rH) (S rH2)
        ((arrSyms out).reverse ++ Sym.mark :: S rU) := by
    simp only [hSt, List.length_replicate, Nat.zero_add, hdrop, houtR]
  have hinit : isRecTop (arrSyms v ++ rest).head? = !(List.replicate nb ()).isEmpty := by
    by_cases hne : v = []
    · have h0 : nb = 0 := by simp [hnb, hne]
      rw [h0, hne]
      simpa using isRecTop_nil hrest
    · obtain ⟨p, l, hpl⟩ := List.exists_cons_of_ne_nil hne
      have hnp := (hpos hne).1
      have h0 : nb = np := by simp [hnb, hne]
      rw [h0, hpl, isRecTop_cons]
      obtain ⟨n, rfl⟩ : ∃ n, np = n + 1 := ⟨np - 1, by omega⟩
      simp
  have t2' : Triple [] (fun s => s.stk =
        fst S (arrSyms v ++ rest) (S rO) (S rH) (S rH2) (Sym.mark :: S rU))
      (rwk (Ro := Ro) (peekR rSrc))
      (fun s => s.stk = St 0 (List.replicate nb ()) () ∧
        isRecTop s.var.1 = !(List.replicate nb ()).isEmpty) 1 :=
    Triple.post t2 fun s hs => ⟨hs.1.trans hSt0.symm, by rw [hs.2, fst_src]; exact hinit⟩
  have hloop' := Triple.post hloop fun s hs => hs.trans hStE
  -- 4. the outputs go to the destination
  have t3 := WP.W9comp.runs_rewind (rlO (Ro := Ro)) (src := (rU : RotL (Fin 2 ⊕ Eo))) (dst := rDst)
    (by simp) Sym.mark (arrSyms out).reverse (S rU)
    (fst S (arrSyms [] ++ rest) (S rO) (S rH) (S rH2) ((arrSyms out).reverse ++ Sym.mark :: S rU))
    (mark_not_mem_rev_arrSyms out) (by simp)
  have hfin : Function.update (Function.update (fst S (arrSyms [] ++ rest) (S rO) (S rH) (S rH2)
      ((arrSyms out).reverse ++ Sym.mark :: S rU)) rU (S rU)) rDst
      ((arrSyms out).reverse.reverse ++ fst S (arrSyms [] ++ rest) (S rO) (S rH) (S rH2)
        ((arrSyms out).reverse ++ Sym.mark :: S rU) rDst) =
      Function.update (Function.update S (.inl 0) rest) (.inl 1) (arrSyms out ++ S (.inl 1)) := by
    funext k
    simp only [fst, Function.update_apply, arrSyms_nil, List.nil_append, List.reverse_reverse]
    split_ifs <;> simp_all
  have hall := Triple.seq (Triple.post t1 fun _ h => h.1) (Triple.seq t2'
    (Triple.seq hloop' (WP.W9comp.runs_congr t3 hfin)))
  refine Triple.cost_mono hall ?_
  -- cost
  rw [loopB_replicate]
  have hvm := volR_mul q b s v 0 M nb
  rw [listSum_range] at hvm
  simp only [Nat.zero_add] at hvm
  have hsum : ((List.range nb).map fun j =>
      lvK4 q (2 * cb) J Co * volR q b s v ((0 + j) * M) M + 1 + 1).sum =
      lvK4 q (2 * cb) J Co * volR q b s v 0 (nb * M) + 2 * nb := by
    rw [listSum_range]
    simp only [Nat.zero_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, Nat.mul_one, ← Finset.mul_sum, hvm]
    ring
  rw [hsum]
  have hVv : volR q b s v 0 (nb * M) ≤ vol v := by
    by_cases hne : v = []
    · simp [hnb, hne, volR]
    · have h0 : nb = np := by simp [hnb, hne]
      rw [h0, volR_all q b s v (np * M) hv]
  have hLv : ((arrSyms out).reverse).length = volR q b s v 0 (nb * M) := by
    rw [List.length_reverse, ← houtR, ← vol_outR]
    rfl
  have hnbv : nb ≤ vol v := by
    by_cases hne : v = []
    · simp [hnb, hne]
    · have h0 : nb = np := by simp [hnb, hne]
      have h1 := hMF hne
      have h2 := length_le_vol v
      have h3 : np ≤ np * (M * F) := Nat.le_mul_of_pos_right _ h1
      rw [h0]
      rw [hv, Nat.mul_assoc] at h2
      omega
  rw [hLv]
  unfold rotC
  nlinarith [hVv, hnbv]

end TopQ

/-! ## Relabeling onto the statement's layout -/

section Relabel

variable {Eo : Type}

/-- The kernel's stacks as the statement's stacks: named `0..7` stay, the parameter slots
`rP1, rP2` become named `8, 9`; the routine's own scratch and the kernel's own stacks are scratch. -/
def embT : RotL (Fin 2 ⊕ Eo) → KLoc (Fin 10) (RotE Eo)
  | .inl i => .inl ⟨i.val, by have := i.isLt; omega⟩
  | .inr (.inl (.inl j)) => .inl ⟨8 + j.val, by have := j.isLt; omega⟩
  | .inr (.inl (.inr e)) => .inr (.inl e)
  | .inr (.inr i) => .inr (.inr i)

/-- Inverse of `embT`. -/
def unT : KLoc (Fin 10) (RotE Eo) → RotL (Fin 2 ⊕ Eo)
  | .inl i => if h : i.val < 8 then .inl ⟨i.val, h⟩
      else .inr (.inl (.inl ⟨i.val - 8, by have := i.isLt; omega⟩))
  | .inr (.inl e) => .inr (.inl (.inr e))
  | .inr (.inr i) => .inr (.inr i)

theorem unT_embT (x : RotL (Fin 2 ⊕ Eo)) : unT (embT x) = x := by
  rcases x with i | (j | e) | i
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl
  · rfl
  · rfl

theorem embT_unT (y : KLoc (Fin 10) (RotE Eo)) : embT (unT y) = y := by
  rcases y with i | e | i
  · fin_cases i <;> rfl
  · rfl
  · rfl

theorem embT_injective :
    Function.Injective (embT : RotL (Fin 2 ⊕ Eo) → KLoc (Fin 10) (RotE Eo)) :=
  Function.LeftInverse.injective unT_embT

end Relabel

section TopPar

variable {Eo : Type} [DecidableEq Eo]

/-- **The K4-ctl-par kernel**: the K4-ctl kernel with the relabeled parameterized routine,
relabeled onto the statement's layout. -/
def rotParProg {Ro : Type} (q : ℕ) (Po : Prog (KLoc (Fin 6) Eo) (fun _ => Sym) Ro) :
    Prog (KLoc (Fin 10) (RotE Eo)) (fun _ => Sym) (RotR Ro) :=
  callInj embT (lensIdR (RotR Ro)) (rotProg q (relP Po))

theorem closed_rotParProg {Ro : Type} (q : ℕ) {Po : Prog (KLoc (Fin 6) Eo) (fun _ => Sym) Ro}
    (h : Po.Closed) : (rotParProg q Po).Closed :=
  closed_callInj _ _ (closed_rotProg q (closed_relP h))

/-- **The K4-ctl-par kernel's run**, in the statement's form. -/
theorem runs_rotPar {Ro : Type} {off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 6) Eo) (fun _ => Sym) Ro} (hO : OffSpecP off J Co Po)
    (hPoC : Po.Closed) (q cb : ℕ) (hq : 2 ≤ q) (hoffQ : ∀ k1 k2 b c1 c2, off k1 k2 b c1 c2 < q ^ b)
    (np b1 n1 b2 n2 b s k1 k2 : ℕ) (v : List (List Bool))
    (rest r2 r3 r4 r5 r6 r7 r8 r9 : List Sym) (S : KLoc (Fin 10) (RotE Eo) → List Sym)
    (hlen : v.length = np * q ^ b1 * n1 * q ^ b2 * n2 * q ^ b * s) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hk1 : k1 ≤ cb * b) (hk2 : k2 ≤ cb * b) (hrest : BlkTerm rest)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hr7 : TermOK r7) (hr8 : TermOK r8) (hr9 : TermOK r9)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hS2 : S (.inl 2) = natSyms b1 ++ r2)
    (hS3 : S (.inl 3) = natSyms n1 ++ r3) (hS4 : S (.inl 4) = natSyms b2 ++ r4)
    (hS5 : S (.inl 5) = natSyms n2 ++ r5) (hS6 : S (.inl 6) = natSyms b ++ r6)
    (hS7 : S (.inl 7) = natSyms s ++ r7) (hS8 : S (.inl 8) = natSyms k1 ++ r8)
    (hS9 : S (.inl 9) = natSyms k2 ++ r9) :
    Runs (rotParProg q Po) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (permByInv (rotCtlInvAddr (q ^ b1) n1 (q ^ b2) n2 (q ^ b) s (off k1 k2 b)) v)
          ++ S (.inl 1)))
      (fun _ => True) (rotC q (2 * cb) J Co * (vol v + 1)) := by
  have h0 : (embT (.inl 0) : KLoc (Fin 10) (RotE Eo)) = .inl 0 := rfl
  have h1 : (embT (.inl 1) : KLoc (Fin 10) (RotE Eo)) = .inl 1 := rfl
  have hR := runs_rotQ (offSpecQ_relP hO) (closed_relP hPoC) q cb hq k1 k2 (hoffQ k1 k2)
    np b1 n1 b2 n2 b s v rest r2 r3 r4 r5 r6 r7 r8 r9 (S ∘ embT) hlen hb1 hb2 hk1 hk2 hrest
    hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hS0 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9
  refine runs_callInj (Q := fun _ => True) embT_injective (lensIdR (RotR Ro)) ?_ ?_
  · rw [← h0, ← h1, Function.update_comp_eq_of_injective _ embT_injective,
      Function.update_comp_eq_of_injective S embT_injective]
    exact hR
  · intro k hk
    exact absurd (embT_unT k) (hk _)

end TopPar

end SubNLogN.Machine.K1.Rot

namespace SubNLogN.Machine.K1

open TMFw TMFw.Contracts SubNLogN.Machine.K1.Rot

/-- **K4-ctl-par, controlled cyclic shift with two control blocks and two runtime parameters,
proved** (`K4RotateCtlParStmt`, `SubNLogN/Machine/K1/RotateParSpec.lean`; paper:
Fact 3.3(4) (`fact:oai-streams`), Lemma A.4 (`lem:transfer-streams`)). For all `q cb J off`:
given `2 ≤ q`, an offset routine with parameters (`K4OffsetCtlParStmt off J`) and reduced offsets
(`off k1 k2 b c1 c2 < q^b`) — the statement's own premises — the kernel `rotParProg` rotates the
target coordinate of every fiber of the shape `[np] × [q^{b1}] × [n1] × [q^{b2}] × [n2] × [q^b] × [s]`
by `off k1 k2 b c1 c2` (`permByInv (rotCtlInvAddr …)`), consuming the source, pushing the result on
the destination and restoring every other stack, within `rotC q (2·cb) J Co · (V + 1)` steps (`Co`
the routine's constant), whenever `b1, b2, k1, k2 ≤ cb·b`. -/
theorem k4RotateCtlPar_holds (q cb J : ℕ) (off : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    K4RotateCtlParStmt q cb J off := by
  intro hq hOff hoffQ
  obtain ⟨Co, hCo⟩ := hOff
  obtain ⟨Eo, iEoF, iEoD, Ro, Po, hRoF, hRoN, hPoC, hPoS⟩ := hCo ()
  refine ⟨rotC q (2 * cb) J Co, fun _ => ⟨RotE Eo, inferInstance, inferInstance, RotR Ro,
    rotParProg q Po, ?_, ?_, closed_rotParProg q hPoC, ?_⟩⟩
  · have := hRoF
    infer_instance
  · obtain ⟨r⟩ := hRoN
    exact ⟨(none, r)⟩
  · intro np b1 n1 b2 n2 b s k1 k2 v rest r2 r3 r4 r5 r6 r7 r8 r9 S hlen hb1 hb2 hk1 hk2 hrest
      hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hS0 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hS9
    exact runs_rotPar hPoS hPoC q cb hq hoffQ np b1 n1 b2 n2 b s k1 k2 v rest r2 r3 r4 r5 r6 r7
      r8 r9 S hlen hb1 hb2 hk1 hk2 hrest hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hS0 hS2 hS3 hS4 hS5 hS6
      hS7 hS8 hS9

end SubNLogN.Machine.K1
