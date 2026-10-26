import WP.W9h.RecPass

/-!
# WP.W9h.RecLoops — the two passes of `W9_reconstruct` as counted loops

* `rs1 B b cs rA i`: carry-pass state with counter `i` (digits `0 … n-i-1` done): `OA` holds the
  remaining digits, `rCR` the carry, `rL` the low parts so far (last on top).
* `rs2 B b cs rA i`: Horner state with counter `i`: `OA` holds `horner` of the low parts `≥ i`,
  `rL` the low parts `< i`.
* `HT_pass1`, `HT_pass2`: the loops, at cost `(C+1)·(n·(Y+4) + 2)`.
-/

namespace WP.W9h

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

theorem natSyms_zero : natSyms 0 = [] :=
  List.eq_nil_of_length_eq_zero (by rw [length_natSyms, bitLen_zero])

theorem hdrSyms_cons (x : ℕ) (xs : List ℕ) (r : List Sym) :
    hdrSyms (x :: xs) ++ r = natSyms x ++ Sym.mark :: (hdrSyms xs ++ r) := by
  simp [hdrSyms]

namespace Kit

variable {K : Kit} {C : ℕ} (hK : K.Spec C)
include hK

/-- Counted loop at cost `(C+1)·(n·(Y+4)+2)` for a body of cost `(C+1)·Y`. -/
theorem HT_loopc' (ctr : H) (rc : List Sym) (hrc : TermOK rc) (n : ℕ)
    (St : ℕ → H → List Sym) (hSt : ∀ i ≤ n, St i ctr = natSyms i ++ rc) (body : K.KP) (Y : ℕ)
    (hbody : ∀ i < n, HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i)
      ((C + 1) * Y)) :
    HT [] (St n) (K.loopc ctr body) (St 0) ((C + 1) * (n * (Y + 4) + 2)) :=
  (Kit.HT_loopc hK ctr rc hrc n St hSt body _ hbody).mono (by
    have h1 : C * bitLen n ≤ C * n := Nat.mul_le_mul_left _ (bitLen_le_self n)
    ring_nf at h1 ⊢
    omega)

end Kit

/-- Carry-pass state with counter `i`. -/
def rs1 (B : H → List Sym) (b : ℕ) (cs : List ℕ) (rA : List Sym) (i : ℕ) : H → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update B
    rB (natSyms b ++ Sym.mark :: B rB)) rCT2 (natSyms cs.length ++ Sym.mark :: B rCT2))
    rT (Sym.mark :: B rT))
    hOA (hdrSyms (cs.drop (cs.length - i)) ++ rA)) rCT (natSyms i ++ Sym.mark :: B rCT))
    rCR (natSyms (carryRun b 0 (cs.take (cs.length - i))).2 ++ Sym.mark :: B rCR))
    rL (hdrSyms (carryRun b 0 (cs.take (cs.length - i))).1.reverse ++ B rL)

/-- Horner state with counter `i`. -/
def rs2 (B : H → List Sym) (b : ℕ) (cs : List ℕ) (rA : List Sym) (i : ℕ) : H → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update B
    rB (natSyms b ++ Sym.mark :: B rB)) rCT (Sym.mark :: B rCT)) rT (Sym.mark :: B rT))
    rCR (Sym.mark :: B rCR))
    hOA (natSyms (horner b ((carryRun b 0 cs).1.drop i) (carryRun b 0 cs).2) ++ rA))
    rCT2 (natSyms i ++ Sym.mark :: B rCT2))
    rL (hdrSyms ((carryRun b 0 cs).1.take i).reverse ++ B rL)

namespace Kit

variable {K : Kit} {C : ℕ} (hK : K.Spec C)
include hK

/-- **Pass 1** (carry pass). -/
theorem HT_pass1 (B : H → List Sym) (b K0 wD : ℕ) (cs : List ℕ) (rA : List Sym)
    (hK0 : cs.length ≤ 2 ^ K0) (hwD : ∀ c ∈ cs, bitLen c ≤ wD) :
    HT [] (rs1 B b cs rA cs.length) (K.loopc rCT K.recBody1) (rs1 B b cs rA 0)
      ((C + 1) * (cs.length * (6 * wD + 4 * K0 + 2 * b + 8 + 4) + 2)) := by
  refine HT_loopc' hK rCT (Sym.mark :: B rCT) (termOK_mark' _) cs.length (rs1 B b cs rA)
    (fun i _ => by simp [rs1]) K.recBody1 _ (fun i hi => ?_)
  obtain ⟨j, hj⟩ : ∃ j, cs.length - (i + 1) = j := ⟨_, rfl⟩
  have hjn : j < cs.length := by omega
  have hij : cs.length - i = j + 1 := by omega
  have hdrop := List.drop_eq_getElem_cons hjn
  have htake := List.take_succ_eq_append_getElem hjn
  have happ := carryRun_append b 0 (cs.take j) cs[j]
  rw [← htake] at happ
  have hcj := carryRun_snd_le b 0 (cs.take j)
  have hxj : cs[j] + (carryRun b 0 (cs.take j)).2 ≤ (cs.take (j + 1)).sum := by
    rw [htake, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hsub : ∀ m, ∀ c ∈ cs.take m, bitLen c ≤ wD := fun m c hc => hwD c (List.mem_of_mem_take hc)
  have hlen : ∀ m, (cs.take m).length ≤ 2 ^ K0 := fun m => by
    rw [List.length_take]; omega
  have b1 : bitLen (carryRun b 0 (cs.take j)).2 ≤ wD + K0 :=
    bitLen_sum_le _ (hsub j) (hlen j) (by omega)
  have b2 : bitLen ((cs[j] + (carryRun b 0 (cs.take j)).2) / 2 ^ b) ≤ wD + K0 :=
    le_trans (bitLen_mono (Nat.div_le_self _ _)) (bitLen_sum_le _ (hsub (j + 1)) (hlen (j + 1)) hxj)
  have b3 : bitLen cs[j] ≤ wD := hwD _ (List.getElem_mem hjn)
  have b4 : bitLen b ≤ b := bitLen_le_self b
  have v1 : hdrSyms (cs.drop j) ++ rA =
      natSyms cs[j] ++ Sym.mark :: (hdrSyms (cs.drop (j + 1)) ++ rA) := by
    rw [hdrop, hdrSyms_cons]
  have v2 : (carryRun b 0 (cs.take (j + 1))).2 =
      (cs[j] + (carryRun b 0 (cs.take j)).2) / 2 ^ b := by rw [happ]
  have v3 : hdrSyms (carryRun b 0 (cs.take (j + 1))).1.reverse ++ B rL =
      natSyms ((cs[j] + (carryRun b 0 (cs.take j)).2) % 2 ^ b) ++ Sym.mark ::
        (hdrSyms (carryRun b 0 (cs.take j)).1.reverse ++ B rL) := by
    rw [happ]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, hdrSyms_cons]
  simp only [rs1, hj, hij]
  refine (HT_recBody1 hK _ cs[j] (carryRun b 0 (cs.take j)).2 b
    (hdrSyms (cs.drop (j + 1)) ++ rA) (B rCR) (B rT) (B rB)
    (by simp [v1]) (by simp) (by simp) (by simp)).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = hOA
    · subst e1; simp
    by_cases e2 : k = rCR
    · subst e2; simp [v2]
    by_cases e3 : k = rL
    · subst e3; simp [v3]
    by_cases e4 : k = rCT
    · subst e4; simp
    simp [e1, e2, e3, e4]
  · have h2 : C * (2 * bitLen cs[j] + 2 * bitLen (carryRun b 0 (cs.take j)).2 +
        2 * bitLen ((cs[j] + (carryRun b 0 (cs.take j)).2) / 2 ^ b) + b + bitLen b + 6) ≤
        C * (6 * wD + 4 * K0 + 2 * b + 8) := Nat.mul_le_mul_left _ (by omega)
    ring_nf at h2 ⊢
    omega

/-- **Pass 2** (Horner). -/
theorem HT_pass2 (B : H → List Sym) (b : ℕ) (cs : List ℕ) (rA : List Sym) (hrA : TermOK rA) :
    HT [] (rs2 B b cs rA cs.length) (K.loopc rCT2 K.recBody2) (rs2 B b cs rA 0)
      ((C + 1) * (cs.length * (2 * b + 2 + 4) + 2)) := by
  refine HT_loopc' hK rCT2 (Sym.mark :: B rCT2) (termOK_mark' _) cs.length (rs2 B b cs rA)
    (fun i _ => by simp [rs2]) K.recBody2 _ (fun i hi => ?_)
  have hl : (carryRun b 0 cs).1.length = cs.length := length_carryRun b 0 cs
  have hin : i < (carryRun b 0 cs).1.length := by omega
  have hdrop := List.drop_eq_getElem_cons hin
  have htake := List.take_succ_eq_append_getElem hin
  have hlo := carryRun_lt b 0 cs _ (List.getElem_mem hin)
  have v1 : hdrSyms ((carryRun b 0 cs).1.take (i + 1)).reverse ++ B rL =
      natSyms (carryRun b 0 cs).1[i] ++ Sym.mark ::
        (hdrSyms ((carryRun b 0 cs).1.take i).reverse ++ B rL) := by
    rw [htake]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, hdrSyms_cons]
  have v2 : horner b ((carryRun b 0 cs).1.drop i) (carryRun b 0 cs).2 =
      (carryRun b 0 cs).1[i] + horner b ((carryRun b 0 cs).1.drop (i + 1)) (carryRun b 0 cs).2 *
        2 ^ b := by
    rw [hdrop]
    rfl
  refine (HT_recBody2 hK _ (horner b ((carryRun b 0 cs).1.drop (i + 1)) (carryRun b 0 cs).2)
    (carryRun b 0 cs).1[i] b rA (hdrSyms ((carryRun b 0 cs).1.take i).reverse ++ B rL) (B rB)
    hrA hlo (by simp [rs2]) (by simp [rs2, v1]) (by simp [rs2])).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = hOA
    · subst e1; simp [rs2, v2]
    by_cases e2 : k = rL
    · subst e2; simp [rs2]
    by_cases e3 : k = rCT2
    · subst e3; simp [rs2]
    simp [rs2, e1, e2, e3]
  · have h2 : C * (b + bitLen b + 1) ≤ C * (2 * b + 2) :=
      Nat.mul_le_mul_left _ (by have := bitLen_le_self b; omega)
    ring_nf at h2 ⊢
    omega

end Kit

#assert_std_axioms natSyms_zero hdrSyms_cons Kit.HT_loopc' Kit.HT_pass1 Kit.HT_pass2

end WP.W9h
