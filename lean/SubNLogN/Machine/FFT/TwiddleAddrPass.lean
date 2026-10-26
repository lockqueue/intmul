/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrAxis

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrPass.lean`): the two passes over the axes

**Scope (honest summary).** Programs and host rules, all proved (no `sorry`):
* pass 1 (`tcd kC1 (p1Body I)`, `HT.pass1`): walk the exponent fields `a_0, …, a_{D-1}` of the
  header, parking each field. This computes `m₀ = ∑ a_i` on `kM` and `longCount ℓ a` on `kLc`.
* pass 2 (`tcd kIx (axBody I)`, `HT.pass2`): walk back from `a_{D-1}` to `a_0`, un-parking each
  field. It keeps the long rank of axis `i` on `kR` and adds the term of axis `i` to `kAcc`.
  The accumulator ends at `∑_{i<D} tmN …` (`TwiddleAddrMath.lean`).
The loop states are `p1St` and `p2St`. The header stack holds `hdrSyms (drop k (ofFn a)) ++ hrest`,
and the park holds `pkS (fx ++ take k (ofFn a))`.
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine.FFT.Phase SubNLogN.Math.Walsh

theorem termOK_pkS (l : List ℕ) : TermOK (pkS l) := by
  unfold pkS
  cases l.reverse with
  | nil => exact TermOK.nil
  | cons x t =>
    simp only [List.flatMap_cons, List.cons_append]
    exact termOK_mark _

theorem sum_take_le {D : ℕ} (a : Fin D → ℕ) (k : ℕ) :
    ((List.ofFn a).take k).sum ≤ addrBits a := by
  have := List.sum_take_add_sum_drop (List.ofFn a) k
  unfold addrBits
  omega

/-! ## Programs -/

section Programs

variable (I : TI)

/-- `kLc += 1` iff `a_k = ℓ`. -/
def incIf : TP I := tcmIf I xA kL (fun o => decide (o = Ordering.eq)) (tic I kLc) (tskip I)

/-- The body of pass 1: read `a_k`, `kM += a_k`, `kLc += [a_k = ℓ]`, park the field. -/
def p1Body : TP I :=
  (tcp I sHd xA).seq <| (accAdd I xA kM).seq <| (incIf I).seq <| (tdr I xA).seq (mvF I sHd kPK)

theorem incIf_closed : (incIf I).Closed :=
  tcmIf_closed I _ _ _ _ _ (callI_closed _ _ _ _) trivial

theorem p1Body_closed : (p1Body I).Closed :=
  ⟨callI_closed _ _ _ _, accAdd_closed I _ _, incIf_closed I, callI_closed _ _ _ _,
    mvF_closed I _ _⟩

end Programs

/-! ## Loop states -/

/-- Pass-1 state with counter `j` (`D - j` fields parked). -/
def p1St (B : TL → List Sym) (as fx : List ℕ) (hrest : List Sym) (ℓ D j : ℕ) :
    TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B
    sHd (hdrSyms (as.drop (D - j)) ++ hrest)) kPK (pkS (fx ++ as.take (D - j))))
    kM (natSyms (as.take (D - j)).sum ++ [])) kLc (natSyms ((as.take (D - j)).count ℓ) ++ []))
    kC1 (natSyms j ++ [])

/-- The term of axis `j` (exponent `a_j`, long rank `longRank ℓ a j`). -/
def tmF (ℓ K D L m n v : ℕ) (a : Fin D → ℕ) (j : ℕ) : ℕ :=
  tmN ℓ K D L m n v (aN a j) (((List.ofFn a).take j).count ℓ) j

/-- Pass-2 state with counter `i` (axes `i, …, D-1` done, `i` fields still parked). -/
def p2St (B : TL → List Sym) (as fx : List ℕ) (hrest : List Sym) (ℓ D : ℕ) (tm : ℕ → ℕ)
    (i : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B
    sHd (hdrSyms (as.drop i) ++ hrest)) kPK (pkS (fx ++ as.take i)))
    kR (natSyms ((as.take i).count ℓ))) kIx (natSyms i ++ []))
    kAcc (natSyms (∑ j ∈ Finset.Ico i D, tm j) ++ [])

/-! ## Host rules -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

theorem HT.incIf (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {x ℓ c : ℕ}
    {rx rc : List Sym} (hx : B xA = natSyms x ++ rx) (hrx : TermOK rx) (hL : B kL = natSyms ℓ)
    (hc : B kLc = natSyms c ++ rc) (hrc : TermOK rc) (bx : bitLen x ≤ Q) (bl : bitLen ℓ ≤ Q)
    (bc : bitLen c ≤ Q) :
    HT [] B (incIf I) (Function.update B kLc (natSyms (c + (if x = ℓ then 1 else 0)) ++ rc))
      (2 * U C KM Q + 2) := by
  unfold SubNLogN.Machine.FFT.TwAddr.incIf
  refine (HT.tcmIf hI Q xA kL (by decide) B _ x ℓ rx [] hrx TermOK.nil hx
    (by rw [hL, List.append_nil]) bx bl _ _ _ (U C KM Q + 1) ?_ ?_).mono (by omega)
  · intro he
    have hxl : x = ℓ := (ordEq_iff _ _).mp (of_decide_eq_true he)
    rw [if_pos hxl]
    exact (HT.tic hI Q kLc B c rc hrc hc bc).mono (by omega)
  · intro hne
    have hxl : x ≠ ℓ := fun h => (of_decide_eq_false hne) ((ordEq_iff _ _).mpr h)
    rw [if_neg hxl, Nat.add_zero, ← hc, Function.update_eq_self]
    exact (HT.tskip B).mono (by omega)

set_option maxHeartbeats 1000000 in
theorem HT.p1Body (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {x ℓ s c : ℕ}
    {tl rs rc : List Sym} (hH : B sHd = natSyms x ++ Sym.mark :: tl) (hL : B kL = natSyms ℓ)
    (hM : B kM = natSyms s ++ rs) (hrs : TermOK rs) (hC : B kLc = natSyms c ++ rc)
    (hrc : TermOK rc) (hxA : TermOK (B xA)) (hxN : TermOK (B xN)) (bx : bitLen x ≤ Q)
    (bl : bitLen ℓ ≤ Q) (bs : bitLen s ≤ Q) (bxs : bitLen (x + s) ≤ Q) (bc : bitLen c ≤ Q) :
    HT [] B (p1Body I)
      (Function.update (Function.update (Function.update (Function.update B
        kM (natSyms (x + s) ++ rs)) kLc (natSyms (c + (if x = ℓ then 1 else 0)) ++ rc))
        sHd tl) kPK (Sym.mark :: (natSyms x ++ B kPK)))
      (10 * U C KM Q + 4) := by
  refine (HT.seq (HT.tcp hI Q sHd xA (by decide) B x (Sym.mark :: tl) (termOK_mark _) hH bx) <|
    HT.seq (HT.accAdd hI Q xA kM (by decide) _ x s (B xA) rs hxA hrs (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hM]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hxN) bx bs bxs) <|
    HT.seq (HT.incIf hI Q _ (x := x) (ℓ := ℓ) (c := c) (rx := B xA) (rc := rc) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) hxA (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hL]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hC]) hrc bx bl bc) <|
    HT.seq (HT.tdr hI Q xA _ x (B xA) hxA (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bx) <|
    HT.mvF hI Q sHd kPK (by decide) _ x tl (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hH]) bx).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 2000000 in
theorem HT.pass1 (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {ℓ D w : ℕ}
    (a : Fin D → ℕ) (fx : List ℕ) (hrest : List Sym)
    (hL : B kL = natSyms ℓ) (hxA : TermOK (B xA)) (hxN : TermOK (B xN))
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (hlw : ℓ ≤ w) (hQ : 6 * (addrBits a + w + 1) ≤ Q)
    (hDQ : D ≤ Q) :
    HT [] (p1St B (List.ofFn a) fx hrest ℓ D D)
      (SubNLogN.Machine.FFT.TwAddr.tcd I kC1 (SubNLogN.Machine.FFT.TwAddr.p1Body I))
      (p1St B (List.ofFn a) fx hrest ℓ D 0)
      (D * (10 * U C KM Q + 4 + 2 * U C KM Q + 1) + U C KM Q + 1) := by
  refine HT.tcd hI Q kC1 [] TermOK.nil (p1St B (List.ofFn a) fx hrest ℓ D) (fun j => by
    unfold p1St; simp only [Function.update_self]) (SubNLogN.Machine.FFT.TwAddr.p1Body I)
    (10 * U C KM Q + 4) D hDQ (fun j hj => ?_)
  have hk : D - (j + 1) < D := by omega
  have e : D - j = D - (j + 1) + 1 := by omega
  have hx := aN_le a ℓ ha (D - (j + 1))
  have hs := sum_take_le a (D - (j + 1))
  have hs1 := sum_take_le a (D - (j + 1) + 1)
  rw [sum_take_succ a hk] at hs1
  have hcD := count_take_le a ℓ (D - (j + 1))
  have bx : bitLen (aN a (D - (j + 1))) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bl : bitLen ℓ ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bs : bitLen ((List.ofFn a).take (D - (j + 1))).sum ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  have bxs : bitLen (aN a (D - (j + 1)) + ((List.ofFn a).take (D - (j + 1))).sum) ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  have bc : bitLen (((List.ofFn a).take (D - (j + 1))).count ℓ) ≤ Q :=
    le_trans (bitLen_le_self _) (by omega)
  have hH : (Function.update (p1St B (List.ofFn a) fx hrest ℓ D (j + 1)) kC1 (natSyms j ++ []))
      sHd = natSyms (aN a (D - (j + 1))) ++
        Sym.mark :: (hdrSyms ((List.ofFn a).drop (D - (j + 1) + 1)) ++ hrest) := by
    unfold p1St
    simp (config := { failIfUnchanged := false }) (disch := decide) only
      [Function.update_self, Function.update_of_ne]
    rw [drop_ofFn a hk, hdrSyms_cons, List.append_assoc, List.cons_append]
  refine (HT.p1Body hI Q _ (ℓ := ℓ) (s := ((List.ofFn a).take (D - (j + 1))).sum)
    (c := ((List.ofFn a).take (D - (j + 1))).count ℓ) (rs := []) (rc := []) hH (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p1St, Function.update_self, Function.update_of_ne, hL]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p1St, Function.update_self, Function.update_of_ne]) TermOK.nil (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p1St, Function.update_self, Function.update_of_ne]) TermOK.nil (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p1St, Function.update_self, Function.update_of_ne]; exact hxA) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p1St, Function.update_self, Function.update_of_ne]; exact hxN) bx bl bs bxs bc).of_eq ?_ le_rfl
  unfold p1St
  rw [e, count_take_succ a ℓ hk, sum_take_succ a hk, take_succ_ofFn a hk, ← List.append_assoc,
    pkS_append_one, Nat.add_comm (((List.ofFn a).take (D - (j + 1))).sum) (aN a (D - (j + 1)))]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 4000000 in
theorem HT.pass2 (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {ℓ K D L m n v w : ℕ}
    {vr nr : List Sym} (a : Fin D → ℕ) (fx : List ℕ) (hrest : List Sym)
    (hc : CtxAt B ℓ K D L m n v vr nr) (ht : TClean B) (h2 : TermOK (B xP2))
    (hxP : TermOK (B xP)) (hxB : TermOK (B xB)) (hxN : TermOK (B xN)) (hIb : TermOK (B kIb))
    (hLo : TermOK (B xLo)) (hxF : TermOK (B xF)) (hxA : TermOK (B xA)) (hIK0 : B kIK = [])
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hvl : v < ℓ) (hn : n < 2 ^ m)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (hDQ : D ≤ Q) :
    HT [] (p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a) D)
      (SubNLogN.Machine.FFT.TwAddr.tcd I kIx (SubNLogN.Machine.FFT.TwAddr.axBody I))
      (p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a) 0)
      (D * (cAx C KM Q v + 2 * U C KM Q + 1) + U C KM Q + 1) := by
  refine HT.tcd hI Q kIx [] TermOK.nil (p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a))
    (fun i => by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne])
    (SubNLogN.Machine.FFT.TwAddr.axBody I) (cAx C KM Q v) D hDQ (fun i hi => ?_)
  have hx := aN_le a ℓ ha i
  have hRD := count_take_le a ℓ (i + 1)
  have hcnt := count_take_succ a ℓ hi
  have hpos : aN a i = ℓ → 1 ≤ ((List.ofFn a).take (i + 1)).count ℓ := fun h => by
    rw [hcnt, if_pos h]; omega
  have hR' : ((List.ofFn a).take (i + 1)).count ℓ - (if aN a i = ℓ then 1 else 0) =
      ((List.ofFn a).take i).count ℓ := by
    rw [hcnt, Nat.add_sub_cancel]
  have hacc : ∑ j ∈ Finset.Ico (i + 1) D, tmF ℓ K D L m n v a j + 2 ^ ℓ ≤ D * 2 ^ ℓ := by
    have h1 := sum_Ico_le (tmF ℓ K D L m n v a) (2 ^ ℓ) (i + 1) D
      (fun j => le_of_lt (tmN_lt hvl))
    have h3 : (D - (i + 1)) * 2 ^ ℓ + 2 ^ ℓ ≤ D * 2 ^ ℓ := by
      have e3 : (D - (i + 1)) * 2 ^ ℓ + 2 ^ ℓ = (D - (i + 1) + 1) * 2 ^ ℓ := by ring
      rw [e3]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hpk : (Function.update (p2St B (List.ofFn a) fx hrest ℓ D (tmF ℓ K D L m n v a) (i + 1))
      kIx (natSyms i ++ [])) kPK =
      Sym.mark :: (natSyms (aN a i) ++ pkS (fx ++ (List.ofFn a).take i)) := by
    unfold p2St
    simp (config := { failIfUnchanged := false }) (disch := decide) only
      [Function.update_self, Function.update_of_ne]
    rw [take_succ_ofFn a hi, ← List.append_assoc, pkS_append_one]
  refine (HT.axBody hI Q _ (x := aN a i) (R := ((List.ofFn a).take (i + 1)).count ℓ) (i := i)
    (acc := ∑ j ∈ Finset.Ico (i + 1) D, tmF ℓ K D L m n v a j) (ra := [])
    (rpk := pkS (fx ++ (List.ofFn a).take i))
    ((((((hc.upd sHd (by decide) _).upd kPK (by decide) _).upd kR (by decide) _).upd kIx
      (by decide) _).upd kAcc (by decide) _).upd kIx (by decide) _)
    ((((((ht.upd sHd (by decide) _).upd kPK (by decide) _).upd kR (by decide) _).upd kIx
      (by decide) _).upd kAcc (by decide) _).upd kIx (by decide) _)
    (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact h2) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hxP) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hxB) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hxN) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hIb) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hLo) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hxF) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]; exact hxA) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne, List.append_nil]) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne, hIK0]) hpk (termOK_pkS _) (by
      simp (config := { failIfUnchanged := false }) (disch := decide) only
        [p2St, Function.update_self, Function.update_of_ne]) TermOK.nil hP hQ hi hvl hn hacc hx hRD
    hpos).of_eq ?_ le_rfl
  rw [hR']
  unfold p2St
  rw [drop_ofFn a hi, hdrSyms_cons, List.append_assoc, List.cons_append,
    Finset.sum_eq_sum_Ico_succ_bot hi,
    show tmF ℓ K D L m n v a i = tmN ℓ K D L m n v (aN a i) (((List.ofFn a).take i).count ℓ) i
      from rfl]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Rules

end SubNLogN.Machine.FFT.TwAddr
