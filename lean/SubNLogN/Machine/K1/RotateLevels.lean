/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateFiber

/-!
# K1, K4-ctl (`K1/RotateLevels.lean`): the nested loops of the controlled rotation

**Scope (honest summary).** Proved (no `sorry`) `Runs` rules for the loop levels of the
controlled rotation, shape `[np] × [q^{b1}] × [n1] × [q^{b2}] × [n2] × [q^b] × [s]`:
* `lvN2`: `n2` consecutive fibers with fixed controls (`nLoop` on the counter `n2`);
* `lvC2`: the `q^{b2}` values of the control `c2` (`powLoop` on `b2`; `c2` counted on `C2`);
* `lvN1`: `n1` repetitions of `lvC2`;
* `lvC1`: the `q^{b1}` values of the control `c1` (`powLoop` on `b1`; `c1` counted on `C1`).
Every level processes a run of consecutive fibers `c0, c0 + 1, …` (fiber `c` is
`chunk (s·q^b) c v`) and stages their rotations `G c` (reversed) on `U`; its cost is at most a
constant times the volume `volR c0 m` of the fibers it processes.

The controls of fiber `c` are those read by `rotCtlInvAddr` (`offAt`); each level passes the
corresponding index identity down (`hctl` hypotheses), discharged at the top by `offAt_idx`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Fibers, outputs, volumes -/

section Global

variable (q b1 n1 b2 n2 b s : ℕ) (off : ℕ → ℕ → ℕ → ℕ) (v : List (List Bool))

/-- Output of fiber `c`: its rotation by the offset of its controls. -/
def gOut (c : ℕ) : List (List Bool) :=
  rotB (q ^ b) s (offAt (q ^ b1) n1 (q ^ b2) n2 (off b) c) (chunk (s * q ^ b) c v)

/-- Volume of the fibers `c0, …, c0 + m - 1`. -/
def volR (c0 m : ℕ) : ℕ := ((List.range m).map fun i => vol (chunk (s * q ^ b) (c0 + i) v)).sum

end Global

theorem volR_add (q b s : ℕ) (v : List (List Bool)) (c0 a a' : ℕ) :
    volR q b s v c0 (a + a') = volR q b s v c0 a + volR q b s v (c0 + a) a' := by
  simp only [volR, List.range_add, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Nat.add_assoc]

theorem volR_mul (q b s : ℕ) (v : List (List Bool)) (c0 m : ℕ) :
    ∀ k, ((List.range k).map fun i => volR q b s v (c0 + i * m) m).sum =
      volR q b s v c0 (k * m)
  | 0 => by simp [volR]
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, volR_mul q b s v c0 m k, Nat.succ_mul,
      volR_add]
    simp

theorem volR_one (q b s : ℕ) (v : List (List Bool)) (c : ℕ) :
    volR q b s v c 1 = vol (chunk (s * q ^ b) c v) := by
  simp [volR]

/-- Each fiber in range has at least `s·q^b` symbols. -/
theorem volR_ge (q b s : ℕ) (v : List (List Bool)) (c0 m NF : ℕ)
    (hv : v.length = NF * (s * q ^ b)) (hm : c0 + m ≤ NF) :
    m * (s * q ^ b) ≤ volR q b s v c0 m := by
  induction m with
  | zero => simp [volR]
  | succ m ih =>
    rw [volR_add, volR_one, Nat.succ_mul]
    have h1 := ih (by omega)
    have h2 : (chunk (s * q ^ b) (c0 + m) v).length = s * q ^ b :=
      length_chunk (by rw [hv]; exact Nat.mul_le_mul_right _ (by omega))
    have h3 := length_le_vol (chunk (s * q ^ b) (c0 + m) v)
    omega

/-- Volume of all fibers. -/
theorem volR_all (q b s : ℕ) (v : List (List Bool)) (NF : ℕ)
    (hv : v.length = NF * (s * q ^ b)) : volR q b s v 0 NF = vol v := by
  have h := sum_vol_chunk (s * q ^ b) v NF
  simp only [volR, Nat.zero_add]
  rw [h, ← hv, List.take_length]

theorem vol_rotB (Q s o : ℕ) (f : List (List Bool)) : vol (rotB Q s o f) = vol f := by
  rw [rotB, vol_append, Nat.add_comm, ← vol_append, List.take_append_drop]

/-! ## Absorbing the offset routine's cost -/

/-- Per-symbol cost constant of a fiber, including the offset routine (`Co`, exponent `J`)
absorbed by the fiber volume `≥ 2^b` (controls with at most `cb·b` radix-`q` digits). -/
def fibK0 (q cb J Co : ℕ) : ℕ :=
  Co * ((1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J)) + fibK q

theorem bitLen_lt_pow (q n c : ℕ) (hc : c < q ^ n) : bitLen c ≤ n * bitLen q := by
  have h1 : q < 2 ^ bitLen q := TMFw.W3s.lt_two_pow_bitLen q
  have h2 : q ^ n ≤ 2 ^ (n * bitLen q) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left h1.le n
  exact (TMFw.W3s.bitLen_le_iff _ _).2 (lt_of_lt_of_le hc h2)

/-- **Fiber cost absorption.** -/
theorem fib_cost_le (q cb J Co b b1 b2 c1 c2 s : ℕ) (hq : 2 ≤ q) (hc1 : c1 < q ^ b1)
    (hc2 : c2 < q ^ b2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b) (f : List (List Bool))
    (hs1 : 1 ≤ s) (hf : f.length = q ^ b * s) :
    Co * (b + bitLen c1 + bitLen c2 + 1) ^ J + fibK q * vol f ≤ fibK0 q cb J Co * vol f := by
  have e1 : bitLen c1 ≤ cb * b * bitLen q :=
    (bitLen_lt_pow q b1 c1 hc1).trans (Nat.mul_le_mul_right _ hb1)
  have e2 : bitLen c2 ≤ cb * b * bitLen q :=
    (bitLen_lt_pow q b2 c2 hc2).trans (Nat.mul_le_mul_right _ hb2)
  have e3 : b + bitLen c1 + bitLen c2 + 1 ≤ (1 + 2 * cb * bitLen q) * (b + 1) := by
    nlinarith
  have e4 : (b + bitLen c1 + bitLen c2 + 1) ^ J ≤
      (1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b) := by
    calc (b + bitLen c1 + bitLen c2 + 1) ^ J ≤ ((1 + 2 * cb * bitLen q) * (b + 1)) ^ J :=
          Nat.pow_le_pow_left e3 J
      _ = (1 + 2 * cb * bitLen q) ^ J * (b + 1) ^ J := by rw [mul_pow]
      _ ≤ (1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow J b)
  have e5 : 2 ^ b ≤ vol f := by
    have h1 : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
    have h2 : q ^ b ≤ q ^ b * s := Nat.le_mul_of_pos_right _ hs1
    have h3 := length_le_vol f
    omega
  have e6 : Co * (b + bitLen c1 + bitLen c2 + 1) ^ J ≤
      Co * ((1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J)) * vol f := by
    calc Co * (b + bitLen c1 + bitLen c2 + 1) ^ J
        ≤ Co * ((1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J * 2 ^ b)) :=
          Nat.mul_le_mul_left _ e4
      _ = Co * ((1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J)) * 2 ^ b := by ring
      _ ≤ Co * ((1 + 2 * cb * bitLen q) ^ J * (J.factorial * 2 ^ J)) * vol f :=
          Nat.mul_le_mul_left _ e5
  unfold fibK0
  rw [Nat.add_mul]
  omega

/-! ## Level `n2`: `n2` fibers with fixed controls -/

section LvN2

variable {Eo Ro : Type} [DecidableEq Eo]

/-- `n2` fibers with fixed controls. -/
def lvN2 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  nLoop rlO rN2 rN2c rTm (fibProg q Po)

theorem closed_lvN2 (q : ℕ) {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (h : Po.Closed) :
    (lvN2 q Po).Closed :=
  closed_nLoop _ _ _ _ (closed_fibProg q h)

/-- Cost factor of the `n2` level. -/
def lvK1 (q cb J Co : ℕ) : ℕ := fibK0 q cb J Co + 41

theorem runs_lvN2 {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po)
    (q cb b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b)
    (hv : v.length = NF * (s * q ^ b)) (hoffQ : ∀ c1 c2, off b c1 c2 < q ^ b)
    (B : RotL Eo → List Sym) (c0 c1 c2 : ℕ) (rb r1 r2 rs rn2 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hr2 : TermOK r2) (hrs : TermOK rs)
    (hrn2 : TermOK rn2) (hbS : B rB = natSyms b ++ rb) (hC1 : B rC1 = natSyms c1 ++ r1)
    (hC2 : B rC2 = natSyms c2 ++ r2) (hsS : B rS = natSyms s ++ rs)
    (hN2 : B rN2 = natSyms n2 ++ rn2) (hc1 : c1 < q ^ b1) (hc2 : c2 < q ^ b2)
    (hc0 : c0 + n2 ≤ NF)
    (hctl : ∀ i < n2, offAt (q ^ b1) n1 (q ^ b2) n2 (off b) (c0 + i) = off b c1 c2)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvN2 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + n2) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 n2)).reverse ++ U0))
      (fun _ => True) (lvK1 q cb J Co * volR q b s v c0 n2) := by
  set F := s * q ^ b with hF
  have hlen : ∀ j, j < n2 → (chunk F (c0 + j) v).length = q ^ b * s := fun j hj => by
    rw [length_chunk (by rw [hv]; exact Nat.mul_le_mul_right _ (by omega)), hF, Nat.mul_comm]
  set St : ℕ → RotL Eo → List Sym := fun j => fst B (arrSyms (v.drop ((c0 + j) * F)) ++ rest)
    O0 H0 H20 ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 j)).reverse ++ U0) with hSt
  have r := runs_nLoop (rlO (Ro := Ro)) (ns := rN2) (Kc := rN2c) (t := rTm) (by simp) (by simp)
    (by simp) (fibProg q Po) St n2 rn2 hrn2
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hN2])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun j => Co * (b + bitLen c1 + bitLen c2 + 1) ^ J + fibK q * vol (chunk F (c0 + j) v))
    (fun j hj => by
      have hpre : Function.update (St j) rN2c
          (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c) =
          fst (Function.update B rN2c (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c))
            (arrSyms (chunk F (c0 + j) v ++ v.drop ((c0 + j + 1) * F)) ++ rest) O0 H0 H20
            ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 j)).reverse ++ U0) := by
        rw [← drop_chunk]
        simp only [hSt]
        rw [fst_upd_comm] <;> simp
      rw [hpre]
      have hm := runs_fib_fst hO q hq
        (Function.update B rN2c (natSyms (n2 - (j + 1)) ++ Sym.mark :: St 0 rN2c))
        (chunk F (c0 + j) v) (v.drop ((c0 + j + 1) * F)) rest b c1 c2 s rb r1 r2 rs hrb hr1 hr2
        hrs hs1 (hlen j hj) (hoffQ c1 c2) (by simp [hbS]) (by simp [hC1]) (by simp [hC2])
        (by simp [hsS]) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 j)).reverse ++ U0)
      refine WP.W9comp.runs_congr hm ?_
      have hG : gOut q b1 n1 b2 n2 b s off v (c0 + j) =
          rotB (q ^ b) s (off b c1 c2) (chunk F (c0 + j) v) := by
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
      Co * (b + bitLen c1 + bitLen c2 + 1) ^ J + fibK q * vol (chunk F (c0 + j) v)).sum ≤
      fibK0 q cb J Co * volR q b s v c0 n2 := by
    simp only [volR, ← hF]
    rw [listSum_range, listSum_range, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj =>
      fib_cost_le q cb J Co b b1 b2 c1 c2 s hq hc1 hc2 hb1 hb2 _ hs1
        (hlen j (Finset.mem_range.1 hj))
  have hge := volR_ge q b s v c0 n2 NF hv hc0
  have hF1 : 1 ≤ F := Nat.mul_pos hs1 (Nat.pow_pos (by omega : 0 < q))
  have hn2V : n2 ≤ volR q b s v c0 n2 := le_trans (Nat.le_mul_of_pos_right _ hF1) hge
  have hbn := bitLen_le_self' n2
  unfold lvK1
  rw [Nat.add_mul]
  omega

end LvN2

/-! ## Cost bookkeeping of an enumeration level -/

/-- The cost of a `powLoop` level whose leaf `k` runs a sub-level of `n2` fibers (cost factor
`K`) and one counter increment from `k`: at most `(K + 6·cb·bitLen q + 2·bitLen q + 4q + 120)`
times the volume. -/
theorem lvC_cost_arith (q cb b b2 n2 s : ℕ) (v : List (List Bool)) (c0 NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn2 : 1 ≤ n2) (hb2 : b2 ≤ cb * b)
    (hv : v.length = NF * (s * q ^ b)) (hc0 : c0 + q ^ b2 * n2 ≤ NF) (K : ℕ) :
    1 + ((enumE q (fun k => K * volR q b s v (c0 + k * n2) n2 + (6 * ones (encodeNat k) + 9))
      b2 0 + 19 * b2 + 13 * bitLen b2 + 17) + (2 * (encodeNat (q ^ b2)).length + 2)) ≤
      (K + 6 * cb * bitLen q + 2 * bitLen q + 4 * q + 120) * volR q b s v c0 (q ^ b2 * n2) := by
  have hQb : b + 1 ≤ q ^ b := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
    omega
  have hF : q ^ b ≤ s * q ^ b := Nat.le_mul_of_pos_left _ hs1
  -- each leaf has volume at least `b + 1`
  have hVk : ∀ k, k < q ^ b2 → b + 1 ≤ volR q b s v (c0 + k * n2) n2 := by
    intro k hk
    have h1 : (k + 1) * n2 ≤ q ^ b2 * n2 := Nat.mul_le_mul_right _ hk
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 := volR_ge q b s v (c0 + k * n2) n2 NF hv (by omega)
    have h3 : s * q ^ b ≤ n2 * (s * q ^ b) := Nat.le_mul_of_pos_left _ hn2
    omega
  have hT : ∀ k, k < q ^ b2 →
      K * volR q b s v (c0 + k * n2) n2 + (6 * ones (encodeNat k) + 9) ≤
        (K + 6 * cb * bitLen q + 9) * volR q b s v (c0 + k * n2) n2 + 0 := by
    intro k hk
    have h1 : ones (encodeNat k) ≤ cb * b * bitLen q :=
      (ones_le_length _).trans ((bitLen_lt_pow q b2 k hk).trans (Nat.mul_le_mul_right _ hb2))
    have h2 := hVk k hk
    have h3 : 6 * (cb * b * bitLen q) + 9 ≤
        (6 * cb * bitLen q + 9) * volR q b s v (c0 + k * n2) n2 := by
      have : 6 * (cb * b * bitLen q) + 9 ≤ (6 * cb * bitLen q + 9) * (b + 1) := by nlinarith
      exact this.trans (Nat.mul_le_mul_left _ h2)
    nlinarith
  have henum := enumE_le q hq _ (fun k => volR q b s v (c0 + k * n2) n2)
    (K + 6 * cb * bitLen q + 9) 0 (q ^ b2) hT b2 0 (by simp)
  have hw : wsum (fun k => volR q b s v (c0 + k * n2) n2) 0 (q ^ b2) =
      volR q b s v c0 (q ^ b2 * n2) := by
    simp only [wsum, Nat.zero_add]
    exact volR_mul q b s v c0 n2 (q ^ b2)
  rw [hw] at henum
  have hV := volR_ge q b s v c0 (q ^ b2 * n2) NF hv hc0
  have hQ2 : q ^ b2 ≤ volR q b s v c0 (q ^ b2 * n2) := by
    have h1 : q ^ b2 ≤ q ^ b2 * n2 := Nat.le_mul_of_pos_right _ hn2
    have h2 : q ^ b2 * n2 ≤ q ^ b2 * n2 * (s * q ^ b) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos hs1 (Nat.pow_pos (by omega : 0 < q)))
    omega
  have hb2Q : b2 + 1 ≤ q ^ b2 := by
    have h1 : b2 < 2 ^ b2 := Nat.lt_two_pow_self
    have h2 : 2 ^ b2 ≤ q ^ b2 := Nat.pow_le_pow_left hq b2
    omega
  have hbl := bitLen_le_self' b2
  have hblQ : (encodeNat (q ^ b2)).length ≤ q ^ b2 := bitLen_le_self' (q ^ b2)
  have hqV : q * q ^ b2 ≤ q * volR q b s v c0 (q ^ b2 * n2) := Nat.mul_le_mul_left _ hQ2
  nlinarith [henum, hQ2, hb2Q, hbl, hblQ, hqV]

/-! ## Level `c2`: the `q^{b2}` values of the second control -/

section LvC2

variable {Eo Ro : Type} [DecidableEq Eo]

omit [DecidableEq Eo] in
theorem closed_inc_lift (k t : RotL Eo) : ((inc k t).liftRegs (rlO (Ro := Ro))).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, Lib.scanBody, moveBits,
      moveBitsBody, pushC, popR, pushR, restoreR, skip])

/-- Leaf of the `c2` enumeration: `n2` fibers, then `c2 := c2 + 1`. -/
def leafC2 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  .seq (lvN2 q Po) (rwk (inc rC2 rTm))

/-- The `c2` level: `q^{b2}` leaves, `c2` counted on `C2` above a guard. -/
def lvC2 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  .seq (rwk (pushC rC2 .mark)) (.seq (powLoop rlO q rB2 rL2 rKb rTm (leafC2 q Po))
    (rwk (dropBits rC2)))

theorem closed_lvC2 (q : ℕ) {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (h : Po.Closed) :
    (lvC2 q Po).Closed :=
  ⟨closed_pushC_lift _ _ _, closed_powLoop _ _ _ _ _ _ ⟨closed_lvN2 q h, closed_inc_lift _ _⟩,
    closed_dropBits_lift _ _⟩

/-- Cost factor of the `c2` level. -/
def lvK2 (q cb J Co : ℕ) : ℕ :=
  lvK1 q cb J Co + 6 * cb * bitLen q + 2 * bitLen q + 4 * q + 120

theorem runs_lvC2 {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b) (hb2 : b2 ≤ cb * b)
    (hv : v.length = NF * (s * q ^ b)) (hoffQ : ∀ c1 c2, off b c1 c2 < q ^ b)
    (B : RotL Eo → List Sym) (c0 c1 : ℕ) (rb r1 rs rn2 rb2 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hrs : TermOK rs) (hrn2 : TermOK rn2)
    (hrb2 : TermOK rb2) (hbS : B rB = natSyms b ++ rb) (hC1 : B rC1 = natSyms c1 ++ r1)
    (hsS : B rS = natSyms s ++ rs) (hN2 : B rN2 = natSyms n2 ++ rn2)
    (hB2 : B rB2 = natSyms b2 ++ rb2) (hc1 : c1 < q ^ b1) (hc0 : c0 + q ^ b2 * n2 ≤ NF)
    (hctl : ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off b) (c0 + k * n2 + i) = off b c1 k)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvC2 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + q ^ b2 * n2) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 (q ^ b2 * n2))).reverse ++ U0))
      (fun _ => True) (lvK2 q cb J Co * volR q b s v c0 (q ^ b2 * n2)) := by
  set F := s * q ^ b with hF
  set G := gOut q b1 n1 b2 n2 b s off v with hG
  set St : ℕ → RotL Eo → List Sym := fun k =>
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
    (fun k => lvK1 q cb J Co * volR q b s v (c0 + k * n2) n2 + (6 * ones (encodeNat k) + 9))
    (fun k hk => by
      have hkn : c0 + k * n2 + n2 ≤ NF := by
        have : (k + 1) * n2 ≤ q ^ b2 * n2 := Nat.mul_le_mul_right _ hk
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hm1 := runs_lvN2 hO q cb b1 n1 b2 n2 b s v rest NF hq hs1 hn2 hb1 hb2 hv hoffQ
        (Function.update (Function.update B rC2 (natSyms k ++ Sym.mark :: B rC2)) rL2
          (Sym.mark :: B rL2))
        (c0 + k * n2) c1 k rb r1 (Sym.mark :: B rC2) rs rn2 hrb hr1 (TermOK.cons rfl _) hrs
        hrn2 (by simp [hbS]) (by simp [hC1]) (by simp) (by simp [hsS]) (by simp [hN2]) hc1 hk
        hkn (fun i hi => hctl k hk i hi) O0 H0 H20 ((arrSyms (outR G c0 (k * n2))).reverse ++ U0)
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
  exact lvC_cost_arith q cb b b2 n2 s v c0 NF hq hs1 hn2 hb2 hv hc0 (lvK1 q cb J Co)

end LvC2

/-! ## Level `n1`: `n1` repetitions of the `c2` level -/

section LvN1

variable {Eo Ro : Type} [DecidableEq Eo]

/-- `n1` repetitions of the `c2` level. -/
def lvN1 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  nLoop rlO rN1 rN1c rTm (lvC2 q Po)

theorem closed_lvN1 (q : ℕ) {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (h : Po.Closed) :
    (lvN1 q Po).Closed :=
  closed_nLoop _ _ _ _ (closed_lvC2 q h)

/-- Cost factor of the `n1` level. -/
def lvK3 (q cb J Co : ℕ) : ℕ := lvK2 q cb J Co + 41

theorem runs_lvN1 {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hv : v.length = NF * (s * q ^ b))
    (hoffQ : ∀ c1 c2, off b c1 c2 < q ^ b)
    (B : RotL Eo → List Sym) (c0 c1 : ℕ) (rb r1 rs rn2 rb2 rn1 : List Sym)
    (hrb : TermOK rb) (hr1 : TermOK r1) (hrs : TermOK rs) (hrn2 : TermOK rn2)
    (hrb2 : TermOK rb2) (hrn1 : TermOK rn1) (hbS : B rB = natSyms b ++ rb)
    (hC1 : B rC1 = natSyms c1 ++ r1) (hsS : B rS = natSyms s ++ rs)
    (hN2 : B rN2 = natSyms n2 ++ rn2) (hB2 : B rB2 = natSyms b2 ++ rb2)
    (hN1 : B rN1 = natSyms n1 ++ rn1) (hc1 : c1 < q ^ b1)
    (hc0 : c0 + n1 * (q ^ b2 * n2) ≤ NF)
    (hctl : ∀ y < n1, ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off b) (c0 + y * (q ^ b2 * n2) + k * n2 + i) = off b c1 k)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvN1 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + n1 * (q ^ b2 * n2)) * (s * q ^ b))) ++ rest) O0 H0 H20
        ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0 (n1 * (q ^ b2 * n2)))).reverse ++ U0))
      (fun _ => True) (lvK3 q cb J Co * volR q b s v c0 (n1 * (q ^ b2 * n2))) := by
  set F := s * q ^ b with hF
  set m := q ^ b2 * n2 with hm
  set G := gOut q b1 n1 b2 n2 b s off v with hG
  set St : ℕ → RotL Eo → List Sym := fun j => fst B (arrSyms (v.drop ((c0 + j * m) * F)) ++ rest)
    O0 H0 H20 ((arrSyms (outR G c0 (j * m))).reverse ++ U0) with hSt
  have r := runs_nLoop (rlO (Ro := Ro)) (ns := rN1) (Kc := rN1c) (t := rTm) (by simp) (by simp)
    (by simp) (lvC2 q Po) St n1 rn1 hrn1
    (by simp only [hSt]; rw [fst_apply_ne] <;> simp [hN1])
    (by simp only [hSt]; rw [fst_apply_ne, fst_apply_ne] <;> simp)
    (fun j => lvK2 q cb J Co * volR q b s v (c0 + j * m) m)
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
      have hm1 := runs_lvC2 hO hPoC q cb b1 n1 b2 n2 b s v rest NF hq hs1 hn2 hb1 hb2 hv hoffQ
        (Function.update B rN1c (natSyms (n1 - (j + 1)) ++ Sym.mark :: St 0 rN1c))
        (c0 + j * m) c1 rb r1 rs rn2 rb2 hrb hr1 hrs hrn2 hrb2 (by simp [hbS]) (by simp [hC1])
        (by simp [hsS]) (by simp [hN2]) (by simp [hB2]) hc1 hjm
        (fun k hk i hi => hctl j hj k hk i hi) O0 H0 H20
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
  have hsum : ((List.range n1).map fun j => lvK2 q cb J Co * volR q b s v (c0 + j * m) m).sum =
      lvK2 q cb J Co * volR q b s v c0 (n1 * m) := by
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

end LvN1

/-! ## Level `c1`: the `q^{b1}` values of the first control -/

section LvC1

variable {Eo Ro : Type} [DecidableEq Eo]

/-- Leaf of the `c1` enumeration: the `n1` level, then `c1 := c1 + 1`. -/
def leafC1 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  .seq (lvN1 q Po) (rwk (inc rC1 rTm))

/-- The `c1` level: `q^{b1}` leaves, `c1` counted on `C1` above a guard. -/
def lvC1 (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  .seq (rwk (pushC rC1 .mark)) (.seq (powLoop rlO q rB1 rL1 rKb rTm (leafC1 q Po))
    (rwk (dropBits rC1)))

theorem closed_lvC1 (q : ℕ) {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (h : Po.Closed) :
    (lvC1 q Po).Closed :=
  ⟨closed_pushC_lift _ _ _, closed_powLoop _ _ _ _ _ _ ⟨closed_lvN1 q h, closed_inc_lift _ _⟩,
    closed_dropBits_lift _ _⟩

/-- Cost factor of the `c1` level. -/
def lvK4 (q cb J Co : ℕ) : ℕ :=
  lvK3 q cb J Co + 6 * cb * bitLen q + 2 * bitLen q + 4 * q + 120

theorem runs_lvC1 {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po)
    (hPoC : Po.Closed)
    (q cb b1 n1 b2 n2 b s : ℕ) (v : List (List Bool)) (rest : List Sym) (NF : ℕ)
    (hq : 2 ≤ q) (hs1 : 1 ≤ s) (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hb1 : b1 ≤ cb * b)
    (hb2 : b2 ≤ cb * b) (hv : v.length = NF * (s * q ^ b))
    (hoffQ : ∀ c1 c2, off b c1 c2 < q ^ b)
    (B : RotL Eo → List Sym) (c0 : ℕ) (rb rs rn2 rb2 rn1 rb1 : List Sym)
    (hrb : TermOK rb) (hrs : TermOK rs) (hrn2 : TermOK rn2) (hrb2 : TermOK rb2)
    (hrn1 : TermOK rn1) (hrb1 : TermOK rb1) (hbS : B rB = natSyms b ++ rb)
    (hsS : B rS = natSyms s ++ rs) (hN2 : B rN2 = natSyms n2 ++ rn2)
    (hB2 : B rB2 = natSyms b2 ++ rb2) (hN1 : B rN1 = natSyms n1 ++ rn1)
    (hB1 : B rB1 = natSyms b1 ++ rb1)
    (hc0 : c0 + q ^ b1 * (n1 * (q ^ b2 * n2)) ≤ NF)
    (hctl : ∀ k1 < q ^ b1, ∀ y < n1, ∀ k < q ^ b2, ∀ i < n2,
      offAt (q ^ b1) n1 (q ^ b2) n2 (off b)
        (c0 + k1 * (n1 * (q ^ b2 * n2)) + y * (q ^ b2 * n2) + k * n2 + i) = off b k1 k)
    (O0 H0 H20 U0 : List Sym) :
    Runs (lvC1 q Po) (fst B (arrSyms (v.drop (c0 * (s * q ^ b))) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (v.drop ((c0 + q ^ b1 * (n1 * (q ^ b2 * n2))) * (s * q ^ b))) ++ rest)
        O0 H0 H20 ((arrSyms (outR (gOut q b1 n1 b2 n2 b s off v) c0
          (q ^ b1 * (n1 * (q ^ b2 * n2))))).reverse ++ U0))
      (fun _ => True) (lvK4 q cb J Co * volR q b s v c0 (q ^ b1 * (n1 * (q ^ b2 * n2)))) := by
  set F := s * q ^ b with hF
  set m := n1 * (q ^ b2 * n2) with hm
  set G := gOut q b1 n1 b2 n2 b s off v with hG
  set St : ℕ → RotL Eo → List Sym := fun k =>
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
    (fun k => lvK3 q cb J Co * volR q b s v (c0 + k * m) m + (6 * ones (encodeNat k) + 9))
    (fun k hk => by
      have hkm : c0 + k * m + n1 * (q ^ b2 * n2) ≤ NF := by
        have : (k + 1) * m ≤ q ^ b1 * m := Nat.mul_le_mul_right _ hk
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hm1' := runs_lvN1 hO hPoC q cb b1 n1 b2 n2 b s v rest NF hq hs1 hn1 hn2 hb1 hb2 hv
        hoffQ
        (Function.update (Function.update B rC1 (natSyms k ++ Sym.mark :: B rC1)) rL1
          (Sym.mark :: B rL1))
        (c0 + k * m) k rb (Sym.mark :: B rC1) rs rn2 rb2 rn1 hrb (TermOK.cons rfl _) hrs hrn2
        hrb2 hrn1 (by simp [hbS]) (by simp) (by simp [hsS]) (by simp [hN2]) (by simp [hB2])
        (by simp [hN1]) hk hkm (fun y hy k' hk' i hi => hctl k hk y hy k' hk' i hi) O0 H0 H20
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
  exact lvC_cost_arith q cb b b1 m s v c0 NF hq hs1 hm1 hb1 hv hc0 (lvK3 q cb J Co)

end LvC1

end SubNLogN.Machine.K1.Rot
