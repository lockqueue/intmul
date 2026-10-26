/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractSetup
import SubNLogN.Machine.Calculus.FramePassR
import IntMulTM.SpecFacts

/-!
# Lemma A.9 extraction, assembly: the cost bound (`Machine/AppC/C7ExtractAssembleCost.lean`)

**Scope.** Pure arithmetic, everything proved (no `sorry`). For the extraction
kernel `setup ; countdown over the M records ; cleanup` (assembled in `C7ExtractAssemble.lean`,
for `c7Extract_of_parts`), `c7x_cost_le` bounds the sum of

* the setup budget `setupCost xk (vol w) M A` (`C7ExtractSetup.lean`),
* the countdown cost `countdownCost (fun _ => b) M` of `M = w.length` record bodies, each of
  constant cost `b` (`Calculus/FramePassR.lean`), and
* the cleanup cost (`runs_cleanupP`, `C7ExtractAssembleKit.lean`: two pops and twelve
  `dropFW`s of the constants `1, 10, 11, f·K, 2^{fK}, 2^K, 2^{K-1}, 2^ρ, 2^{ρ+1}, f-1, 2^A, A`)

by the extraction budget `Cf · (M (lgVol V + 1)^3 + V + badMax K f M (lgVol V + 1) + 1)` of
`C7ExtractStmt` (`C7RepairDefs.lean`), given the pure inequality `hCf` (an instance of
`C7XCostStmt` with `c = 110`, as proved in `C7ExtractCost.lean`). Paper:
Lemma A.9 (`lem:transfer13`, eq. (`eq:transfer-packed`)) (repair scan `O(A_rect^3)` per record;
counters, rewinds and cleanup fit the same costs). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Implicit facts used (all derived here, not assumed): `vol w = M (R + 1)` for records of width `R`
(`vol_widths`); `opCost xk n = ocost 110 n` when `xk.c = 110`; `2^{fK} ≤ M < 2^A`, hence
`f·K < A` (`fK_lt_size`); `bitLen n = Nat.size n`, so `bitLen (2^k) = k + 1` and `bitLen n ≤ n`.

Plan: (1) rewrite `vol w`, `opCost`, `w.length = M`; (2) `countdownCost_le` with the constant
body sum `M · b`; (3) the cleanup sum is at most `92 + 24 A ≤ 40 · ocost 110 (A + 2)`;
(4) add up and apply `hCf`.
-/

namespace SubNLogN.Machine.AppC.C7XCostAux

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus SubNLogN.Machine.AppC.C7ExtractAux
  SubNLogN.Machine.AppC.C7Aux

/-- Volume of an array of `R`-bit records: `vol w = w.length · (R + 1)`. -/
theorem vol_widths (w : List (List Bool)) (R : ℕ) (hw : ∀ p ∈ w, p.length = R) :
    SubNLogN.Machine.vol w = w.length * (R + 1) := by
  induction w with
  | nil => simp [SubNLogN.Machine.vol, FramePassRAux.arrSyms_nil]
  | cons p w ih =>
    have ih' := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    simp only [SubNLogN.Machine.vol] at ih' ⊢
    rw [FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms,
      hw p List.mem_cons_self, ih', List.length_cons]
    ring

/-- `bitLen (2^k) = k + 1`. -/
theorem bitLen_two_pow' (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  rw [bitLen, IntMulTM.length_encodeNat, Nat.size_pow]

/-- `bitLen n ≤ n`. -/
theorem bitLen_le_self'' (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

/-- `f·K < Nat.size (c7M K f N0 N1 N2 N3)` when all `N_i ≥ 1` (since `2^{fK} ≤ c7M`). -/
theorem fK_lt_size {K f N0 N1 N2 N3 : ℕ} (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) : f * K < Nat.size (c7M K f N0 N1 N2 N3) := by
  have hle : 2 ^ (f * K) ≤ c7M K f N0 N1 N2 N3 := by
    unfold c7M
    have h1 : 1 ≤ 2 ^ (f * K) := Nat.one_le_two_pow
    calc 2 ^ (f * K) = 1 * 2 ^ (f * K) * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
        gcongr
  exact Nat.lt_size.2 hle

/-- **The cleanup budget.** The cost of `runs_cleanupP` (two pops, twelve constant drops) is at
most `40 · ocost 110 (A + 2)`, given `K ≥ 1`, `ρ < K`, `f ≥ 1` and `f·K < A`. -/
theorem cleanup_le (K ρ f A : ℕ) (hK : 1 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hA : f * K < A) :
    2 + (2 * bitLen 1 + 2) + (2 * bitLen 10 + 2) + (2 * bitLen 11 + 2) +
      (2 * bitLen (f * K) + 2) + (2 * bitLen (2 ^ (f * K)) + 2) + (2 * bitLen (2 ^ K) + 2) +
      (2 * bitLen (2 ^ (K - 1)) + 2) + (2 * bitLen (2 ^ ρ) + 2) +
      (2 * bitLen (2 ^ (ρ + 1)) + 2) + (2 * bitLen (f - 1) + 2) +
      (2 * bitLen (2 ^ A) + 2) + (2 * bitLen A + 2) ≤ 40 * ocost 110 (A + 2) := by
  have b10 : bitLen 10 = 4 := by decide
  have b11 : bitLen 11 = 4 := by decide
  have b1 : bitLen 1 = 1 := by simpa using bitLen_two_pow' 0
  simp only [bitLen_two_pow', b10, b11, b1]
  have h1 := bitLen_le_self'' (f * K)
  have h2 := bitLen_le_self'' (f - 1)
  have h3 := bitLen_le_self'' A
  have hKfK : K ≤ f * K := Nat.le_mul_of_pos_left K hf
  have hf1 : f ≤ f * K := Nat.le_mul_of_pos_right f hK
  have hO : 10400 * (A + 3) ≤ 40 * ocost 110 (A + 2) := by
    unfold ocost
    have h : A + 3 ≤ (A + 2 + 1) ^ 2 := by nlinarith
    calc 10400 * (A + 3) ≤ 10400 * (A + 2 + 1) ^ 2 := Nat.mul_le_mul_left _ h
      _ = 40 * ((2 * 110 + 40) * (A + 2 + 1) ^ 2) := by ring
  omega

/-- Sum of a constant over `List.range N`. -/
theorem sum_range_const (N b : ℕ) : ((List.range N).map (fun _ => b)).sum = N * b := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- **Cost of the assembled extraction kernel** (`c7Extract_of_parts`, `C7ExtractAssemble.lean`).
For a kit with constant `xk.c = 110`, records `w` of width `R` with `w.length = M = c7M K f N0 N1
N2 N3` (`6 ≤ K`, `ρ < K`, `1 ≤ f`, all `N_i ≥ 1`, `1 ≤ R`) and `A = Nat.size M`: the setup budget
`setupCost xk (vol w) M A`, plus the countdown cost of `M` record bodies of constant cost
`2((f-1)(8·opCost(A+2) + 16)) + 64·opCost(A+2) + Ct(fK+1)^3 + 4R + 8A + 60`, plus the cleanup cost
of `runs_cleanupP` on the constants of `setupSt`, is at most
`Cf · (M (lgVol (vol w) + 1)^3 + vol w + badMax K f M (lgVol (vol w) + 1) + 1)`. The only
hypothesis beyond the parameter bounds is `hCf`, the pure inequality of `C7XCostStmt` at `c = 110`
for this `Ct` and `Cf` (proved in `C7ExtractCost.lean`). Paper:
Lemma A.9 (`lem:transfer13`, eq. (`eq:transfer-packed`)). -/
theorem c7x_cost_le {E' : Type} [DecidableEq E'] (xk : XKit (XK E')) (hc : xk.c = 110)
    (Ct Cf K ρ f N0 N1 N2 N3 R : ℕ) (w : List (List Bool))
    (hCf : ∀ (K ρ f N0 N1 N2 N3 R : ℕ), 6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 →
      1 ≤ N3 → 1 ≤ R →
      let M := c7M K f N0 N1 N2 N3
      let V := M * (R + 1)
      let A := Nat.size M
      (20 * V + (M + 100 * (A + 2)) * ocost 110 (A + 2)) +
        (M * (2 * ((f - 1) * (8 * ocost 110 (A + 2) + 16)) + 64 * ocost 110 (A + 2) +
          Ct * (f * K + 1) ^ 3 + 4 * R + 8 * A + 60) + 16 * M + 2) +
        40 * ocost 110 (A + 2) ≤
      Cf * (M * (lgVol V + 1) ^ 3 + V + badMax K f M * (lgVol V + 1) + 1))
    (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) (hR : 1 ≤ R) (hw : w.length = c7M K f N0 N1 N2 N3)
    (hwR : ∀ p ∈ w, p.length = R) :
    setupCost xk (SubNLogN.Machine.vol w) w.length (Nat.size w.length) +
      (countdownCost (fun _ => 2 * ((f - 1) * (8 * opCost xk (Nat.size w.length + 2) + 16)) +
          64 * opCost xk (Nat.size w.length + 2) + Ct * (f * K + 1) ^ 3 + 4 * R +
          8 * Nat.size w.length + 60) w.length +
        (2 + (2 * bitLen 1 + 2) + (2 * bitLen 10 + 2) + (2 * bitLen 11 + 2) +
          (2 * bitLen (f * K) + 2) + (2 * bitLen (2 ^ (f * K)) + 2) + (2 * bitLen (2 ^ K) + 2) +
          (2 * bitLen (2 ^ (K - 1)) + 2) + (2 * bitLen (2 ^ ρ) + 2) +
          (2 * bitLen (2 ^ (ρ + 1)) + 2) + (2 * bitLen (f - 1) + 2) +
          (2 * bitLen (2 ^ Nat.size w.length) + 2) + (2 * bitLen (Nat.size w.length) + 2))) ≤
    Cf * (w.length * (lgVol (SubNLogN.Machine.vol w) + 1) ^ 3 + SubNLogN.Machine.vol w +
      badMax K f w.length * (lgVol (SubNLogN.Machine.vol w) + 1) + 1) := by
  have hV := vol_widths w R hwR
  have hO : ∀ n, opCost xk n = ocost 110 n := fun n => by simp only [opCost, ocost, hc]
  have H := hCf K ρ f N0 N1 N2 N3 R hK hρ hf hN0 hN1 hN2 hN3 hR
  dsimp only at H
  have hA := fK_lt_size (K := K) (f := f) hN0 hN1 hN2 hN3
  rw [← hw] at H hA
  rw [hV]
  unfold setupCost
  simp only [hO]
  have hcd := countdownCost_le
    (fun _ => 2 * ((f - 1) * (8 * ocost 110 (Nat.size w.length + 2) + 16)) +
      64 * ocost 110 (Nat.size w.length + 2) + Ct * (f * K + 1) ^ 3 + 4 * R +
      8 * Nat.size w.length + 60) w.length
  rw [sum_range_const] at hcd
  have hcl := cleanup_le K ρ f (Nat.size w.length) (by omega) hρ hf hA
  omega

end SubNLogN.Machine.AppC.C7XCostAux
