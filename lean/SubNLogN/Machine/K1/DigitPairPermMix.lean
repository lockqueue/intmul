/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitMix

/-!
# K1a-mix (`K1/DigitPairPermMix.lean`): fixed permutation of a digit pair, mixed shape

Paper: Fact 3.3(1) (`fact:oai-streams`) and Lemma A.4(1) (`lem:transfer-streams`,
split into `q²` streams by the two digit values, merge with permuted labels).

**Scope (honest summary).** Proves `k1PairPermMix_holds : K1PairPermMixStmt q π` for every
`q` with `NeZero q` and every fixed `π` (`Contracts/Streams.lean`, `K1PairPermMixStmt`), with no
extra hypotheses. The program is `mixProg id π.symm D D` with `D = [A, R 0, B, R 1]`
(`K1/DigitMix.lean`):
* distribute: for each leading block (while the source is nonempty), for each `d1`, each of the
  `N1` middle addresses, each `d2`, each of the `N2` trailing addresses, move the next record to
  stream `(d1, d2)`;
* merge: the same nest in reverse order; the record for output digits `(e1, e2)` is taken from
  stream `π⁻¹ (e1, e2)` and pushed onto the destination.
Cost `C·(V + 1)`: two record moves per record, `O(q²)` per leaf, and `O(blockSize)` loop
overhead per block (`ohN_le`), uniformly in `N0, N1, N2`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Arithmetic helpers -/

theorem div_lin (a b n : ℕ) (hb : b < n) : (a * n + b) / n = a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem mod_lin (a b n : ℕ) (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem lin_lt {a A b n : ℕ} (ha : a < A) (hb : b < n) : a * n + b < A * n := by
  calc a * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ A * n := Nat.mul_le_mul_right _ ha

/-- Mixed-radix decomposition for the shape `[·] × [q] × [N1] × [q] × [N2]`. -/
theorem decomp5 (q N1 N2 x : ℕ) :
    x = (((x / (N2 * q * N1 * q) * q + x / (N2 * q * N1) % q) * N1 + x / (N2 * q) % N1) * q +
      x / N2 % q) * N2 + x % N2 := by
  have h1 := Nat.div_add_mod' x N2
  have h2 := Nat.div_add_mod' (x / N2) q
  have h3 := Nat.div_add_mod' (x / N2 / q) N1
  have h4 := Nat.div_add_mod' (x / N2 / q / N1) q
  simp only [Nat.div_div_eq_div_mul] at h2 h3 h4
  rw [h4, h3, h2, h1]

/-- Overhead bound of a nested walk with nonzero ranges. -/
theorem ohN_le {q : ℕ} (Ns : Fin 2 → ℕ) :
    ∀ D : List NLab, (∀ l ∈ D, 1 ≤ l.size q Ns) →
      ohN q Ns D + 1 ≤ 36 ^ D.length * sizeN q Ns D
  | [], _ => by simp [ohN, sizeN]
  | l :: D, h => by
    have ih := ohN_le Ns D (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    have hsD : 1 ≤ sizeN q Ns D := by
      have := Nat.le_trans (Nat.le_add_left 1 _) ih
      rcases Nat.eq_zero_or_pos (sizeN q Ns D) with h0 | h0
      · rw [h0, Nat.mul_zero] at this; omega
      · exact h0
    have hP : 1 ≤ 36 ^ D.length * sizeN q Ns D :=
      Nat.mul_le_mul (Nat.one_le_pow _ _ (by norm_num)) hsD
    have hsz : sizeN q Ns (l :: D) = l.size q Ns * sizeN q Ns D := rfl
    have hpow : 36 ^ (l :: D).length * sizeN q Ns (l :: D) =
        36 * (l.size q Ns * (36 ^ D.length * sizeN q Ns D)) := by
      rw [hsz, List.length_cons, pow_succ]; ring
    rw [hpow]
    generalize hX : 36 ^ D.length * sizeN q Ns D = X at ih hP
    have hsX : 1 ≤ l.size q Ns * X := Nat.mul_le_mul hl hP
    cases l with
    | A =>
      simp only [ohN, NLab.size] at hl hsX ⊢
      have := Nat.mul_le_mul_left q ih
      nlinarith
    | B =>
      simp only [ohN, NLab.size] at hl hsX ⊢
      have := Nat.mul_le_mul_left q ih
      nlinarith
    | R r =>
      simp only [ohN, NLab.size] at hl hsX ⊢
      have hb := bitLen_le_self (Ns r)
      have := Nat.mul_le_mul_left (Ns r) ih
      nlinarith

/-- Volume bounds the record count. -/
theorem length_le_vol (v : List (List Bool)) : v.length ≤ vol v := by
  rw [vol_eq_sum]
  induction v with
  | nil => simp
  | cons p v ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-! ## The shape `[N0] × [q] × [N1] × [q] × [N2]` -/

/-- The two spectator ranges. -/
def nsOf (N1 N2 : ℕ) : Fin 2 → ℕ := fun r => if r.val = 0 then N1 else N2

/-- Static labels of the pair-permutation nest. -/
def ppD : List NLab := [.A, .R 0, .B, .R 1]

/-- The key digits of an address: `(d1, d2)`. -/
def ppKey (q N1 N2 : ℕ) [NeZero q] (x : ℕ) : Key q :=
  (modFin q (x / (N2 * q * N1)), modFin q (x / N2))

theorem ppD_size (q N1 N2 : ℕ) : sizeN q (nsOf N1 N2) ppD = q * (N1 * (q * (N2 * 1))) := by
  simp [ppD, sizeN, NLab.size, nsOf]

theorem ppD_key (q N1 N2 : ℕ) [NeZero q] (κ : Key q) (x : ℕ) :
    keyN q (nsOf N1 N2) ppD κ (x % sizeN q (nsOf N1 N2) ppD) = ppKey q N1 N2 x := by
  rw [ppD_size]
  simp only [ppD, keyN, sizeN, NLab.size, nsOf, updN, ppKey, Fin.isValue]
  simp only [show ((0 : Fin 2).val = 0) from rfl, show ((1 : Fin 2).val = 0) = False by decide,
    if_true, if_false]
  ext
  · simp only [Fin.val_ofNat, modFin]
    rw [Nat.mod_mul_left_div_self, Nat.mod_mod,
      show N1 * (q * (N2 * 1)) = N2 * q * N1 by ring]
  · simp only [Fin.val_ofNat, modFin]
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left q (show q * (N1 * (q * (N2 * 1))) =
        q * (N1 * (q * (N2 * 1))) from rfl)),
      Nat.mod_mod_of_dvd _ (Dvd.intro_left N1 (show N1 * (q * (N2 * 1)) =
        N1 * (q * (N2 * 1)) from rfl)),
      show q * (N2 * 1) = q * N2 by ring, Nat.mul_one, Nat.mod_mul_left_div_self, Nat.mod_mod]

/-! ## The address map `pairPermMixAddr` -/

theorem addr5_div2 {a p1 b p2 c q N1 N2 : ℕ} (hp2 : p2 < q) (hc : c < N2) :
    ((((a * q + p1) * N1 + b) * q + p2) * N2 + c) / (N2 * q) = (a * q + p1) * N1 + b := by
  rw [← Nat.div_div_eq_div_mul, div_lin _ _ _ hc, div_lin _ _ _ hp2]

theorem addr5_div3 {a p1 b p2 c q N1 N2 : ℕ} (hb : b < N1) (hp2 : p2 < q) (hc : c < N2) :
    ((((a * q + p1) * N1 + b) * q + p2) * N2 + c) / (N2 * q * N1) = a * q + p1 := by
  rw [← Nat.div_div_eq_div_mul, addr5_div2 hp2 hc, div_lin _ _ _ hb]

theorem modFin_val (q : ℕ) [NeZero q] (n : ℕ) : (modFin q n).val = n % q := rfl

section PP

variable (q N1 N2 : ℕ) [NeZero q]

theorem pp_def (σ : Equiv.Perm (Key q)) (y : ℕ) :
    pairPermMixAddr q N1 N2 σ y =
      (((y / (N2 * q * N1 * q) * q + (σ (ppKey q N1 N2 y)).1.val) * N1 + y / (N2 * q) % N1) * q +
        (σ (ppKey q N1 N2 y)).2.val) * N2 + y % N2 := rfl

/-- The key digits of `pairPermMixAddr σ y` are `σ` of those of `y`. -/
theorem ppKey_addr (σ : Equiv.Perm (Key q)) (y : ℕ) (hN1 : 0 < N1) (hN2 : 0 < N2) :
    ppKey q N1 N2 (pairPermMixAddr q N1 N2 σ y) = σ (ppKey q N1 N2 y) := by
  have hx2 : y % N2 < N2 := Nat.mod_lt _ hN2
  have hx1 : y / (N2 * q) % N1 < N1 := Nat.mod_lt _ hN1
  have hp1 := (σ (ppKey q N1 N2 y)).1.isLt
  have hp2 := (σ (ppKey q N1 N2 y)).2.isLt
  rw [pp_def]
  generalize σ (ppKey q N1 N2 y) = p at hp1 hp2 ⊢
  ext
  · simp only [ppKey, modFin_val]
    rw [addr5_div3 hx1 hp2 hx2, mod_lin _ _ _ hp1]
  · simp only [ppKey, modFin_val]
    rw [div_lin _ _ _ hx2, mod_lin _ _ _ hp2]

/-- `pairPermMixAddr` stays in range. -/
theorem pp_lt (σ : Equiv.Perm (Key q)) (N0 y : ℕ) (hy : y < N0 * q * N1 * q * N2) :
    pairPermMixAddr q N1 N2 σ y < N0 * q * N1 * q * N2 := by
  have hpos : 0 < N0 * q * N1 * q * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hN2 : 0 < N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hN1 : 0 < N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hq : 0 < q := Nat.pos_of_neZero q
  have hk : 0 < N2 * q * N1 * q := by positivity
  have ha : y / (N2 * q * N1 * q) < N0 := by
    rw [Nat.div_lt_iff_lt_mul hk]
    calc y < N0 * q * N1 * q * N2 := hy
      _ = N0 * (N2 * q * N1 * q) := by ring
  rw [pp_def]
  exact lin_lt (lin_lt (lin_lt (lin_lt ha (σ (ppKey q N1 N2 y)).1.isLt) (Nat.mod_lt _ hN1))
    (σ (ppKey q N1 N2 y)).2.isLt) (Nat.mod_lt _ hN2)

/-- On a fiber of the key digits, `pairPermMixAddr` is a translation. -/
theorem pp_shift (σ : Equiv.Perm (Key q)) (y : ℕ) :
    pairPermMixAddr q N1 N2 σ y + (ppKey q N1 N2 y).1.val * (N1 * q * N2) +
        (ppKey q N1 N2 y).2.val * N2 =
      y + (σ (ppKey q N1 N2 y)).1.val * (N1 * q * N2) + (σ (ppKey q N1 N2 y)).2.val * N2 := by
  have hd := decomp5 q N1 N2 y
  rw [pp_def]
  simp only [ppKey, modFin_val] at hd ⊢
  generalize (σ (modFin q (y / (N2 * q * N1)), modFin q (y / N2))).1.val = e1
  generalize (σ (modFin q (y / (N2 * q * N1)), modFin q (y / N2))).2.val = e2
  generalize y / (N2 * q * N1 * q) = A at hd ⊢
  generalize y / (N2 * q * N1) = Q3 at hd ⊢
  generalize y / (N2 * q) = Q2 at hd ⊢
  generalize y / N2 = Q1 at hd ⊢
  generalize y % N2 = C at hd ⊢
  conv_rhs => rw [hd]
  ring

end PP

/-! ## The contract -/

/-- **[PROVED] K1a-mix**: `K1PairPermMixStmt q π` holds for every `q ≥ 1` and every fixed
permutation `π` of `Fin q × Fin q`. -/
theorem k1PairPermMix_holds (q : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) :
    K1PairPermMixStmt q π := by
  refine ⟨2 * 1679616 + 2 * (allKeys q).length + 9, fun _ => ⟨EM q, inferInstance, inferInstance,
    Reg q, mixProg id π.symm ppD ppD, inferInstance, ⟨((none, none, .eq), (0, 0))⟩,
    mixProg_closed _ _ _ _, ?_⟩⟩
  intro N0 N1 N2 v rest r2 r3 S hlen hrest hr2 hr3 hS hS2 hS3
  set Bs := sizeN q (nsOf N1 N2) ppD with hBs
  have hBs' : Bs = q * (N1 * (q * (N2 * 1))) := ppD_size q N1 N2
  set M0 := if Bs = 0 then 0 else N0 with hM0def
  have hNB : N0 * q * N1 * q * N2 = N0 * Bs := by rw [hBs']; ring
  have hlen' : v.length = M0 * Bs := by
    rw [hlen, hNB, hM0def]
    by_cases h0 : Bs = 0
    · simp [h0]
    · simp [h0]
  have hM0 : 0 < Bs ∨ M0 = 0 := by
    by_cases h0 : Bs = 0
    · right; simp [hM0def, h0]
    · left; omega
  have hrr : ∀ r : Fin 2, TermOK ((fun r : Fin 2 => if r.val = 0 then r2 else r3) r) := by
    intro r; fin_cases r <;> simp [hr2, hr3]
  have hNP : ∀ r : Fin 2, S (mNP r) = natSyms (nsOf N1 N2 r) ++
      (fun r : Fin 2 => if r.val = 0 then r2 else r3) r := by
    intro r; fin_cases r
    · simpa [mNP, nsOf] using hS2
    · simpa [mNP, nsOf] using hS3
  have hpos : ∀ y, y < v.length → 0 < N1 ∧ 0 < N2 := by
    intro y hy
    rw [hlen] at hy
    have hp : 0 < N0 * q * N1 * q * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
    exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at hp),
      Nat.pos_of_ne_zero (fun h => by simp [h] at hp)⟩
  have hR := mixProg_runs id π.symm ppD ppD (nsOf N1 N2) rfl v M0 hlen' hM0
    (ppKey q N1 N2) (fun y => π.symm (ppKey q N1 N2 y)) (pairPermMixAddr q N1 N2 π.symm)
    (fun κ x _ => by simp only [id]; exact ppD_key q N1 N2 κ x)
    (fun κ y _ => by rw [ppD_key])
    (fun y hy => by rw [hlen] at hy ⊢; exact pp_lt q N1 N2 π.symm N0 y hy)
    (fun y hy => ppKey_addr q N1 N2 π.symm y (hpos y hy).1 (hpos y hy).2)
    (fun y y' hy hy' he hlt => by
      have hk : ppKey q N1 N2 y = ppKey q N1 N2 y' := π.symm.injective he
      have h1 := pp_shift q N1 N2 π.symm y
      have h2 := pp_shift q N1 N2 π.symm y'
      rw [hk] at h1
      omega)
    rest hrest _ hrr S hS hNP
  refine WP.W9comp.runs_mono hR (fun _ _ => trivial) ?_
  -- cost
  have hvl := length_le_vol v
  have hK : M0 * (ohN q (nsOf N1 N2) ppD + ohN q (nsOf N1 N2) ppD + 5) ≤
      (2 * 1679616 + 3) * v.length := by
    by_cases h0 : M0 = 0
    · simp [h0]
    · have hBpos : 0 < Bs := by
        rcases hM0 with h | h
        · exact h
        · exact absurd h h0
      have hall : ∀ l ∈ ppD, 1 ≤ l.size q (nsOf N1 N2) := by
        rw [hBs'] at hBpos
        have hq : 1 ≤ q := Nat.pos_of_neZero q
        have hN1 : 1 ≤ N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
        have hN2 : 1 ≤ N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
        intro l hl
        simp only [ppD, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> simp [NLab.size, nsOf, hq, hN1, hN2]
      have hoh := ohN_le (q := q) (nsOf N1 N2) ppD hall
      rw [← hBs] at hoh
      have h36 : 36 ^ ppD.length = 1679616 := by simp [ppD]
      rw [h36] at hoh
      rw [hlen']
      have hM0B : M0 ≤ M0 * Bs := Nat.le_mul_of_pos_right _ hBpos
      have h3 := Nat.mul_le_mul_left M0 hoh
      nlinarith
  have h1 := Nat.mul_le_mul_left (2 * (allKeys q).length) hvl
  have h2 := Nat.mul_le_mul_left (2 * 1679616 + 3) hvl
  nlinarith

end SubNLogN.Machine.K1Digit
