import SubNLogN.Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Component S1 (`Orbits.lean`): `[OAI26]` Lemma 6 Residual Table, 3-Atom Cell Calculus & Orbit Rank Sums

Proves the algebraic telescoping of the Lemma 6 of `[OAI26]` residual dimensions across stages `j ∈ {1, 2, 3}`
(`a = h^{j-1}`, `f = h^{3-j}`) for `X`, `Y`, `side`, and `center` wires (`[OAI26, Lemma 6, Props. 7–8]`),
the 3-atom factor-space decomposition (`1 + 1 + (h - 2) = h`), and the exact agreement of the
orbit-summed edge ranks with `tripleSb h` and `tripleSc h` (Definition A.1 (`def:fixed-network-premises`)).
-/

namespace SubNLogN.S1

open SubNLogN

/-- Lemma 6 of `[OAI26]` edge-rank sum for a single data role (`X` or `Y`) in stage `j ∈ {1, 2, 3}` with
prefix dimension `a = h^{j-1}`:
`(a - 1)*(h - 1) + (h - 1) + 0 + 0 = a * (h - 1)`. -/
def lemma6DataStageSum (a h : ℕ) : ℕ :=
  (a - 1) * (h - 1) + (h - 1)

/-- Summing `lemma6DataStageSum (h^{j-1}) h` over stages `j = 1, 2, 3` telescopes to `h^3 - 1 = m - 1`
for every `h ≥ 1`. -/
theorem lemma6_data_three_stages_eq (h : ℕ) (hh : 1 ≤ h) :
    lemma6DataStageSum 1 h + lemma6DataStageSum h h + lemma6DataStageSum (h ^ 2) h =
      tripleM h - 1 := by
  unfold lemma6DataStageSum tripleM
  have hh2 : 1 ≤ h ^ 2 := Nat.one_le_pow 2 h hh
  have hh3 : 1 ≤ h ^ 3 := Nat.one_le_pow 3 h hh
  zify [hh, hh2, hh3]
  ring

/-- Lemma 6 of `[OAI26]` edge-rank sum for a single `side` role in stage `j` with `a = h^{j-1}`, `f = h^{3-j}`:
`(a - 1) + ((a - 1)*(h - 1) + 1) + (h - 2) + 1 + a * h * (f - 1)`. -/
def lemma6SideRoleSum (a h f : ℕ) : ℕ :=
  (a - 1) + ((a - 1) * (h - 1) + 1) + (h - 2) + 1 + a * h * (f - 1)

/-- Every `side` role in every stage `j ∈ {1, 2, 3}` has total edge rank `a * h * f = h^3 = m`
for `h ≥ 2`, `a ≥ 1`, `f ≥ 1`. -/
theorem lemma6_side_role_sum_eq (a h f : ℕ) (ha : 1 ≤ a) (hh : 2 ≤ h) (hf : 1 ≤ f) :
    lemma6SideRoleSum a h f = a * h * f := by
  unfold lemma6SideRoleSum
  have hh1 : 1 ≤ h := by omega
  zify [ha, hh, hh1, hf]
  ring

/-- Lemma 6 of `[OAI26]` edge-rank sum for a single `center` role in stage `j` with `a = h^{j-1}`, `f = h^{3-j}`:
`(a - 1)*h + h + h + h + a * h * (f - 1)`. -/
def lemma6CenterRoleSum (a h f : ℕ) : ℕ :=
  (a - 1) * h + h + h + h + a * h * (f - 1)

/-- Every `center` role in every stage `j ∈ {1, 2, 3}` has total edge rank `a * h * f + 2 * h = m + 2h`
for `h ≥ 1`, `a ≥ 1`, `f ≥ 1`. -/
theorem lemma6_center_role_sum_eq (a h f : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) (hf : 1 ≤ f) :
    lemma6CenterRoleSum a h f = a * h * f + 2 * h := by
  have _ := hh
  unfold lemma6CenterRoleSum
  zify [ha, hf]
  ring

/-- **3-Atom Factor Cell Calculus (`[OAI26, §3]`):**
When an edge mentions two neighboring triples `S, T` in a factor of dimension `h ≥ 7`, the factor
splits into 3 orthogonal atoms (`⟨t₁⟩`, `⟨t₂⟩`, `⟨S, T⟩^⊥`) of dimensions `1, 1, h - 2`, whose
dimensions sum to `h`, and whose 3-tensor product has `3^3 = 27` cells summing to `h^3 = m`. -/
theorem three_atom_cell_dimensions_sum (h : ℕ) (hh : 2 ≤ h) :
    1 + 1 + (h - 2) = h ∧ (1 + 1 + (h - 2)) ^ 3 = tripleM h := by
  have h1 : 1 + 1 + (h - 2) = h := by omega
  exact ⟨h1, by rw [h1, tripleM]⟩

/-- **Global Orbit Rank-Sum Theorem (`[OAI26, Props. 7–8]`):**
Summing the Lemma 6 of `[OAI26]` role edge ranks across all `W_b` bit roles (with `N` data roles having sink
rank `0` and `N` having sink rank `1`, `I v z_b` side roles of rank `m`, and `I h` center roles
of rank `m + 2h`) equals `tripleSb h = W_b m + 2 L_b - N`; and across all `W_c` complex roles
(with all `2N` data roles having sink residual `0`, `I v z_c` side roles of residual `m`, and
`I (h + 1)` center roles of residual `m + 2h`) equals `tripleSc h = W_c m + 2 L_c - 2N`. -/
theorem orbit_rank_sum_identities (h : ℕ) (hh : 7 ≤ h) :
    tripleN h * (tripleM h - 1) + tripleN h * tripleM h +
      (tripleI h * tripleV h * tripleZb h) * tripleM h +
      (tripleI h * h) * (tripleM h + 2 * h) = tripleSb h ∧
    (2 * tripleN h) * (tripleM h - 1) +
      (tripleI h * tripleV h * tripleZc h) * tripleM h +
      (tripleI h * (h + 1)) * (tripleM h + 2 * h) = tripleSc h := by
  have hm : 1 ≤ tripleM h := Nat.one_le_pow 3 h (by omega)
  have h2n : 2 * tripleN h ≤ 2 * tripleN h * tripleM h := Nat.le_mul_of_pos_right _ hm
  have hsb : tripleN h ≤ tripleWb h * tripleM h + 2 * tripleLb h := by
    unfold tripleWb
    rw [Nat.add_mul]
    omega
  have hsc : 2 * tripleN h ≤ tripleWc h * tripleM h + 2 * tripleLc h := by
    unfold tripleWc
    rw [Nat.add_mul]
    omega
  constructor
  · unfold tripleSb
    zify [hm, hsb]
    unfold tripleWb tripleLb
    push_cast
    ring
  · unfold tripleSc
    zify [hm, hsc]
    unfold tripleWc tripleLc
    push_cast
    ring

/-- The 8 `(S_100)^3` role-orbit multiplicities of the bit triple network at `h = 100`
(`X data`, `Y data`, and `center` + `side |S ∩ T| = 1` across stages `1, 2, 3`). -/
def bitRoleOrbitMultiplicities100 : List ℕ :=
  [ 4227952113000000,
    4227952113000000,
    2614689000000,
    59056035114384000000,
    2614689000000,
    59056035114384000000,
    2614689000000,
    59056035114384000000 ]

/-- The 14 `(S_100)^3` role-orbit multiplicities of the complex triple network at `h = 100`
(`X data`, `Y data`, and `center`, `Cstar`, `side |S ∩ T| = 0`, `side |S ∩ T| = 2` across stages `1, 2, 3`). -/
def complexRoleOrbitMultiplicities100 : List ℕ :=
  [ 4227952113000000,
    4227952113000000,
    2614689000000,
    26146890000,
    623369259540720000000,
    1230334064883000000,
    2614689000000,
    26146890000,
    623369259540720000000,
    1230334064883000000,
    2614689000000,
    26146890000,
    623369259540720000000,
    1230334064883000000 ]

/-- All 56 `(multiplicity, residual_dim, bit_rank)` edge-class rows of the bit triple network at `h = 100`
(Definition A.1(a) (`def:fixed-network-premises`), Table 8 (`app:cert-closed`); full graph proof in `SubNLogN/Math/Networks/`). -/
def bitEdgeClassTable100 : List (ℕ × ℕ × ℕ) :=
  [ (4227952113000000, 0, 1),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 9801, 9801),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 989901, 989901),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 9801, 9801),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 989901, 989901),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (2614689000000, 0, 0),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 999900, 999900),
    (59056035114384000000, 0, 0),
    (59056035114384000000, 1, 1),
    (59056035114384000000, 98, 98),
    (59056035114384000000, 1, 1),
    (59056035114384000000, 999900, 999900),
    (2614689000000, 9900, 9900),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 990000, 990000),
    (59056035114384000000, 99, 99),
    (59056035114384000000, 9802, 9802),
    (59056035114384000000, 98, 98),
    (59056035114384000000, 1, 1),
    (59056035114384000000, 990000, 990000),
    (2614689000000, 999900, 999900),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 0, 0),
    (59056035114384000000, 9999, 9999),
    (59056035114384000000, 989902, 989902),
    (59056035114384000000, 98, 98),
    (59056035114384000000, 1, 1),
    (59056035114384000000, 0, 0) ]

/-- All 86 `(multiplicity, residual_dim, rank)` edge-class rows of the complex triple network at `h = 100`
(Definition A.1(b) (`def:fixed-network-premises`), Table 8 (`app:cert-closed`); full graph proof in `SubNLogN/Math/Networks/`). -/
def complexEdgeClassTable100 : List (ℕ × ℕ × ℕ) :=
  [ (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 9801, 9801),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 989901, 989901),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 9801, 9801),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (4227952113000000, 989901, 989901),
    (4227952113000000, 0, 0),
    (4227952113000000, 99, 99),
    (4227952113000000, 0, 0),
    (2614689000000, 0, 0),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 999900, 999900),
    (26146890000, 0, 0),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 999900, 999900),
    (623369259540720000000, 0, 0),
    (623369259540720000000, 1, 1),
    (623369259540720000000, 98, 98),
    (623369259540720000000, 1, 1),
    (623369259540720000000, 999900, 999900),
    (1230334064883000000, 0, 0),
    (1230334064883000000, 1, 1),
    (1230334064883000000, 98, 98),
    (1230334064883000000, 1, 1),
    (1230334064883000000, 999900, 999900),
    (2614689000000, 9900, 9900),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 990000, 990000),
    (26146890000, 9900, 9900),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 990000, 990000),
    (623369259540720000000, 99, 99),
    (623369259540720000000, 9802, 9802),
    (623369259540720000000, 98, 98),
    (623369259540720000000, 1, 1),
    (623369259540720000000, 990000, 990000),
    (1230334064883000000, 99, 99),
    (1230334064883000000, 9802, 9802),
    (1230334064883000000, 98, 98),
    (1230334064883000000, 1, 1),
    (1230334064883000000, 990000, 990000),
    (2614689000000, 999900, 999900),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 100, 100),
    (2614689000000, 0, 0),
    (26146890000, 999900, 999900),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 100, 100),
    (26146890000, 0, 0),
    (623369259540720000000, 9999, 9999),
    (623369259540720000000, 989902, 989902),
    (623369259540720000000, 98, 98),
    (623369259540720000000, 1, 1),
    (623369259540720000000, 0, 0),
    (1230334064883000000, 9999, 9999),
    (1230334064883000000, 989902, 989902),
    (1230334064883000000, 98, 98),
    (1230334064883000000, 1, 1),
    (1230334064883000000, 0, 0) ]

/-- **Explicit Orbit & Edge-Class Sums at `h = 100` (Definition A.1 (`def:fixed-network-premises`)):**
1. The 8 bit role-orbit multiplicities sum to `tripleWb 100 = 177176569091445000000`;
2. The 14 complex role-orbit multiplicities sum to `tripleWc 100 = 1873807244643542670000`;
3. The 56 bit edge-class rows (`multiplicity * rank`) sum to `tripleSb 100 = 177176569088785861287000000`;
4. The 86 complex edge-class rows (`multiplicity * rank`) sum to `tripleSc 100 = 1873807244636671267308000000`. -/
theorem h100_explicit_orbit_table_certificate :
    bitRoleOrbitMultiplicities100.sum = tripleWb 100 ∧
    complexRoleOrbitMultiplicities100.sum = tripleWc 100 ∧
    (bitEdgeClassTable100.map fun r => r.1 * r.2.2).sum = tripleSb 100 ∧
    (complexEdgeClassTable100.map fun r => r.1 * r.2.2).sum = tripleSc 100 := by decide

end SubNLogN.S1
