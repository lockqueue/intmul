import WP.W9c.PureGlueQuant

/-!
# WP.W9c.PureGlueCells — `GlueCells` (split 4, pure)

* `length_passEmit`: a pass emits exactly `(nb + 1)·W` buckets (`W ≤ ol ≤ 2W`, so every window has
  `W` values).
* `cycAdd_spec`: closed form of the cyclic fold: cell `i < r` is the start cell plus the sum of the
  values `v_j` with `(p + j) mod r = i`.
* `card_filter_mod_le`: among `n ≤ 3r` consecutive `j`, at most `3` have `(p + j) mod r = i`
  (`j ↦ j / r` is injective on them).
* `glueCells_of_emit`: from `GlueEmit` (emitted buckets have bit length `≤ k + 1`, i.e. `|e| < 2^(k+1)`),
  every cell of every prefix tape has `|c| ≤ 3·(2^(k+1) − 1) < 2^(k+3)`: the prefix has
  `≤ (nb + 1)·W ≤ r + 2W − 1 < 3r` values.
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul
open scoped BigOperators

/-! ## Lengths -/

theorem length_unpackSK (H : ℤ) : ∀ (n : ℕ) (P : ℤ), (unpackSignedKronecker H n P).length = n
  | 0, _ => rfl
  | n + 1, P => by
    simp only [unpackSignedKronecker, List.length_cons, length_unpackSK H n]

theorem length_winStep (W : ℕ) (ws ds : List ℤ) (hws : ws.length = W) (h1 : W ≤ ds.length)
    (h2 : ds.length ≤ 2 * W) :
    (winStep W ws ds).1.length = W ∧ (winStep W ws ds).2.length = W := by
  simp only [winStep, List.length_zipWith, List.length_take, List.length_append, List.length_drop,
    List.length_replicate, hws]
  omega

theorem length_emitAll (W : ℕ) : ∀ (dss : List (List ℤ)) (ws : List ℤ), ws.length = W →
    (∀ ds ∈ dss, W ≤ ds.length ∧ ds.length ≤ 2 * W) →
    (emitAll W ws dss).length = (dss.length + 1) * W
  | [], ws, hws, _ => by simp [emitAll, hws]
  | ds :: dss, ws, hws, hds => by
    obtain ⟨h1, h2⟩ := hds ds (by simp)
    obtain ⟨hw1, hw2⟩ := length_winStep W ws ds hws h1 h2
    have ih := length_emitAll W dss _ hw2 (fun d hd => hds d (by simp [hd]))
    simp only [emitAll, List.length_append, hw1, ih, List.length_cons]
    ring

theorem length_passEmit (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ) (hWol : W ≤ ol)
    (hol : ol ≤ 2 * W) :
    (passEmit k p_in q W ol Pg x).length = ((chunks W x.length x).length + 1) * W := by
  have hds : ∀ ds ∈ passDigits k p_in q W ol Pg x, W ≤ ds.length ∧ ds.length ≤ 2 * W := by
    intro ds hds
    unfold passDigits at hds
    obtain ⟨blk, _, rfl⟩ := List.mem_map.1 hds
    rw [blockDigits, length_unpackSK]
    exact ⟨hWol, hol⟩
  have h := length_emitAll W (passDigits k p_in q W ol Pg x) (List.replicate W 0) (by simp) hds
  rw [passEmit, h, passDigits, List.length_map]

/-! ## The cyclic fold in closed form -/

theorem mod_add_succ (r p p' j : ℕ) (h : p' % r = p % r) :
    (p' + 1 + j) % r = (p + (j + 1)) % r := by
  rw [show p' + 1 + j = p' + (j + 1) by ring, Nat.add_mod, h, ← Nat.add_mod]

theorem cycAdd_spec (r : ℕ) (hr : 0 < r) : ∀ (vs cells : List ℤ) (p : ℕ), cells.length = r →
    p ≤ r →
    (cycAdd r cells p vs).1.length = r ∧
    ∀ i < r, (cycAdd r cells p vs).1.getD i 0 =
      cells.getD i 0 + ∑ j ∈ Finset.range vs.length, if (p + j) % r = i then vs.getD j 0 else 0
  | [], cells, p, hc, _ => ⟨hc, fun i _ => by simp [cycAdd]⟩
  | v :: vs, cells, p, hc, hp => by
    obtain ⟨p', hp'⟩ : ∃ p', p' = if p = r then 0 else p := ⟨_, rfl⟩
    have hp'r : p' < r := by
      rw [hp']
      split_ifs <;> omega
    have hp'm : p' % r = p % r := by
      rw [hp']
      split_ifs with h
      · subst h
        simp
      · rfl
    have hc' : (cells.set p' (cells.getD p' 0 + v)).length = r := by rw [List.length_set, hc]
    obtain ⟨ih1, ih2⟩ := cycAdd_spec r hr vs _ _ hc' (by omega : p' + 1 ≤ r)
    have hstep : cycAdd r cells p (v :: vs) = cycAdd r (cells.set p' (cells.getD p' 0 + v))
        (p' + 1) vs := by
      subst hp'
      rfl
    rw [hstep]
    refine ⟨ih1, fun i hi => ?_⟩
    rw [ih2 i hi, List.length_cons, Finset.sum_range_succ']
    have hpp : (p + 0) % r = p' := by rw [Nat.add_zero, ← hp'm, Nat.mod_eq_of_lt hp'r]
    have hset : (cells.set p' (cells.getD p' 0 + v)).getD i 0 =
        cells.getD i 0 + if (p + 0) % r = i then v else 0 := by
      rw [hpp]
      by_cases h : p' = i
      · subst h
        rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega),
          Option.getD_some]
      · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
          ← List.getD_eq_getElem?_getD, add_zero]
    rw [hset]
    simp only [List.getD_cons_succ, List.getD_cons_zero, mod_add_succ r p p' _ hp'm]
    ring

/-! ## Counting -/

theorem card_filter_mod_le (r p i n : ℕ) (hn : n ≤ 3 * r) :
    ((Finset.range n).filter (fun j => (p + j) % r = i)).card ≤ 3 := by
  calc ((Finset.range n).filter (fun j => (p + j) % r = i)).card
      ≤ (Finset.range 3).card := by
        apply Finset.card_le_card_of_injOn (fun j => j / r)
        · intro j hj
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
          rw [Finset.mem_coe, Finset.mem_range]
          exact Nat.div_lt_of_lt_mul (by omega)
        · intro j1 hj1 j2 hj2 heq
          rw [Finset.mem_coe, Finset.mem_filter] at hj1 hj2
          have hm : j1 % r = j2 % r := Nat.ModEq.add_left_cancel' p (hj1.2.trans hj2.2.symm)
          have heq' : j1 / r = j2 / r := heq
          rw [← Nat.div_add_mod j1 r, ← Nat.div_add_mod j2 r, heq', hm]
    _ = 3 := Finset.card_range 3

theorem sum_mod_bound (r p i n : ℕ) (hn : n ≤ 3 * r) (f : ℕ → ℤ) (M : ℤ)
    (hM : 0 ≤ M) (hf : ∀ j < n, |f j| ≤ M) :
    |∑ j ∈ Finset.range n, if (p + j) % r = i then f j else 0| ≤ 3 * M := by
  rw [← Finset.sum_filter]
  calc |∑ j ∈ (Finset.range n).filter (fun j => (p + j) % r = i), f j|
      ≤ ∑ j ∈ (Finset.range n).filter (fun j => (p + j) % r = i), |f j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (Finset.range n).filter (fun j => (p + j) % r = i), M :=
        Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
    _ = (((Finset.range n).filter (fun j => (p + j) % r = i)).card : ℤ) * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * M := by
        have h := card_filter_mod_le r p i n hn
        have h' : (((Finset.range n).filter (fun j => (p + j) % r = i)).card : ℤ) ≤ 3 := by
          exact_mod_cast h
        exact mul_le_mul_of_nonneg_right h' hM

/-! ## GlueCells -/

/-- **GlueCells**, from `GlueEmit` (proved in the GlueEmit share): every cell of every prefix
tape has bit length `≤ k + 3`. -/
theorem glueCells_of_emit (hE : GlueEmit) : GlueCells := by
  intro k p_in q W r z ol Pg x hk hW hWr hz hWol hol2 hnb m hm c hc
  have hr : 0 < r := by omega
  have hEb : ∀ e ∈ passEmit k p_in q W ol Pg x, |e| ≤ 2 ^ (k + 1) - 1 := by
    intro e he
    exact Int.le_sub_one_of_lt (abs_lt_of_bitLen (hE k p_in q W ol Pg x hk hWol hol2 e he))
  have hlen := length_passEmit k p_in q W ol Pg x hWol hol2
  generalize passEmit k p_in q W ol Pg x = E at hEb hlen hm hc
  generalize (chunks W x.length x).length = nb at hlen hnb
  have hm3 : (E.take m).length ≤ 3 * r := by
    rw [List.length_take]
    have h1 : (nb + 1) * W = nb * W + W := by ring
    omega
  obtain ⟨hlenC, hval⟩ := cycAdd_spec r hr (E.take m) (List.replicate r 0) z (by simp) hz.le
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hc
  have hi' : i < r := by omega
  have hci : c = (cycAdd r (List.replicate r 0) z (E.take m)).1.getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
  rw [hci, hval i hi']
  have h0 : (List.replicate r (0 : ℤ)).getD i 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, hi']
  rw [h0, zero_add]
  have hK1 : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpow1 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hpow3 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by ring
  have hb : |∑ j ∈ Finset.range (E.take m).length,
      if (z + j) % r = i then (E.take m).getD j 0 else 0| ≤ 3 * (2 ^ (k + 1) - 1) :=
    sum_mod_bound r z i (E.take m).length hm3 (fun j => (E.take m).getD j 0)
    (2 ^ (k + 1) - 1) (by rw [hpow1]; linarith) (fun j hj => by
      have hmem : (E.take m).getD j 0 ∈ E := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.mem_of_mem_take (List.getElem_mem hj)
      exact hEb _ hmem)
  apply bitLen_le_of_abs_lt
  rw [hpow3]
  rw [hpow1] at hb
  linarith

#assert_std_axioms length_unpackSK length_winStep length_emitAll length_passEmit mod_add_succ
  cycAdd_spec card_filter_mod_le sum_mod_bound glueCells_of_emit

end WP.W9c
