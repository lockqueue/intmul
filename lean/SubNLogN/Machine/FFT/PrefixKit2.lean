/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixKit

/-!
# K4-PREFIX, list shapes and the block count (`Machine/FFT/PrefixKit2.lean`)

* Shapes of `bev`, `bod`, `bint`, `bpass`, `bflyIter` (`Machine/FFT/PrefixDefs.lean`): the number
  of records and the record lengths are preserved.
* `countBlk`: move a normal array of `h·N` records, `h` at a time, onto a reversed stack, and
  push one mark per block (`runs_countBlk`).

All proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF

/-! ## Shapes -/

section Shapes

variable {α : Type}

theorem length_flatMap_range (F : ℕ → List α) (c : ℕ) :
    ∀ M, (∀ j < M, (F j).length = c) → ((List.range M).flatMap F).length = M * c := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hF
    rw [List.range_succ, List.flatMap_append, List.length_append,
      ih (fun j hj => hF j (by omega))]
    simp [hF M (by omega)]
    ring

theorem length_bev (h M : ℕ) (B : List α) (hB : 2 * h * M ≤ B.length) :
    (bev h M B).length = M * h := by
  refine length_flatMap_range _ h M (fun j hj => ?_)
  simp only [List.length_take, List.length_drop]
  have : 2 * j * h + h ≤ B.length := by nlinarith
  omega

theorem length_bod (h M : ℕ) (B : List α) (hB : 2 * h * M ≤ B.length) :
    (bod h M B).length = M * h := by
  refine length_flatMap_range _ h M (fun j hj => ?_)
  simp only [List.length_take, List.length_drop]
  have : 2 * j * h + h + h ≤ B.length := by nlinarith
  omega

theorem length_bint (h M : ℕ) (X Y : List α) (hX : h * M ≤ X.length) (hY : h * M ≤ Y.length) :
    (bint h M X Y).length = M * (2 * h) := by
  refine length_flatMap_range _ (2 * h) M (fun j hj => ?_)
  simp only [List.length_append, List.length_take, List.length_drop]
  have h1 : j * h + h ≤ X.length := by nlinarith
  have h2 : j * h + h ≤ Y.length := by nlinarith
  omega

theorem mem_bev {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bev h M B) : x ∈ B := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_bod {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bod h M B) : x ∈ B := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_bint {h M : ℕ} {X Y : List α} {x : α} (hx : x ∈ bint h M X Y) : x ∈ X ∨ x ∈ Y := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hx
  rcases List.mem_append.1 hj with h1 | h1
  · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h1))
  · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h1))

theorem rows_zipC {f : CInt → CInt → CInt} {u v : List (List CInt)} {r : ℕ}
    (hu : ∀ row ∈ u, row.length = r) (hv : ∀ row ∈ v, row.length = r) :
    ∀ row ∈ zipC f u v, row.length = r := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  simp only [zipC, List.getElem_zipWith, List.length_zipWith]
  have hi' := hi
  simp only [zipC, List.length_zipWith] at hi'
  rw [hu _ (List.getElem_mem _), hv _ (List.getElem_mem _), Nat.min_self]

theorem length_zipC (f : CInt → CInt → CInt) (u v : List (List CInt)) :
    (zipC f u v).length = min u.length v.length := by
  simp [zipC]

theorem shape_bpass (h M r : ℕ) (B : List (List CInt)) (hB : B.length = 2 * h * M)
    (hrow : ∀ row ∈ B, row.length = r) :
    (bpass h M B).length = 2 * h * M ∧ ∀ row ∈ bpass h M B, row.length = r := by
  have he := length_bev h M B hB.ge
  have ho := length_bod h M B hB.ge
  have hre : ∀ row ∈ bev h M B, row.length = r := fun row hr => hrow row (mem_bev hr)
  have hro : ∀ row ∈ bod h M B, row.length = r := fun row hr => hrow row (mem_bod hr)
  refine ⟨?_, fun row hr => ?_⟩
  · unfold bpass
    rw [length_bint _ _ _ _ (by rw [length_zipC, he, ho]; simp [Nat.mul_comm])
      (by rw [length_zipC, he, ho]; simp [Nat.mul_comm])]
    ring
  · unfold bpass at hr
    rcases mem_bint hr with h1 | h1
    · exact rows_zipC hre hro row h1
    · exact rows_zipC hre hro row h1

theorem shape_bflyIter (m L r : ℕ) (B : List (List CInt)) (hB : B.length = 2 ^ m)
    (hrow : ∀ row ∈ B, row.length = r) :
    ∀ j, L + j ≤ m → (bflyIter m L j B).length = 2 ^ m ∧
      ∀ row ∈ bflyIter m L j B, row.length = r := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hB, hrow⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hpow : 2 ^ m = 2 * 2 ^ (L + j) * 2 ^ (m - L - j - 1) := by
      rw [mul_comm 2, mul_assoc, ← pow_succ', ← pow_add]
      congr 1
      omega
    obtain ⟨e1, e2⟩ := shape_bpass (2 ^ (L + j)) (2 ^ (m - L - j - 1)) r (bflyIter m L j B)
      (by rw [h1, hpow]) h2
    exact ⟨by simp only [bflyIter]; rw [e1, ← hpow], e2⟩

end Shapes

/-! ## Counting blocks while reversing an array -/

section Count

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Move the normal array on `E` onto `T` (reversed), `|H|` records at a time, pushing one mark on
`G` per block. -/
def countBlk (E T G H HA : K) : Prog K (fun _ => Sym) σ :=
  ploop lO E Option.isSome (.seq (bmov lO E T H HA) (pushK G .mark))

omit [DecidableEq K] in
theorem closed_countBlk (E T G H HA : K) : (countBlk lO E T G H HA).Closed :=
  closed_ploop lO E _ ⟨closed_bmov lO E T H HA, closed_pushK G .mark⟩

theorem runs_countBlk {E T G H HA : K} (hd : [E, T, G, H, HA].Nodup) (S : K → List Sym)
    (Bb : List (List Bool)) (n0 h N : ℕ) (hh : 1 ≤ h) (hP : ∀ p ∈ Bb, p.length = n0)
    (hlen : Bb.length = h * N) (hE : S E = arrSyms Bb) (hH : S H = List.replicate h .mark)
    (hHA : S HA = []) :
    Runs (countBlk lO E T G H HA) S
      (Function.update (Function.update (Function.update S E []) T ((arrSyms Bb).reverse ++ S T))
        G (List.replicate N .mark ++ S G))
      (fun _ => True) (N * (h * (4 * n0 + 8) + 4 * h + 4 + 1 + 2) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have h_E_T : E ≠ T := p0.1 T (by simp)
  have h_E_G : E ≠ G := p0.1 G (by simp)
  have h_E_H : E ≠ H := p0.1 H (by simp)
  have h_E_A : E ≠ HA := p0.1 HA (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_T_G : T ≠ G := p1.1 G (by simp)
  have h_T_H : T ≠ H := p1.1 H (by simp)
  have h_T_A : T ≠ HA := p1.1 HA (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_G_H : G ≠ H := p2.1 H (by simp)
  have h_G_A : G ≠ HA := p2.1 HA (by simp)
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S E (arrSyms (Bb.drop (h * i)))) T
      ((arrSyms (Bb.take (h * i))).reverse ++ S T)) G (List.replicate i .mark ++ S G)
  have hStE : ∀ i, St i E = arrSyms (Bb.drop (h * i)) := fun i => by
    simp only [St, Function.update_of_ne h_E_G, Function.update_of_ne h_E_T, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply, Nat.mul_zero, List.drop_zero, List.take_zero,
      arrSyms_nil', List.reverse_nil, List.nil_append, List.replicate_zero]
    split_ifs with h1 h2 h3 <;> simp_all
  have hloop := runs_ploop_const lO E Option.isSome (.seq (bmov lO E T H HA) (pushK G .mark)) N St
    (h * (4 * n0 + 8) + 4 * h + 4 + 1) ?_ ?_
  · rw [h0] at hloop
    refine runs_congr hloop ?_
    funext j
    simp only [St, Function.update_apply]
    split_ifs with h1 h2 h3
    · rfl
    · rw [← hlen, List.take_length]
    · rw [← hlen, List.drop_length, arrSyms_nil']
    · rfl
  · intro i hi
    rw [hStE]
    by_cases hlt : i < N
    · have hne : Bb.drop (h * i) ≠ [] := by
        intro he
        have := congrArg List.length he
        simp only [List.length_drop, List.length_nil] at this
        have : h * i < h * N := Nat.mul_lt_mul_of_pos_left hlt (by omega)
        omega
      obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil hne
      rw [hps, arrSyms_cons', recSyms_eq]
      cases p <;> simp [hlt]
    · have : Bb.drop (h * i) = [] := List.drop_eq_nil_of_le (by rw [hlen]; nlinarith)
      rw [this, arrSyms_nil']
      simp [hlt]
  · intro i hi
    set Ps := (Bb.drop (h * i)).take h with hPs
    have hPsl : Ps.length = h := by
      rw [hPs, List.length_take, List.length_drop, hlen]
      have : h * i + h ≤ h * N := by nlinarith
      omega
    have hdrop : Bb.drop (h * i) = Ps ++ Bb.drop (h * (i + 1)) := by
      rw [hPs, show h * (i + 1) = h * i + h by ring, ← List.drop_drop, List.take_append_drop]
    have htake : Bb.take (h * (i + 1)) = Bb.take (h * i) ++ Ps := by
      rw [hPs, show h * (i + 1) = h * i + h by ring, List.take_add]
    have hSE : St i E = arrSyms Ps ++ arrSyms (Bb.drop (h * (i + 1))) := by
      rw [hStE, hdrop, arrSyms_append']
    have hSH : St i H = List.replicate Ps.length .mark := by
      rw [hPsl]
      simp only [St, Function.update_of_ne (Ne.symm h_G_H), Function.update_of_ne (Ne.symm h_T_H),
        Function.update_of_ne (Ne.symm h_E_H), hH]
    have hSA : St i HA = [] := by
      simp only [St, Function.update_of_ne (Ne.symm h_G_A), Function.update_of_ne (Ne.symm h_T_A),
        Function.update_of_ne (Ne.symm h_E_A), hHA]
    have p3 := List.pairwise_cons.1 p2.2
    have h_H_A : H ≠ HA := p3.1 HA (by simp)
    have e1 := runs_bmov lO (src := E) (dst := T) (H := H) (HA := HA)
      (by simp [List.nodup_cons, h_E_T, h_E_H, h_E_A, h_T_H, h_T_A, h_H_A]) (St i) Ps n0
      (fun p hp => hP p (List.mem_of_mem_drop (List.mem_of_mem_take hp))) _ hSE hSH hSA
    have e2 := runs_pushK (σ := σ) G .mark (Function.update (Function.update (St i) E
      (arrSyms (Bb.drop (h * (i + 1))))) T ((arrSyms Ps).reverse ++ St i T))
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) (by rw [hPsl])) ?_
    funext j
    simp only [St, Function.update_apply, htake, arrSyms_append', List.reverse_append,
      List.append_assoc]
    split_ifs <;> simp_all [List.replicate_succ]

end Count

end SubNLogN.Machine.FFT.PrefixAux
