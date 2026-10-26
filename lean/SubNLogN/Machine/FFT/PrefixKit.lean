/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFPass
import SubNLogN.Machine.FFT.PrefixDefs

/-!
# K4-PREFIX, generic machine kit (`Machine/FFT/PrefixKit.lean`)

Generic programs with exact `Runs` lemmas, for the prefix-round kernel (`PrefixRoundStmt`):
* `rep H HA body`: run `body` `|H|` times (`H` a stack of marks, parked on `HA` and restored),
  `runs_rep`;
* `dupRevRec`: one reversed record moved into normal orientation onto two stacks;
* block moves of `h` records: `bmov` (normal source, arrives reversed), `bdupRev` (reversed
  source, arrives normal on two stacks);
* list facts for the blocks of `bev`, `bod`, `bint` (`Machine/FFT/PrefixDefs.lean`).

All proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF

/-! ## Counted repeat -/

section Rep

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Run `body` `|H|` times (`H` a stack of marks, parked on `HA` and restored). -/
def rep (H HA : K) (body : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO H Option.isSome (.seq (popO lO H) (.seq (pushK HA .mark) body)))
    (movePrefix lO HA H Option.isSome)

omit [DecidableEq K] in
theorem closed_rep (H HA : K) {body : Prog K (fun _ => Sym) σ} (hb : body.Closed) :
    (rep lO H HA body).Closed :=
  ⟨closed_ploop lO H _ ⟨closed_popO lO H, closed_pushK HA .mark, hb⟩,
    closed_movePrefix lO HA H _⟩

/-- **Counted repeat.** `F i` are the states after `i` runs of `body` (with `H`, `HA` at their
initial values `mark^k`, `[]`); the body runs from `F i` to `F (i+1)` with the counters
`mark^{k-(i+1)}`, `mark^{i+1}`. -/
theorem runs_rep {H HA : K} (hne : H ≠ HA) (body : Prog K (fun _ => Sym) σ) (k c : ℕ)
    (F : ℕ → K → List Sym) (hH : ∀ i, F i H = List.replicate k .mark) (hHA : ∀ i, F i HA = [])
    (hbody : ∀ i < k, Runs body
      (Function.update (Function.update (F i) H (List.replicate (k - (i + 1)) .mark)) HA
        (List.replicate (i + 1) .mark))
      (Function.update (Function.update (F (i + 1)) H (List.replicate (k - (i + 1)) .mark)) HA
        (List.replicate (i + 1) .mark)) (fun _ => True) c) :
    Runs (rep lO H HA body) (F 0) (F k) (fun _ => True) (k * (c + 4) + 4 * k + 4) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (F i) H (List.replicate (k - i) .mark)) HA
      (List.replicate i .mark)
  have hStH : ∀ i, St i H = List.replicate (k - i) .mark := fun i => by
    simp only [St, Function.update_of_ne hne, Function.update_self]
  have hStHA : ∀ i, St i HA = List.replicate i .mark := fun i => by
    simp only [St, Function.update_self]
  have h0 : St 0 = F 0 := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; simp [hHA]
    · subst h2; simp [hH]
    · rfl
  have hloop := runs_ploop_const lO H Option.isSome
    (.seq (popO lO H) (.seq (pushK HA .mark) body)) k St (c + 2) ?_ ?_
  · rw [h0] at hloop
    have hA' : St k HA = List.replicate k .mark ++ [] := by rw [hStHA, List.append_nil]
    have hmv := runs_movePrefix lO hne.symm Option.isSome (St k) (List.replicate k .mark) []
      hA' (by simp) rfl
    refine runs_congr (runs_mono (runs_seq hloop hmv) (fun _ _ => trivial) ?_) ?_
    · simp only [List.length_replicate, show c + 2 + 2 = c + 4 by omega]; omega
    · funext j
      by_cases hj1 : j = H
      · rw [hj1, Function.update_self, hStH, hH k, Nat.sub_self, List.replicate_zero,
          List.append_nil, List.reverse_replicate]
      · by_cases hj2 : j = HA
        · rw [hj2, Function.update_of_ne (Ne.symm hne), Function.update_self, hHA k]
        · rw [Function.update_of_ne hj1, Function.update_of_ne hj2]
          simp only [St, Function.update_of_ne hj1, Function.update_of_ne hj2]
  · intro i hi
    rw [hStH, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have e1 := runs_popO lO H (St i)
    have e2 := runs_pushK (σ := σ) HA .mark (Function.update (St i) H (St i H).tail)
    have hS2 : Function.update (Function.update (St i) H (St i H).tail) HA
        (Sym.mark :: Function.update (St i) H (St i H).tail HA) =
        Function.update (Function.update (F i) H (List.replicate (k - (i + 1)) .mark)) HA
          (List.replicate (i + 1) .mark) := by
      rw [hStH, List.tail_replicate, Function.update_of_ne hne.symm, hStHA]
      funext j
      simp only [St, Function.update_apply]
      split_ifs <;> simp_all [List.replicate_succ, Nat.sub_sub]
    have e3 := hbody i hi
    rw [← hS2] at e3
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial)
      (by omega)) ?_
    rfl

end Rep

/-! ## Records and blocks of records -/

section Blocks

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Duplicate one reversed record from `src` onto `a` and `b`, in normal orientation. -/
def dupRevRec (src a b : K) : Prog K (fun _ => Sym) σ :=
  .seq (dupmv lO src a b) (dupPrefix lO src a b optIsBit)

omit [DecidableEq K] in
theorem closed_dupRevRec (src a b : K) : (dupRevRec lO src a b).Closed :=
  ⟨closed_dupmv lO src a b, closed_dupPrefix lO src a b _⟩

theorem runs_dupRevRec {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (S : K → List Sym) (p : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hS : S src = (recSyms p).reverse ++ rest) :
    Runs (dupRevRec lO src a b) S
      (Function.update (Function.update (Function.update S src rest) a (recSyms p ++ S a)) b
        (recSyms p ++ S b))
      (fun _ => True) (5 * p.length + 5) := by
  have hS' : S src = Sym.sep :: ((p.map Sym.bit).reverse ++ rest) := by
    rw [hS, reverse_recSyms']; rfl
  have e1 := runs_dupmv lO hsa hsb hab S hS'
  set S1 := Function.update (Function.update (Function.update S src
    ((p.map Sym.bit).reverse ++ rest)) a (Sym.sep :: S a)) b (Sym.sep :: S b) with hS1
  have h1 : S1 src = (p.map Sym.bit).reverse ++ rest := by
    rw [hS1, Function.update_of_ne hsb, Function.update_of_ne hsa, Function.update_self]
  have e2 := runs_dupPrefix lO hsa hsb hab optIsBit S1 _ _ h1 (bits_optIsBit_rev p)
    (optIsBit_head?_of_termOK hrest)
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [List.length_reverse, List.length_map]; omega)) ?_
  funext j
  simp only [hS1, Function.update_apply, recSyms_eq, List.reverse_reverse]
  split_ifs <;> simp_all

/-- Move `|H|` normal records from `src` to `dst` (they arrive reversed). -/
def bmov (src dst H HA : K) : Prog K (fun _ => Sym) σ := rep lO H HA (moveRec lO src dst)

omit [DecidableEq K] in
theorem closed_bmov (src dst H HA : K) : (bmov lO src dst H HA).Closed :=
  closed_rep lO H HA (closed_moveRec lO src dst)

theorem runs_bmov {src dst H HA : K} (hd : [src, dst, H, HA].Nodup) (S : K → List Sym)
    (Ps : List (List Bool)) (n0 : ℕ) (hP : ∀ p ∈ Ps, p.length = n0) (R : List Sym)
    (hS : S src = arrSyms Ps ++ R) (hH : S H = List.replicate Ps.length .mark)
    (hHA : S HA = []) :
    Runs (bmov lO src dst H HA) S
      (Function.update (Function.update S src R) dst ((arrSyms Ps).reverse ++ S dst))
      (fun _ => True) (Ps.length * (4 * n0 + 8) + 4 * Ps.length + 4) := by
  have p0 := List.pairwise_cons.1 hd
  have h_s_d : src ≠ dst := p0.1 dst (by simp)
  have h_s_H : src ≠ H := p0.1 H (by simp)
  have h_s_A : src ≠ HA := p0.1 HA (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_d_H : dst ≠ H := p1.1 H (by simp)
  have h_d_A : dst ≠ HA := p1.1 HA (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_H_A : H ≠ HA := p2.1 HA (by simp)
  let F : ℕ → K → List Sym := fun i =>
    Function.update (Function.update S src (arrSyms (Ps.drop i) ++ R)) dst
      ((arrSyms (Ps.take i)).reverse ++ S dst)
  have hF0 : F 0 = S := by
    funext j
    simp only [F, Function.update_apply, List.drop_zero, List.take_zero, arrSyms_nil']
    split_ifs with h1 h2 <;> simp_all
  have hFk : F Ps.length =
      Function.update (Function.update S src R) dst ((arrSyms Ps).reverse ++ S dst) := by
    simp only [F, List.drop_length, List.take_length, arrSyms_nil', List.nil_append]
  have h := runs_rep lO h_H_A (moveRec lO src dst) Ps.length (4 * n0 + 4) F
    (fun i => by
      simp only [F, Function.update_of_ne (Ne.symm h_d_H), Function.update_of_ne (Ne.symm h_s_H),
        hH])
    (fun i => by
      simp only [F, Function.update_of_ne (Ne.symm h_d_A), Function.update_of_ne (Ne.symm h_s_A),
        hHA])
    (fun i hi => ?_)
  · rw [hF0, hFk] at h
    refine runs_mono h (fun _ _ => trivial) ?_
    nlinarith
  · have hdrop : Ps.drop i = Ps[i] :: Ps.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hGs : Function.update (Function.update (F i) H
        (List.replicate (Ps.length - (i + 1)) .mark)) HA (List.replicate (i + 1) .mark) src =
        recSyms Ps[i] ++ (arrSyms (Ps.drop (i + 1)) ++ R) := by
      rw [Function.update_of_ne h_s_A, Function.update_of_ne h_s_H]
      simp only [F, Function.update_of_ne h_s_d, Function.update_self, hdrop, arrSyms_cons',
        List.append_assoc]
    have e := runs_moveRec lO h_s_d _ Ps[i] _ hGs
    rw [hP _ (List.getElem_mem hi)] at e
    refine runs_congr e ?_
    have ht : (arrSyms (Ps.take (i + 1))).reverse =
        (recSyms Ps[i]).reverse ++ (arrSyms (Ps.take i)).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, arrSyms_append',
        List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil]
    funext j
    simp only [F, Function.update_apply, ht]
    split_ifs <;> simp_all

/-- Duplicate `|H|` reversed records from `src` onto `a` and `b` (they arrive in normal order). -/
def bdupRev (src a b H HA : K) : Prog K (fun _ => Sym) σ := rep lO H HA (dupRevRec lO src a b)

omit [DecidableEq K] in
theorem closed_bdupRev (src a b H HA : K) : (bdupRev lO src a b H HA).Closed :=
  closed_rep lO H HA (closed_dupRevRec lO src a b)

theorem runs_bdupRev {src a b H HA : K} (hd : [src, a, b, H, HA].Nodup) (S : K → List Sym)
    (Ps : List (List Bool)) (n0 : ℕ) (hP : ∀ p ∈ Ps, p.length = n0) (R : List Sym)
    (hR : TermOK R) (hS : S src = (arrSyms Ps).reverse ++ R)
    (hH : S H = List.replicate Ps.length .mark) (hHA : S HA = []) :
    Runs (bdupRev lO src a b H HA) S
      (Function.update (Function.update (Function.update S src R) a (arrSyms Ps ++ S a)) b
        (arrSyms Ps ++ S b))
      (fun _ => True) (Ps.length * (5 * n0 + 9) + 4 * Ps.length + 4) := by
  have p0 := List.pairwise_cons.1 hd
  have h_s_a : src ≠ a := p0.1 a (by simp)
  have h_s_b : src ≠ b := p0.1 b (by simp)
  have h_s_H : src ≠ H := p0.1 H (by simp)
  have h_s_A : src ≠ HA := p0.1 HA (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_a_b : a ≠ b := p1.1 b (by simp)
  have h_a_H : a ≠ H := p1.1 H (by simp)
  have h_a_A : a ≠ HA := p1.1 HA (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_b_H : b ≠ H := p2.1 H (by simp)
  have h_b_A : b ≠ HA := p2.1 HA (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have h_H_A : H ≠ HA := p3.1 HA (by simp)
  set k := Ps.length with hk
  let F : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S src
      ((arrSyms (Ps.take (k - i))).reverse ++ R)) a (arrSyms (Ps.drop (k - i)) ++ S a)) b
      (arrSyms (Ps.drop (k - i)) ++ S b)
  have hF0 : F 0 = S := by
    funext j
    simp only [F, Function.update_apply, Nat.sub_zero]
    split_ifs with h1 h2 h3 <;> simp_all [arrSyms_nil']
  have hFk : F k = Function.update (Function.update (Function.update S src R) a
      (arrSyms Ps ++ S a)) b (arrSyms Ps ++ S b) := by
    simp only [F, Nat.sub_self, List.take_zero, List.drop_zero, arrSyms_nil', List.reverse_nil,
      List.nil_append]
  have h := runs_rep lO h_H_A (dupRevRec lO src a b) k (5 * n0 + 5) F
    (fun i => by
      simp only [F, Function.update_of_ne (Ne.symm h_b_H), Function.update_of_ne (Ne.symm h_a_H),
        Function.update_of_ne (Ne.symm h_s_H), hH])
    (fun i => by
      simp only [F, Function.update_of_ne (Ne.symm h_b_A), Function.update_of_ne (Ne.symm h_a_A),
        Function.update_of_ne (Ne.symm h_s_A), hHA])
    (fun i hi => ?_)
  · rw [hF0, hFk] at h
    refine runs_mono h (fun _ _ => trivial) ?_
    nlinarith
  · obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
    have hjk : j < k := by omega
    have hj' : k - (i + 1) = j := by omega
    have htake : (arrSyms (Ps.take (j + 1))).reverse =
        (recSyms Ps[j]).reverse ++ (arrSyms (Ps.take j)).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjk, Option.toList_some, arrSyms_append',
        List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil]
    have hdrop : Ps.drop j = Ps[j] :: Ps.drop (j + 1) := List.drop_eq_getElem_cons hjk
    have hGs : Function.update (Function.update (F i) H
        (List.replicate (k - (i + 1)) .mark)) HA (List.replicate (i + 1) .mark) src =
        (recSyms Ps[j]).reverse ++ ((arrSyms (Ps.take j)).reverse ++ R) := by
      rw [Function.update_of_ne h_s_A, Function.update_of_ne h_s_H]
      simp only [F, Function.update_of_ne h_s_b, Function.update_of_ne h_s_a,
        Function.update_self, hj, htake, List.append_assoc]
    have e := runs_dupRevRec lO h_s_a h_s_b h_a_b _ Ps[j] _ (termOK_rev_arrSyms _ R hR) hGs
    rw [hP _ (List.getElem_mem hjk)] at e
    refine runs_congr e ?_
    funext x
    simp only [F, Function.update_apply, hj, hj', hdrop, arrSyms_cons', List.append_assoc]
    split_ifs <;> simp_all

end Blocks

