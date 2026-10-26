/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleSel

/-!
# K4-PREFIX parameter phase: unary kit (`Machine/FFT/PrefixParamKit.lean`)

**Scope (honest summary).** Generic machine routines (any stack type `K`, registers through a lens
`lO : Lens σ (Option Sym)`) on unary mark counters, for the parameter phase `PrefixParamStmt`
(`Machine/FFT/PrefixParamSpec.lean`). Every routine has an exact `Runs` lemma with explicit cost;
proved, no `sorry`:
* `uloop U body`: run `body` once per mark of `U` (consumed), `runs_uloop`;
* `toUnary`: binary `natSyms n` to `n` marks; `uCopy`: copy a counter; `runs_uMove`: move one;
* `monus`: `z ↦ z - t`; `cycMod`: `x mod k` by a cyclic counter; `mulU`: `d·y`;
* `pow2m1`: `2^p - 1` marks by iterated `dbl1`; `incLoop`: binary `b ↦ b + d`.
-/

namespace SubNLogN.Machine.FFT.PrefixParamAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF SubNLogN.Machine.FFT.TwiddleAux

theorem succ_mod_cases (i k : ℕ) (hk : 0 < k) :
    (i % k + 1 < k ∧ (i + 1) % k = i % k + 1) ∨ (i % k + 1 = k ∧ (i + 1) % k = 0) := by
  have hlt := Nat.mod_lt i hk
  rcases Nat.lt_or_ge (i % k + 1) k with h | h
  · refine Or.inl ⟨h, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt h]
  · have he : i % k + 1 = k := by omega
    refine Or.inr ⟨he, ?_⟩
    rcases Nat.lt_or_ge 1 k with h1 | h1
    · rw [Nat.add_mod, Nat.mod_eq_of_lt h1, he, Nat.mod_self]
    · have hk1 : k = 1 := by omega
      subst hk1
      exact Nat.mod_one _

section Kit

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Run `body` once per mark of the counter `U` (the counter is consumed). -/
def uloop (U : K) (body : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  ploop lO U Option.isSome (.seq (popO lO U) body)

omit [DecidableEq K] in
theorem closed_uloop (U : K) {body : Prog K (fun _ => Sym) σ} (hb : body.Closed) :
    (uloop lO U body).Closed :=
  closed_ploop lO U _ ⟨closed_popO lO U, hb⟩

/-- **Counted loop.** `F i` is the state after `i` runs of `body` (the counter entry is
overwritten). -/
theorem runs_uloop {U : K} (body : Prog K (fun _ => Sym) σ) (n c : ℕ) (F : ℕ → K → List Sym)
    (S : K → List Sym) (h0 : Function.update (F 0) U (List.replicate n .mark) = S)
    (hbody : ∀ i < n, Runs body
      (Function.update (F i) U (List.replicate (n - (i + 1)) .mark))
      (Function.update (F (i + 1)) U (List.replicate (n - (i + 1)) .mark)) (fun _ => True) c) :
    Runs (uloop lO U body) S (Function.update (F n) U []) (fun _ => True) (n * (c + 3) + 2) := by
  let St : ℕ → K → List Sym := fun i => Function.update (F i) U (List.replicate (n - i) .mark)
  have hloop := runs_ploop_const lO U Option.isSome (.seq (popO lO U) body) n St (1 + c) ?_ ?_
  · have hs0 : St 0 = S := by simp only [St, Nat.sub_zero]; exact h0
    have hN : St n = Function.update (F n) U [] := by simp [St]
    rw [hs0, hN] at hloop
    exact runs_mono hloop (fun _ _ => trivial) (le_of_eq (by ring))
  · intro i _
    simp only [St, Function.update_self]
    rcases Nat.lt_or_ge i n with h | h
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
      rw [hk, List.replicate_succ]
      simp only [List.head?_cons, Option.isSome_some]
      exact (decide_eq_true h).symm
    · rw [show n - i = 0 by omega]
      simp only [List.replicate_zero, List.head?_nil, Option.isSome_none]
      exact (decide_eq_false (by omega)).symm
  · intro i hi
    have e1 := runs_popO lO U (St i)
    have hpop : Function.update (St i) U (St i U).tail =
        Function.update (F i) U (List.replicate (n - (i + 1)) .mark) := by
      simp only [St, Function.update_self, Function.update_idem, List.tail_replicate,
        Nat.sub_sub]
    rw [hpop] at e1
    exact runs_mono (runs_seq' e1 (hbody i hi)) (fun _ _ => trivial) le_rfl

/-- Binary to unary: `natSyms n` on top of `I` is consumed and `n` marks are pushed on `U`. -/
def toUnary (I U t : K) : Prog K (fun _ => Sym) σ :=
  ploop lO I optIsBit (.seq (decP lO I t) (pushK U .mark))

omit [DecidableEq K] in
theorem closed_toUnary (I U t : K) : (toUnary lO I U t).Closed :=
  closed_ploop lO I _ ⟨closed_decP lO I t, closed_pushK U .mark⟩

theorem runs_toUnary {I U t : K} (h1 : I ≠ U) (h2 : I ≠ t) (S : K → List Sym) (n : ℕ)
    (Ir : List Sym) (hIr : TermOK Ir) (hI : S I = natSyms n ++ Ir) :
    Runs (toUnary lO I U t) S
      (Function.update (Function.update S I Ir) U (List.replicate n .mark ++ S U))
      (fun _ => True) (n * (6 * bitLen n + 11) + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update S I (natSyms (n - i) ++ Ir)) U
      (List.replicate i .mark ++ S U)
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  have hN : St n = Function.update (Function.update S I Ir) U
      (List.replicate n .mark ++ S U) := by
    simp only [St, Nat.sub_self, natSyms_zero', List.nil_append]
  have hloop := runs_ploop_const lO I optIsBit (.seq (decP lO I t) (pushK U .mark)) n St
    (6 * bitLen n + 9) ?_ ?_
  · rw [h0, hN] at hloop
    exact runs_mono hloop (fun _ _ => trivial) (le_of_eq (by ring))
  · intro i _
    simp only [St, Function.update_of_ne h1, Function.update_self]
    rw [optIsBit_natSyms _ _ hIr]
    simp
  · intro i hi
    have hmi : n - i = n - (i + 1) + 1 := by omega
    have hSI : St i I = natSyms (n - (i + 1) + 1) ++ Ir := by
      simp only [St, Function.update_of_ne h1, Function.update_self, hmi]
    have e1 := runs_decP lO h2 (St i) (n - (i + 1)) Ir hIr hSI
    have e2 := runs_pushK (σ := σ) U .mark
      (Function.update (St i) I (natSyms (n - (i + 1)) ++ Ir))
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) ?_) ?_
    · have hb : bitLen (n - (i + 1) + 1) ≤ bitLen n := bitLen_le_bitLen (by omega)
      omega
    · funext j
      simp only [St, Function.update_apply, h1.symm, List.replicate_succ, List.cons_append]
      split_ifs <;> simp_all

theorem runs_uMove {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (n : ℕ)
    (hS : S src = List.replicate n .mark) :
    Runs (movePrefix lO src dst Option.isSome) S
      (Function.update (Function.update S src []) dst (List.replicate n .mark ++ S dst))
      (fun _ => True) (4 * n + 2) := by
  have h := runs_movePrefix lO hne Option.isSome S (List.replicate n .mark) []
    (by rw [hS, List.append_nil]) (fun _ _ => rfl) rfl
  rw [List.reverse_replicate, List.length_replicate] at h
  exact h

/-- Copy the counter `src` (alone on its stack) onto `dst`, through `tmp`. -/
def uCopy (src dst tmp : K) : Prog K (fun _ => Sym) σ :=
  .seq (dupPrefix lO src tmp dst Option.isSome) (movePrefix lO tmp src Option.isSome)

omit [DecidableEq K] in
theorem closed_uCopy (src dst tmp : K) : (uCopy lO src dst tmp).Closed :=
  ⟨closed_dupPrefix lO src tmp dst _, closed_movePrefix lO tmp src _⟩

theorem runs_uCopy {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (S : K → List Sym) (n : ℕ) (hS : S src = List.replicate n .mark) (ht : S tmp = []) :
    Runs (uCopy lO src dst tmp) S (Function.update S dst (List.replicate n .mark ++ S dst))
      (fun _ => True) (9 * n + 4) := by
  have e1 := runs_dupPrefix lO h2 h1 h3.symm Option.isSome S (List.replicate n .mark) []
    (by rw [hS, List.append_nil]) (fun _ _ => rfl) rfl
  rw [List.reverse_replicate, ht, List.append_nil, List.length_replicate] at e1
  have e2 := runs_uMove lO h2.symm (Function.update (Function.update (Function.update S src [])
    tmp (List.replicate n .mark)) dst (List.replicate n .mark ++ S dst)) n
    (by rw [Function.update_of_ne h3.symm, Function.update_self])
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) (by omega)) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `Z := Z - |T|` (unary monus; `T` is consumed). -/
def monus (T Z : K) : Prog K (fun _ => Sym) σ := uloop lO T (popO lO Z)

omit [DecidableEq K] in
theorem closed_monus (T Z : K) : (monus lO T Z).Closed := closed_uloop lO T (closed_popO lO Z)

theorem runs_monus {T Z : K} (hne : T ≠ Z) (S : K → List Sym) (t z : ℕ)
    (hT : S T = List.replicate t .mark) (hZ : S Z = List.replicate z .mark) :
    Runs (monus lO T Z) S
      (Function.update (Function.update S T []) Z (List.replicate (z - t) .mark))
      (fun _ => True) (t * 4 + 2) := by
  have h := runs_uloop lO (U := T) (popO lO Z) t 1
    (fun i => Function.update S Z (List.replicate (z - i) .mark)) S
    (by funext j; simp only [Function.update_apply, Nat.sub_zero]; split_ifs <;> simp_all)
    (fun i _ => by
      refine runs_congr (runs_mono (runs_popO lO Z _) (fun _ _ => trivial) le_rfl) ?_
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all [Nat.sub_sub])
  refine runs_congr h ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- One step of the cyclic counter: move a mark from `C` to `R`; if `C` is then empty, move `R`
back onto `C`. -/
def cycStep (C R : K) : Prog K (fun _ => Sym) σ :=
  .seq (popO lO C) (.seq (pushK R .mark) (.seq (peekO lO C)
    (.ite (fun v => (lO.get v).isSome) skipP (movePrefix lO R C Option.isSome))))

omit [DecidableEq K] in
theorem closed_cycStep (C R : K) : (cycStep lO C R).Closed :=
  ⟨closed_popO lO C, closed_pushK R .mark, closed_peekO lO C, closed_skipP,
    closed_movePrefix lO R C _⟩

theorem runs_cycStep {C R : K} (hne : C ≠ R) (S : K → List Sym) (k i : ℕ) (hk : 0 < k)
    (hC : S C = List.replicate (k - i % k) .mark) (hR : S R = List.replicate (i % k) .mark) :
    Runs (cycStep lO C R) S
      (Function.update (Function.update S C (List.replicate (k - (i + 1) % k) .mark)) R
        (List.replicate ((i + 1) % k) .mark))
      (fun _ => True) (4 * k + 8) := by
  have hlt := Nat.mod_lt i hk
  have e1 := runs_popO lO C S
  rw [hC, List.tail_replicate] at e1
  have e2 := runs_pushK (σ := σ) R .mark
    (Function.update S C (List.replicate (k - i % k - 1) .mark))
  rw [Function.update_of_ne hne.symm, hR] at e2
  set S2 := Function.update (Function.update S C (List.replicate (k - i % k - 1) .mark)) R
    (Sym.mark :: List.replicate (i % k) .mark) with hS2
  have hS2C : S2 C = List.replicate (k - i % k - 1) .mark := by
    rw [hS2, Function.update_of_ne hne, Function.update_self]
  have e3 := runs_peekO lO C S2
  rcases succ_mod_cases i k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e4 := runs_seq_ite_t (p := (skipP : Prog K (fun _ => Sym) σ))
      (q := movePrefix lO R C Option.isSome) e3
      (fun v hv => by
        have hv' : lO.get v = (S2 C).head? := hv
        show (lO.get v).isSome = true
        rw [hv', hS2C]
        obtain ⟨c, hc⟩ : ∃ c, k - i % k - 1 = c + 1 := ⟨k - i % k - 2, by omega⟩
        rw [hc, List.replicate_succ]
        try rfl)
      (runs_skipP S2)
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e4)) (fun _ _ => trivial)
      (by omega)) ?_
    funext j
    simp only [hS2, Function.update_apply, h2, Nat.sub_sub, List.replicate_succ]
  · have hz : k - i % k - 1 = 0 := by omega
    have e5 := runs_uMove lO hne.symm S2 (i % k + 1)
      (by rw [hS2, Function.update_self, List.replicate_succ])
    have e4 := runs_seq_ite_f (p := (skipP : Prog K (fun _ => Sym) σ))
      (q := movePrefix lO R C Option.isSome) e3
      (fun v hv => by
        have hv' : lO.get v = (S2 C).head? := hv
        show (lO.get v).isSome = false
        rw [hv', hS2C, hz]
        try rfl) e5
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e4)) (fun _ _ => trivial)
      (by omega)) ?_
    funext j
    simp only [hS2, Function.update_apply, h2, hz, h1, Nat.sub_zero]
    split_ifs <;> simp_all

/-- `R := x mod k` marks (`X` holds `x` marks and is consumed; `C` starts with `k ≥ 1` marks and
ends with `k - x mod k`). -/
def cycMod (X C R : K) : Prog K (fun _ => Sym) σ := uloop lO X (cycStep lO C R)

omit [DecidableEq K] in
theorem closed_cycMod (X C R : K) : (cycMod lO X C R).Closed :=
  closed_uloop lO X (closed_cycStep lO C R)

theorem runs_cycMod {X C R : K} (hd : [X, C, R].Nodup) (S : K → List Sym) (x k : ℕ)
    (hk : 0 < k) (hX : S X = List.replicate x .mark) (hC : S C = List.replicate k .mark)
    (hR : S R = []) :
    Runs (cycMod lO X C R) S
      (Function.update (Function.update (Function.update S X []) C
        (List.replicate (k - x % k) .mark)) R (List.replicate (x % k) .mark))
      (fun _ => True) (x * (4 * k + 11) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have hXC : X ≠ C := p0.1 C (by simp)
  have hXR : X ≠ R := p0.1 R (by simp)
  have hCR : C ≠ R := (List.pairwise_cons.1 p0.2).1 R (by simp)
  have h := runs_uloop lO (U := X) (cycStep lO C R) x (4 * k + 8)
    (fun i => Function.update (Function.update S C (List.replicate (k - i % k) .mark)) R
      (List.replicate (i % k) .mark)) S
    (by funext j; simp only [Function.update_apply, Nat.zero_mod, Nat.sub_zero,
          List.replicate_zero]; split_ifs <;> simp_all)
    (fun i _ => by
      refine runs_congr (runs_cycStep lO hCR _ k i hk ?_ ?_) ?_
      · simp [hXC.symm, hCR]
      · simp [hXR.symm]
      · funext j
        simp only [Function.update_apply]
        split_ifs <;> simp_all)
  refine runs_congr (runs_mono h (fun _ _ => trivial) (le_of_eq (by ring))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `P := P + |Dc|·|Y|` (`Dc` is consumed, `Y` restored; temporary `T`). -/
def mulU (Dc Y P T : K) : Prog K (fun _ => Sym) σ := uloop lO Dc (uCopy lO Y P T)

omit [DecidableEq K] in
theorem closed_mulU (Dc Y P T : K) : (mulU lO Dc Y P T).Closed :=
  closed_uloop lO Dc (closed_uCopy lO Y P T)

theorem runs_mulU {Dc Y P T : K} (hd : [Dc, Y, P, T].Nodup) (S : K → List Sym) (d y : ℕ)
    (hDc : S Dc = List.replicate d .mark) (hY : S Y = List.replicate y .mark) (hP : S P = [])
    (hT : S T = []) :
    Runs (mulU lO Dc Y P T) S
      (Function.update (Function.update S Dc []) P (List.replicate (d * y) .mark))
      (fun _ => True) (d * (9 * y + 7) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have h1 : Dc ≠ Y := p0.1 Y (by simp)
  have h2 : Dc ≠ P := p0.1 P (by simp)
  have h3 : Dc ≠ T := p0.1 T (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h4 : Y ≠ P := p1.1 P (by simp)
  have h5 : Y ≠ T := p1.1 T (by simp)
  have h6 : P ≠ T := (List.pairwise_cons.1 p1.2).1 T (by simp)
  have h := runs_uloop lO (U := Dc) (uCopy lO Y P T) d (9 * y + 4)
    (fun i => Function.update S P (List.replicate (i * y) .mark)) S
    (by funext j; simp only [Function.update_apply, Nat.zero_mul, List.replicate_zero];
        split_ifs <;> simp_all)
    (fun i _ => by
      refine runs_congr (runs_uCopy lO h4 h5 h6 _ y ?_ ?_) ?_
      · simp [h1.symm, h4, hY]
      · simp [h3.symm, h6.symm, hT]
      · funext j
        have e : (i + 1) * y = y + i * y := by ring
        simp only [Function.update_apply, e, List.replicate_add]
        split_ifs <;> simp_all)
  refine runs_congr (runs_mono h (fun _ _ => trivial) (le_of_eq (by ring))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `E := 2^{|P|} - 1` marks, from `E` empty (`P` is consumed; temporary `A`). -/
def pow2m1 (P E A : K) : Prog K (fun _ => Sym) σ := uloop lO P (dbl1 lO E A)

omit [DecidableEq K] in
theorem closed_pow2m1 (P E A : K) : (pow2m1 lO P E A).Closed :=
  closed_uloop lO P (closed_dbl1 lO E A)

theorem runs_pow2m1 {P E A : K} (hd : [P, E, A].Nodup) (S : K → List Sym) (p : ℕ)
    (hP : S P = List.replicate p .mark) (hE : S E = []) (hA : S A = []) :
    Runs (pow2m1 lO P E A) S
      (Function.update (Function.update S P []) E (List.replicate (2 ^ p - 1) .mark))
      (fun _ => True) (p * (13 * 2 ^ p + 12) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have h1 : P ≠ E := p0.1 E (by simp)
  have h2 : P ≠ A := p0.1 A (by simp)
  have h3 : E ≠ A := (List.pairwise_cons.1 p0.2).1 A (by simp)
  have h := runs_uloop lO (U := P) (dbl1 lO E A) p (13 * 2 ^ p + 9)
    (fun i => Function.update S E (List.replicate (2 ^ i - 1) .mark)) S
    (by funext j; simp only [Function.update_apply, pow_zero, Nat.sub_self,
          List.replicate_zero]; split_ifs <;> simp_all)
    (fun i hi => by
      have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      have hle : 2 ^ i ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hi.le
      refine runs_congr (runs_mono (runs_dbl1 lO h3 _ (2 ^ i - 1) ?_ ?_) (fun _ _ => trivial)
        (by omega)) ?_
      · simp [h1.symm]
      · simp [h2.symm, h3.symm, hA]
      · funext j
        have e : 2 * (2 ^ i - 1) + 1 = 2 ^ (i + 1) - 1 := by rw [pow_succ]; omega
        simp only [Function.update_apply, e]
        split_ifs <;> simp_all)
  refine runs_congr (runs_mono h (fun _ _ => trivial) (le_of_eq (by ring))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `B := natSyms (b + |Dc|)` (`Dc` is consumed; `B` holds `natSyms b` alone; temporary `t`). -/
def incLoop (Dc B t : K) : Prog K (fun _ => Sym) σ := uloop lO Dc (incP lO B t)

omit [DecidableEq K] in
theorem closed_incLoop (Dc B t : K) : (incLoop lO Dc B t).Closed :=
  closed_uloop lO Dc (closed_incP lO B t)

theorem runs_incLoop {Dc B t : K} (hd : [Dc, B, t].Nodup) (S : K → List Sym) (d b : ℕ)
    (hDc : S Dc = List.replicate d .mark) (hB : S B = natSyms b) :
    Runs (incLoop lO Dc B t) S
      (Function.update (Function.update S Dc []) B (natSyms (b + d)))
      (fun _ => True) (d * (6 * bitLen (b + d) + 12) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have h1 : Dc ≠ B := p0.1 B (by simp)
  have h3 : B ≠ t := (List.pairwise_cons.1 p0.2).1 t (by simp)
  have h := runs_uloop lO (U := Dc) (incP lO B t) d (6 * bitLen (b + d) + 9)
    (fun i => Function.update S B (natSyms (b + i))) S
    (by funext j; simp only [Function.update_apply, Nat.add_zero]; split_ifs <;> simp_all)
    (fun i hi => by
      have hb : bitLen (b + i) ≤ bitLen (b + d) := bitLen_le_bitLen (by omega)
      refine runs_congr (runs_mono (runs_incP lO h3 _ (b + i) [] termOK_nil' ?_)
        (fun _ _ => trivial) (by omega)) ?_
      · simp [h1.symm]
      · funext j
        have e : b + (i + 1) = b + i + 1 := by omega
        simp only [Function.update_apply, e, List.append_nil]
        split_ifs <;> simp_all)
  refine runs_congr (runs_mono h (fun _ _ => trivial) (le_of_eq (by ring))) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Kit

end SubNLogN.Machine.FFT.PrefixParamAux
