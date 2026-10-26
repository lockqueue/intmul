/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Counter
import IntMulTM.SpecFacts
import WP.W9comp.Kit

/-!
# Lemma A.9 top bit: counter arithmetic routines (`Machine/AppC/C7TopArith.lean`)

Support file of `Machine/AppC/C7Top.lean` (the top selected bit of Lemma A.9 (`lem:transfer13`),
Appendix A.4 (`sec:transfer-packed`),
via Lemma A.4(1) (`lem:transfer-streams`)). The kernel needs the two spectator sizes of a digit-pair permutation as binary counters;
they are products of the Lemma A.9 counters and powers of two. This file provides the stack routines that
build them, with exact final stacks and explicit cost bounds (`Eval` level, register `Option Sym`):

* `rep NP T U body`: run `body` `N` times, where `N` is the counter on `NP` (restored). The count is
  copied to `T` above a `mark` and counted down; `U` is the scratch stack of the `Lib` routines.
  `rep_runs`: if every iteration only changes the stack `X` (content `F i ↦ F (i+1)`, within `cb`
  steps), then `rep` changes `X` from `F 0` to `F N` within `N (cb + 6|N| + 10) + 7|N| + 12` steps.
* Instances: pushing `N` (or `N·N'`) zeros, popping `N` symbols, adding `N·N'` to a counter.
* `dropTo X g`: pop `X` down to and including the first `g`.
* `natSyms_mul_two_pow`: `natSyms (n·2^m) = 0^m ++ natSyms n` for `n ≥ 1` (LSB on top).

Everything here is proved (no pending hypotheses). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7TopAux

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Binary shifts -/

theorem encodeNat_mul_two_pow (n : ℕ) (hn : 0 < n) :
    ∀ m : ℕ, encodeNat (n * 2 ^ m) = List.replicate m false ++ encodeNat n
  | 0 => by simp
  | m + 1 => by
    have hpos : 0 < n * 2 ^ m := Nat.mul_pos hn (pow_pos (by norm_num) m)
    have hne : encodeNat (n * 2 ^ m) ≠ [] := by
      rw [Ne, encodeNat_eq_nil_iff]; omega
    have h2 : n * 2 ^ (m + 1) = n * 2 ^ m + n * 2 ^ m := by rw [pow_succ]; ring
    rw [h2, TMFw.encodeNat_add, if_neg hne, encodeNat_mul_two_pow n hn m, List.replicate_succ,
      List.cons_append]

/-- Shifting a positive counter left by `m` pushes `m` zeros (LSB on top). -/
theorem natSyms_mul_two_pow (n m : ℕ) (hn : 0 < n) :
    natSyms (n * 2 ^ m) = List.replicate m (Sym.bit false) ++ natSyms n := by
  rw [natSyms, encodeNat_mul_two_pow n hn m, List.map_append, List.map_replicate]
  rfl

theorem natSyms_zero : natSyms 0 = [] := by simp [natSyms, TMFw.encodeNat_zero]

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem bitLen_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 h

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt Nat.lt_two_pow_self

/-! ## Counted repetition -/

section Rep

variable {K : Type} [DecidableEq K]

/-- **Counted repetition**: run `body` `N` times, `N` the counter on `NP` (restored). The count is
copied onto `T` above a `mark` and counted down after each iteration; `U` is the scratch stack of
`copyBlock` and `dec`. -/
def rep (NP T U : K) (body : SProg K) : SProg K :=
  .seq (pushC T .mark) (.seq (copyBlock NP T U) (.seq (peekR T)
    (.seq (.loop optIsBit (.seq body (.seq (dec T U) (peekR T)))) (popR T))))

theorem head?_natSyms_succ (m : ℕ) (rest : List Sym) :
    optIsBit (natSyms (m + 1) ++ rest).head? = true := by
  obtain ⟨b0, l, hbl⟩ : ∃ b0 l, encodeNat (m + 1) = b0 :: l := by
    cases h : encodeNat (m + 1) with
    | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
    | cons b0 l => exact ⟨b0, l, rfl⟩
  simp [natSyms, hbl, optIsBit]

/-- Loop invariant of `rep`: `m` iterations remain. -/
theorem rep_loop {T U X : K} (hTU : T ≠ U) (hXT : X ≠ T) (body : SProg K)
    (S : K → List Sym) (F : ℕ → List Sym) (cb N : ℕ)
    (hbody : ∀ i < N, ∀ (Y : List Sym) (v : Option Sym), ∃ v' c, c ≤ cb ∧
      Eval [] body ⟨v, Function.update (Function.update S T Y) X (F i)⟩
        ⟨v', Function.update (Function.update S T Y) X (F (i + 1))⟩ c) :
    ∀ m, m ≤ N → ∀ v : Option Sym, v = (natSyms m ++ Sym.mark :: S T).head? →
      ∃ v' c, c ≤ m * (cb + 6 * bitLen N + 10) + 1 ∧
        Eval [] (.loop optIsBit (.seq body (.seq (dec T U) (peekR T))))
          ⟨v, Function.update (Function.update S T (natSyms m ++ Sym.mark :: S T)) X (F (N - m))⟩
          ⟨v', Function.update (Function.update S T (Sym.mark :: S T)) X (F N)⟩ c
  | 0, _, v, hv => by
    refine ⟨v, 1, by omega, ?_⟩
    have h0 : natSyms 0 ++ Sym.mark :: S T = Sym.mark :: S T := by simp [natSyms_zero]
    rw [h0, Nat.sub_zero]
    refine Eval.loop_false ?_
    show optIsBit v = false
    rw [hv, h0]
    rfl
  | m + 1, hm, v, hv => by
    obtain ⟨v1, c1, hc1, e1⟩ := hbody (N - (m + 1)) (by omega)
      (natSyms (m + 1) ++ Sym.mark :: S T) v
    have hidx : N - (m + 1) + 1 = N - m := by omega
    rw [hidx] at e1
    have hT : Function.update (Function.update S T (natSyms (m + 1) ++ Sym.mark :: S T)) X
        (F (N - m)) T = (encodeNat (m + 1)).map Sym.bit ++ (Sym.mark :: S T) := by
      rw [Function.update_of_ne hXT.symm, Function.update_self]; rfl
    have e2 := dec_eval hTU [] v1 m (Sym.mark :: S T) _ (TermOK.cons rfl _) hT
    have hSt : Function.update (Function.update (Function.update S T
        (natSyms (m + 1) ++ Sym.mark :: S T)) X (F (N - m))) T
          ((encodeNat m).map Sym.bit ++ Sym.mark :: S T) =
        Function.update (Function.update S T (natSyms m ++ Sym.mark :: S T)) X (F (N - m)) := by
      rw [Function.update_comm hXT.symm, Function.update_idem, Function.update_comm hXT]; rfl
    rw [hSt] at e2
    have e3 := Eval.peek [] T (fun _ o => o) (some Sym.mark)
      (Function.update (Function.update S T (natSyms m ++ Sym.mark :: S T)) X (F (N - m)))
    have hpk : (Function.update (Function.update S T (natSyms m ++ Sym.mark :: S T)) X
        (F (N - m)) T).head? = (natSyms m ++ Sym.mark :: S T).head? := by
      rw [Function.update_of_ne hXT.symm, Function.update_self]
    rw [hpk] at e3
    obtain ⟨v4, c4, hc4, e4⟩ := rep_loop hTU hXT body S F cb N hbody m (by omega) _ rfl
    refine ⟨v4, c1 + (6 * zerosLead (encodeNat (m + 1)) + 8 + 1) + c4 + 1, ?_,
      Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 e3)) e4⟩
    · have hz : zerosLead (encodeNat (m + 1)) ≤ bitLen N := by
        refine le_trans (zerosLead_le_length _) ?_
        exact bitLen_mono (by omega)
      have hmul : (m + 1) * (cb + 6 * bitLen N + 10) = m * (cb + 6 * bitLen N + 10) +
          (cb + 6 * bitLen N + 10) := by ring
      rw [hmul]
      omega
    · show optIsBit v = true
      rw [hv]
      exact head?_natSyms_succ m _

end Rep

section Rep2

variable {K : Type} [DecidableEq K]

/-- Bounded evaluation from any register, read off a `Runs` fact. -/
theorem runs_toEval {P : SProg K} {S S' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : Runs P S S' Q T) (v : Option Sym) : ∃ v' c, c ≤ T ∧ Eval [] P ⟨v, S⟩ ⟨v', S'⟩ c := by
  obtain ⟨s', t, e, ⟨hs, -⟩, ht⟩ := h ⟨v, S⟩ rfl
  obtain ⟨v', stk'⟩ := s'
  change stk' = S' at hs
  subst hs
  exact ⟨v', t, ht, e⟩

/-- A `Lib` routine lifted to a larger register type through a lens. -/
theorem runs_lift {σ : Type} (l : Lens σ (Option Sym)) {P : SProg K} {S S' : K → List Sym}
    {Q : Option Sym → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  exact ⟨⟨l.set v s'.var, s'.stk⟩, t, Eval.liftRegs l e v rfl, ⟨hs', trivial⟩, ht⟩

theorem pushC_runs (X : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC X x) S (Function.update S X (x :: S X)) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ?_
  have e := Eval.push [] X (fun _ => x) v S
  exact ⟨v, 1, e, trivial, le_rfl⟩

theorem popR_runs (X : K) (S : K → List Sym) :
    Runs (popR X) S (Function.update S X (S X).tail) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ?_
  have e := Eval.pop [] X (fun _ o => o) v S
  exact ⟨_, 1, e, trivial, le_rfl⟩

/-- **`rep`, exact**: if each iteration changes only `X`, from `F i` to `F (i+1)`, within `cb`
steps (for every content `Y` of the count stack `T`), then `rep` changes `X` from `F 0` to `F N`. -/
theorem rep_runs {NP T U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U) (hXT : X ≠ T)
    (hXN : X ≠ NP) (body : SProg K) (S : K → List Sym) (F : ℕ → List Sym) (cb N : ℕ)
    (rN : List Sym) (hrN : TermOK rN) (hNP : S NP = natSyms N ++ rN)
    (hbody : ∀ i < N, ∀ Y : List Sym, Runs body (Function.update (Function.update S T Y) X (F i))
      (Function.update (Function.update S T Y) X (F (i + 1))) (fun _ => True) cb) :
    Runs (rep NP T U body) (Function.update S X (F 0)) (Function.update S X (F N))
      (fun _ => True) (N * (cb + 6 * bitLen N + 10) + 7 * bitLen N + 11) := by
  refine Runs.of_eval fun v => ?_
  have e1 := Eval.push [] T (fun _ => Sym.mark) v (Function.update S X (F 0))
  have hT0 : Function.update S X (F 0) T = S T := Function.update_of_ne hXT.symm _ _
  rw [hT0] at e1
  have hNPv : Function.update (Function.update S X (F 0)) T (Sym.mark :: S T) NP =
      (encodeNat N).map Sym.bit ++ rN := by
    rw [Function.update_of_ne hNT, Function.update_of_ne hXN.symm, hNP]; rfl
  have e2 := copyBlock_eval hNT hNU hTU [] v (encodeNat N) rN _ hrN hNPv
  rw [Function.update_self, Function.update_idem] at e2
  have hcomm : Function.update (Function.update S X (F 0)) T
      ((encodeNat N).map Sym.bit ++ Sym.mark :: S T) =
      Function.update (Function.update S T (natSyms N ++ Sym.mark :: S T)) X (F (N - N)) := by
    rw [Nat.sub_self, Function.update_comm hXT]; rfl
  rw [hcomm] at e2
  have e3 := Eval.peek [] T (fun _ o => o) (some Sym.mark)
    (Function.update (Function.update S T (natSyms N ++ Sym.mark :: S T)) X (F (N - N)))
  have hpk : (Function.update (Function.update S T (natSyms N ++ Sym.mark :: S T)) X
      (F (N - N)) T).head? = (natSyms N ++ Sym.mark :: S T).head? := by
    rw [Function.update_of_ne hXT.symm, Function.update_self]
  rw [hpk] at e3
  have hb' : ∀ i < N, ∀ (Y : List Sym) (v : Option Sym), ∃ v' c, c ≤ cb ∧
      Eval [] body ⟨v, Function.update (Function.update S T Y) X (F i)⟩
        ⟨v', Function.update (Function.update S T Y) X (F (i + 1))⟩ c :=
    fun i hi Y v => runs_toEval (hbody i hi Y) v
  obtain ⟨v4, c4, hc4, e4⟩ := rep_loop hTU hXT body S F cb N hb' N le_rfl _ rfl
  have e5 := Eval.pop [] T (fun _ o => o) v4
    (Function.update (Function.update S T (Sym.mark :: S T)) X (F N))
  have hfin : Function.update (Function.update (Function.update S T (Sym.mark :: S T)) X (F N)) T
      (Function.update (Function.update S T (Sym.mark :: S T)) X (F N) T).tail =
      Function.update S X (F N) := by
    rw [Function.update_of_ne hXT.symm, Function.update_self, List.tail_cons,
      Function.update_comm hXT.symm, Function.update_idem,
      ← Function.update_of_ne hXT.symm (F N) S, Function.update_eq_self]
  rw [hfin] at e5
  refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))), trivial, ?_⟩
  have hl : (encodeNat N).length = bitLen N := rfl
  rw [hl]
  omega

/-- Push `N` zeros on `X`, `N` the counter on `NP`. -/
def pushZ (NP T U X : K) : SProg K := rep NP T U (pushC X (.bit false))

theorem pushZ_runs {NP T U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U) (hXT : X ≠ T)
    (hXN : X ≠ NP) (S : K → List Sym) (N : ℕ) (rN : List Sym) (hrN : TermOK rN)
    (hNP : S NP = natSyms N ++ rN) :
    Runs (pushZ NP T U X) S (Function.update S X (List.replicate N (Sym.bit false) ++ S X))
      (fun _ => True) (N * (6 * bitLen N + 11) + 7 * bitLen N + 11) := by
  have h := rep_runs hNT hNU hTU hXT hXN (pushC X (.bit false)) S
    (fun i => List.replicate i (Sym.bit false) ++ S X) 1 N rN hrN hNP (fun i _ Y => by
      have := pushC_runs X (Sym.bit false) (Function.update (Function.update S T Y) X
        (List.replicate i (Sym.bit false) ++ S X))
      rw [Function.update_self, Function.update_idem, ← List.cons_append,
        ← List.replicate_succ] at this
      exact this)
  simp only [List.replicate_zero, List.nil_append, Function.update_eq_self] at h
  exact WP.W9comp.runs_mono h (fun _ _ => trivial) (Nat.le_of_eq (by ring))

/-- Push `N·N'` zeros on `X` (`N` on `NP`, `N'` on `NP'`). -/
def pushZZ (NP NP' T T' U X : K) : SProg K := rep NP T U (pushZ NP' T' U X)

theorem pushZZ_runs {NP NP' T T' U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U)
    (hXT : X ≠ T) (hXN : X ≠ NP) (hN'T' : NP' ≠ T') (hN'U : NP' ≠ U) (hT'U : T' ≠ U)
    (hXT' : X ≠ T') (hXN' : X ≠ NP') (hN'T : NP' ≠ T) (S : K → List Sym) (N N' : ℕ)
    (rN rN' : List Sym) (hrN : TermOK rN) (hrN' : TermOK rN')
    (hNP : S NP = natSyms N ++ rN) (hNP' : S NP' = natSyms N' ++ rN') :
    Runs (pushZZ NP NP' T T' U X) S
      (Function.update S X (List.replicate (N * N') (Sym.bit false) ++ S X)) (fun _ => True)
      (N * (N' * (6 * bitLen N' + 11) + 7 * bitLen N' + 11 + 6 * bitLen N + 10) +
        7 * bitLen N + 11) := by
  have h := rep_runs hNT hNU hTU hXT hXN (pushZ NP' T' U X) S
    (fun i => List.replicate (i * N') (Sym.bit false) ++ S X)
    (N' * (6 * bitLen N' + 11) + 7 * bitLen N' + 11) N rN hrN hNP (fun i _ Y => by
      have hS' : Function.update (Function.update S T Y) X
          (List.replicate (i * N') (Sym.bit false) ++ S X) NP' = natSyms N' ++ rN' := by
        rw [Function.update_of_ne hXN'.symm, Function.update_of_ne hN'T, hNP']
      have := pushZ_runs hN'T' hN'U hT'U hXT' hXN' _ N' rN' hrN' hS'
      rw [Function.update_self, Function.update_idem, ← List.append_assoc,
        ← List.replicate_add, show N' + i * N' = (i + 1) * N' by ring] at this
      exact this)
  simp only [Nat.zero_mul, List.replicate_zero, List.nil_append, Function.update_eq_self] at h
  exact h

theorem inc_runs {X U : K} (hXU : X ≠ U) (S : K → List Sym) (a : ℕ) (rX : List Sym)
    (hrX : TermOK rX) (hX : S X = natSyms a ++ rX) :
    Runs (inc X U) S (Function.update S X (natSyms (a + 1) ++ rX)) (fun _ => True)
      (6 * bitLen a + 9) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hXU [] v (encodeNat a) rX S hrX hX
  refine ⟨some Sym.mark, c, ?_, trivial, ?_⟩
  · rw [natSyms, encodeNat_succ]; exact e
  · have := ones_le_length (encodeNat a)
    have hl : (encodeNat a).length = bitLen a := rfl
    omega

/-- Add `N·N'` to the counter on `X` (nested repetition of `inc`). -/
def mulAdd (NP NP' T T' U X : K) : SProg K := rep NP T U (rep NP' T' U (inc X U))

theorem mulAdd_runs {NP NP' T T' U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U)
    (hXT : X ≠ T) (hXN : X ≠ NP) (hN'T' : NP' ≠ T') (hN'U : NP' ≠ U) (hT'U : T' ≠ U)
    (hXT' : X ≠ T') (hXN' : X ≠ NP') (hN'T : NP' ≠ T) (hXU : X ≠ U) (S : K → List Sym)
    (N N' a : ℕ) (rN rN' rX : List Sym) (hrN : TermOK rN) (hrN' : TermOK rN') (hrX : TermOK rX)
    (hNP : S NP = natSyms N ++ rN) (hNP' : S NP' = natSyms N' ++ rN')
    (hX : S X = natSyms a ++ rX) :
    Runs (mulAdd NP NP' T T' U X) S (Function.update S X (natSyms (a + N * N') ++ rX))
      (fun _ => True)
      (N * (N' * (6 * bitLen (a + N * N') + 9 + 6 * bitLen N' + 10) + 7 * bitLen N' + 11 +
        6 * bitLen N + 10) + 7 * bitLen N + 11) := by
  have h := rep_runs hNT hNU hTU hXT hXN (rep NP' T' U (inc X U)) S
    (fun i => natSyms (a + i * N') ++ rX)
    (N' * (6 * bitLen (a + N * N') + 9 + 6 * bitLen N' + 10) + 7 * bitLen N' + 11) N rN hrN hNP
    (fun i hi Y => by
      have hS' : Function.update S T Y NP' = natSyms N' ++ rN' := by
        rw [Function.update_of_ne hN'T, hNP']
      have := rep_runs hN'T' hN'U hT'U hXT' hXN' (inc X U) (Function.update S T Y)
        (fun j => natSyms (a + i * N' + j) ++ rX) (6 * bitLen (a + N * N') + 9) N' rN' hrN' hS'
        (fun j hj Y' => by
          have hX' : Function.update (Function.update (Function.update S T Y) T' Y') X
              (natSyms (a + i * N' + j) ++ rX) X = natSyms (a + i * N' + j) ++ rX :=
            Function.update_self _ _ _
          have h2 := inc_runs hXU _ (a + i * N' + j) rX hrX hX'
          rw [Function.update_idem] at h2
          refine WP.W9comp.runs_mono h2 (fun _ _ => trivial) ?_
          have hle : a + i * N' + j ≤ a + N * N' := by
            have h3 : (i + 1) * N' ≤ N * N' := Nat.mul_le_mul_right _ hi
            have h4 : (i + 1) * N' = i * N' + N' := by ring
            omega
          have := bitLen_mono hle
          omega)
      simp only [Nat.add_zero] at this
      rw [show a + i * N' + N' = a + (i + 1) * N' by ring] at this
      exact this)
  simp only [Nat.zero_mul, Nat.add_zero] at h
  rw [← hX, Function.update_eq_self] at h
  exact h

/-- Pop `N` symbols from `X`. -/
def popN (NP T U X : K) : SProg K := rep NP T U (popR X)

theorem popN_runs {NP T U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U) (hXT : X ≠ T)
    (hXN : X ≠ NP) (S : K → List Sym) (N m : ℕ) (W rN : List Sym) (hrN : TermOK rN)
    (hNP : S NP = natSyms N ++ rN) (hX : S X = List.replicate m (Sym.bit false) ++ W)
    (hNm : N ≤ m) :
    Runs (popN NP T U X) S (Function.update S X (List.replicate (m - N) (Sym.bit false) ++ W))
      (fun _ => True) (N * (6 * bitLen N + 11) + 7 * bitLen N + 11) := by
  have h := rep_runs hNT hNU hTU hXT hXN (popR X) S
    (fun i => List.replicate (m - i) (Sym.bit false) ++ W) 1 N rN hrN hNP (fun i hi Y => by
      have := popR_runs X (Function.update (Function.update S T Y) X
        (List.replicate (m - i) (Sym.bit false) ++ W))
      have e : (List.replicate (m - i) (Sym.bit false) ++ W).tail =
          List.replicate (m - (i + 1)) (Sym.bit false) ++ W := by
        rw [show m - i = (m - (i + 1)) + 1 by omega, List.replicate_succ, List.cons_append,
          List.tail_cons]
      rw [Function.update_self, Function.update_idem, e] at this
      exact this)
  simp only [Nat.sub_zero] at h
  rw [← hX, Function.update_eq_self] at h
  exact WP.W9comp.runs_mono h (fun _ _ => trivial) (Nat.le_of_eq (by ring))

/-- Pop `X` down to and including the first `g`. -/
def dropTo (X : K) (g : Sym) : SProg K := .seq (popR X) (.loop (WP.W9comp.notG g) (popR X))

theorem dropTo_loop {X : K} (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S X = (L ++ g :: rest).tail →
      Eval [] (.loop (WP.W9comp.notG g) (popR X)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update S X rest⟩ (2 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [WP.W9comp.notG])).of_eq ?_ rfl
    have hS' : S X = rest := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S X rest⟩
    rw [← hS', Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S X = L ++ g :: rest := hS
    have hpop : Eval [] (popR X) ⟨some x, S⟩
        ⟨(L ++ g :: rest).head?, Function.update S X (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] X (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := dropTo_loop g L rest (Function.update S X (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [WP.W9comp.notG, hx]) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]; omega

theorem dropTo_runs (X : K) (g : Sym) (L rest : List Sym) (S : K → List Sym) (hg : g ∉ L)
    (hX : S X = L ++ g :: rest) :
    Runs (dropTo X g) S (Function.update S X rest) (fun _ => True) (2 * L.length + 2) := by
  refine Runs.of_eval fun v => ?_
  have h1 : Eval [] (popR X) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S X (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] X (fun _ o => o) v S).of_eq ?_ rfl
    rw [hX]
  have h2 := dropTo_loop g L rest (Function.update S X (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  have e := (Eval.seq h1 h2).of_eq (s₂ := ⟨some g, Function.update S X rest⟩)
    (by rw [Function.update_idem]) rfl
  exact ⟨some g, _, e, trivial, by omega⟩

/-! ### Closedness -/

omit [DecidableEq K] in
theorem copyBlock_closed (src dst tmp : K) : (copyBlock src dst tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, restoreR,
    moveBitsDup, dupBody, pushC, popR, pushR, skip]

omit [DecidableEq K] in
theorem dec_closed (k t : K) : (dec k t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR, pushR,
    skip, moveBits, moveBitsBody]

omit [DecidableEq K] in
theorem inc_closed (k t : K) : (inc k t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, restoreR, pushR,
    skip, moveBits, moveBitsBody]

theorem rep_closed (NP T U : K) {body : SProg K} (h : body.Closed) : (rep NP T U body).Closed :=
  ⟨trivial, copyBlock_closed NP T U, trivial, ⟨h, dec_closed T U, trivial⟩, trivial⟩

theorem pushZ_closed (NP T U X : K) : (pushZ NP T U X).Closed := rep_closed _ _ _ trivial

theorem pushZZ_closed (NP NP' T T' U X : K) : (pushZZ NP NP' T T' U X).Closed :=
  rep_closed _ _ _ (pushZ_closed _ _ _ _)

theorem mulAdd_closed (NP NP' T T' U X : K) : (mulAdd NP NP' T T' U X).Closed :=
  rep_closed _ _ _ (rep_closed _ _ _ (inc_closed _ _))

theorem popN_closed (NP T U X : K) : (popN NP T U X).Closed := rep_closed _ _ _ trivial

omit [DecidableEq K] in
theorem dropTo_closed (X : K) (g : Sym) : (dropTo X g).Closed := ⟨trivial, trivial⟩

end Rep2

end SubNLogN.Machine.AppC.C7TopAux
