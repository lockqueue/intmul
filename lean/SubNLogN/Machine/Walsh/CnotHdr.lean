/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.Cnot1
import SubNLogN.Machine.Walsh.CnotLeaf
import WP.W3.AddSub

/-!
# `SubNLogN.Machine.Walsh.CnotHdr`: the header builder of a CNOT batch (K3.4a)

Paper: Lemma 5.3 (`lem:walsh-lift`: `P_* = P + 8d`, `w_* = w + 8d`)
and Proposition 5.5 (`prop:cnot-batch`: lift, gadget, `CZ`, gadget, shift, lowering).

## Plan
From the slice header `sliceHdr P d r w K m j₀ D nS ρ = hdrSyms [P, d, r, w, K, m, j₀, D, nS, ρ]`
on stack `0` (restored):
* copy `P, d, r, w` onto clean scratch stacks (`copyBlock`), parking each field on `pk`;
* move the six tail fields `K, …, ρ` onto `pk2` and back, duplicating them onto stack `2`
  (`dupDrain`); restore the first four fields from `pk`;
* `8d` by pushing three zero bits on a copy of `d` (`times8`; nothing for `d = 0`);
* `P + 8d`, `w + 8d` by the proved W3 adder (`WP.W3.W3_addNat_holds`), embedded with `callInj`;
* push the remaining fields of the lifted header onto stack `2` and `hdrSyms [w, 8d]` onto stack
  `1` (`copyBlock`, `mark`s); clear the scratch.
Cost `O(|sliceHdr| + 1)`: every number involved has at most `|sliceHdr| + 4` bits.

**Scope (honest summary).** Proved (no `sorry`): `cnotHdr_holds : CnotHdrStmt`
(`Walsh/CnotLeaf.lean`). Helper lemmas live in `SubNLogN.Machine.WalshScanAux`.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Generic helpers -/

section Generic

variable {K : Type}

/-- Loop body of `dupDrain`. -/
def dupDrainBody (src d1 d2 : K) : SProg K := .seq (pushR d1) (.seq (pushR d2) (popR src))

/-- Empty `src`, pushing every symbol onto both `d1` and `d2`. -/
def dupDrain (src d1 d2 : K) : SProg K :=
  .seq (popR src) (.loop WalshLift.isSomeR (dupDrainBody src d1 d2))

/-- Multiply the natural number alone on `k` by `8`: push three zero bits unless it is `0`. -/
def times8 (k : K) : SProg K :=
  .seq (peekR k) (.ite optIsBit
    (.seq (pushC k (.bit false)) (.seq (pushC k (.bit false)) (pushC k (.bit false)))) skip)

theorem closed_dupDrain (src d1 d2 : K) : (dupDrain src d1 d2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dupDrain, dupDrainBody, pushR, popR]

theorem closed_times8 (k : K) : (times8 k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, times8, peekR, pushC, skip]

variable [DecidableEq K]

theorem dupDrain_loop_eval {src d1 d2 : K} (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval [] (.loop WalshLift.isSomeR (dupDrainBody src d1 d2)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S src []) d1 (L.reverse ++ S d1))
          d2 (L.reverse ++ S d2)⟩ (4 * L.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S src = [] := hS
    have e : Function.update (Function.update (Function.update S src []) d1
        (([] : List Sym).reverse ++ S d1)) d2 (([] : List Sym).reverse ++ S d2) = S := by
      funext k
      simp only [Function.update_apply, List.reverse_nil, List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    have ea := WalshLift.eval_pushR_some d1 x S
    have eb := WalshLift.eval_pushR_some d2 x (Function.update S d1 (x :: S d1))
    have hpop := WalshLift.eval_popR src (some x) L
      (Function.update (Function.update S d1 (x :: S d1)) d2
        (x :: Function.update S d1 (x :: S d1) d2))
      (by rw [Function.update_of_ne h2, Function.update_of_ne h1, hS'])
    have ih := dupDrain_loop_eval h1 h2 h12 L
      (Function.update (Function.update (Function.update S d1 (x :: S d1)) d2
        (x :: Function.update S d1 (x :: S d1) d2)) src L.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq ea (Eval.seq eb hpop)) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **`dupDrain`**, exact: `src` (holding `L`) is emptied onto both `d1` and `d2`, reversed. -/
theorem dupDrain_eval {src d1 d2 : K} (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2)
    (v : Option Sym) (L : List Sym) (S : K → List Sym) (hS : S src = L) :
    Eval [] (dupDrain src d1 d2) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S src []) d1 (L.reverse ++ S d1))
        d2 (L.reverse ++ S d2)⟩ (4 * L.length + 2) := by
  have e1 := WalshLift.eval_popR src v L S hS
  have e2 := dupDrain_loop_eval h1 h2 h12 L (Function.update S src L.tail)
    (Function.update_self _ _ _)
  refine (Eval.seq e1 e2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem encodeNat_eight_mul (d : ℕ) (hd : d ≠ 0) :
    encodeNat (8 * d) = false :: false :: false :: encodeNat d := by
  have hne : ∀ n : ℕ, n ≠ 0 → encodeNat n ≠ [] := fun n hn h => hn ((encodeNat_eq_nil_iff n).1 h)
  have e2 : ∀ n : ℕ, n ≠ 0 → encodeNat (2 * n) = false :: encodeNat n := by
    intro n hn
    rw [two_mul, encodeNat_add, if_neg (hne n hn)]
  rw [show 8 * d = 2 * (2 * (2 * d)) by ring, e2 _ (by omega), e2 _ (by omega), e2 _ hd]

/-- **`times8`**: the natural number `d` alone on `k` becomes `8d`. -/
theorem times8_eval (k : K) (v : Option Sym) (d : ℕ) (S : K → List Sym) (hS : S k = natSyms d) :
    ∃ v' t, Eval [] (times8 k) ⟨v, S⟩ ⟨v', Function.update S k (natSyms (8 * d))⟩ t ∧ t ≤ 5 := by
  unfold times8
  have e1 := WalshLift.eval_peekR k v _ S hS
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨(natSyms 0).head?, _, (Eval.seq e1 (Eval.ite_false (p := .seq (pushC k (.bit false))
      (.seq (pushC k (.bit false)) (pushC k (.bit false))))
      (by rw [natSyms, encodeNat_zero]; rfl) (skip_eval [] _))).of_eq ?_ rfl, by norm_num⟩
    rw [Nat.mul_zero, ← hS, Function.update_eq_self]
  · have h8 : natSyms (8 * d) = .bit false :: .bit false :: .bit false :: natSyms d := by
      simp [natSyms, encodeNat_eight_mul d (by omega)]
    obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat d = b :: l := by
      cases h : encodeNat d with
      | nil => exact absurd ((encodeNat_eq_nil_iff d).1 h) (by omega)
      | cons b l => exact ⟨b, l, rfl⟩
    have hhead : (natSyms d).head? = some (.bit b) := by simp [natSyms, hbl]
    have e2 := WalshLift.eval_pushC k (.bit false) (natSyms d).head? S
    have e3 := WalshLift.eval_pushC k (.bit false) (natSyms d).head?
      (Function.update S k (.bit false :: S k))
    have e4 := WalshLift.eval_pushC k (.bit false) (natSyms d).head?
      (Function.update (Function.update S k (.bit false :: S k)) k
        (.bit false :: Function.update S k (.bit false :: S k) k))
    refine ⟨(natSyms d).head?, _, (Eval.seq e1 (Eval.ite_true (q := skip) (by rw [hhead]; rfl)
      (Eval.seq e2 (Eval.seq e3 e4)))).of_eq ?_ rfl, by norm_num⟩
    rw [h8]
    congr 1
    simp [hS]

/-! ### `Runs` forms of the stream steps -/

/-- Copy the top field `natSyms n` of `h` onto `c` and park it (with its `mark`) on `pk`. -/
def copyField (h c pk tmp : K) : SProg K := .seq (copyBlock h c tmp) (WalshCnot1.skipField h pk)

/-- Push `mark`, then a copy of the number alone on `src`, onto `dst`. -/
def pushField (src dst tmp : K) : SProg K := .seq (pushC dst .mark) (copyBlock src dst tmp)

omit [DecidableEq K] in
theorem closed_copyField (h c pk tmp : K) : (copyField h c pk tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyField, WalshCnot1.skipField, copyBlock, moveBlock,
    moveBits, moveBitsBody, moveBitsDup, dupBody, restoreR, pushR, popR, pushC, skip]

omit [DecidableEq K] in
theorem closed_pushField (src dst tmp : K) : (pushField src dst tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushField, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, restoreR, pushR, popR, pushC, skip]

theorem runs_copyField {h c pk tmp : K} (hc : h ≠ c) (hp : h ≠ pk) (ht : h ≠ tmp) (hct : c ≠ tmp)
    (n : ℕ) (rest : List Sym) (S : K → List Sym) (hS : S h = natSyms n ++ Sym.mark :: rest) :
    Runs (copyField h c pk tmp) S
      (Function.update (Function.update (Function.update S c (natSyms n ++ S c)) h rest) pk
        ((natSyms n ++ [Sym.mark]).reverse ++ Function.update S c (natSyms n ++ S c) pk))
      (fun _ => True) (10 * bitLen n + 10) := by
  apply Runs.of_eval
  intro v
  have e1 := copyBlock_eval hc ht hct [] v (encodeNat n) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  have e2 := WalshCnot1.skipField_eval hp (some .mark) n rest
    (Function.update S c ((encodeNat n).map Sym.bit ++ S c))
    (by rw [Function.update_of_ne hc, hS])
  exact ⟨_, _, Eval.seq e1 e2, trivial, by simp only [bitLen]; omega⟩

theorem runs_pushField {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (S : K → List Sym) (hS : S src = natSyms n) :
    Runs (pushField src dst tmp) S
      (Function.update S dst (natSyms n ++ Sym.mark :: S dst)) (fun _ => True)
      (7 * bitLen n + 8) := by
  unfold pushField
  apply Runs.of_eval
  intro v
  have e1 := WalshLift.eval_pushC dst Sym.mark v S
  have e2 := copyBlock_eval hsd hst hdt [] v (encodeNat n) [] (Function.update S dst
    (Sym.mark :: S dst)) TermOK.nil (by rw [Function.update_of_ne hsd, hS, List.append_nil]; rfl)
  refine ⟨some .mark, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by simp only [bitLen]; omega⟩
  congr 1
  rw [Function.update_idem, Function.update_self]
  rfl

theorem runs_dupDrain {src d1 d2 : K} (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2)
    (L : List Sym) (S : K → List Sym) (hS : S src = L) :
    Runs (dupDrain src d1 d2) S
      (Function.update (Function.update (Function.update S src []) d1 (L.reverse ++ S d1))
        d2 (L.reverse ++ S d2)) (fun _ => True) (4 * L.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, dupDrain_eval h1 h2 h12 v L S hS, trivial, le_rfl⟩

theorem runs_drain {src dst : K} (hne : src ≠ dst) (L : List Sym) (S : K → List Sym)
    (hS : S src = L) :
    Runs (WalshLift.drain src dst) S
      (Function.update (Function.update S src []) dst (L.reverse ++ S dst)) (fun _ => True)
      (3 * L.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, WalshLift.drain_eval hne v L S hS, trivial, le_rfl⟩

theorem runs_clear (k : K) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Runs (WalshLift.clear k) S (Function.update S k []) (fun _ => True) (2 * L.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, WalshLift.clear_eval k v L S hS, trivial, le_rfl⟩

theorem runs_times8 (k : K) (d : ℕ) (S : K → List Sym) (hS : S k = natSyms d) :
    Runs (times8 k) S (Function.update S k (natSyms (8 * d))) (fun _ => True) 5 := by
  apply Runs.of_eval
  intro v
  obtain ⟨v', t, e, ht⟩ := times8_eval k v d S hS
  exact ⟨v', t, e, trivial, ht⟩

theorem runs_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (S : K → List Sym) (hS : S src = natSyms n) :
    Runs (copyBlock src dst tmp) S (Function.update S dst (natSyms n ++ S dst)) (fun _ => True)
      (7 * bitLen n + 7) :=
  Runs.of_eval fun v => ⟨_, _, copyBlock_eval hsd hst hdt [] v (encodeNat n) [] S TermOK.nil
    (by rw [hS, List.append_nil]; rfl), trivial, le_rfl⟩

theorem runs_skipFields {src pk : K} (hne : src ≠ pk) (rest : List Sym) (fs : List ℕ)
    (S : K → List Sym) (hS : S src = hdrSyms fs ++ rest) :
    Runs (WalshCnot1.skipFields src pk fs.length) S
      (Function.update (Function.update S src rest) pk ((hdrSyms fs).reverse ++ S pk))
      (fun _ => True) (3 * (hdrSyms fs).length + 1) := by
  apply Runs.of_eval
  intro v
  obtain ⟨v', e⟩ := WalshCnot1.skipFields_eval hne rest fs v S hS
  exact ⟨v', _, e, trivial, le_rfl⟩

end Generic

/-! ## Embedding a one-stack update -/

section CallInj

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

theorem runs_callInj_update {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {x : L} {v : List Sym} {Q : R → Prop}
    {T : ℕ} (hP : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T := by
  refine runs_callInj (Q := Q) hι l ?_ ?_
  · rwa [Function.update_comp_eq_of_injective B hι x v]
  · intro k hk
    exact Function.update_of_ne (fun h => hk x h.symm) _ _

theorem runs_callInj_id (l : Lens σ R) {P : Prog K (fun _ => Sym) R} {B B' : K → List Sym}
    {Q : R → Prop} {T : ℕ} (hP : Runs P B B' Q T) :
    Runs (callInj id l P) B B' (fun _ => True) T :=
  runs_callInj (ι := id) Function.injective_id l hP (fun k hk => (hk k rfl).elim)

end CallInj

/-! ## Bit lengths -/

theorem bitsVal_lt_two_pow : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by simp
  | b :: l => by
    have ih := bitsVal_lt_two_pow l
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    rw [bitsVal_cons, List.length_cons, pow_succ]
    omega

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  have h := bitsVal_lt_two_pow (encodeNat n)
  rwa [bitsVal_encodeNat] at h

theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  apply WP.W9comp.bitLen_le_of_lt_two_pow
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem bitLen_eight_mul (d : ℕ) : bitLen (8 * d) ≤ bitLen d + 3 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [bitLen, encodeNat_zero]
  · simp [bitLen, encodeNat_eight_mul d (by omega)]

/-! ## The header builder -/

/-- Private scratch stacks of the header builder (besides the adder's own scratch): copies `cp`,
`cd`, `cr`, `cw` of `P, d, r, w`; `d8 = 8d`; the sums `ps = P + 8d`, `ws = w + 8d`; the park
stacks `pk`, `pk2`; the temporary `tmp` of `copyBlock`. -/
inductive HS : Type
  | cp | cd | cr | cw | d8 | ps | ws | pk | pk2 | tmp
  deriving DecidableEq

instance : Fintype HS where
  elems := {.cp, .cd, .cr, .cw, .d8, .ps, .ws, .pk, .pk2, .tmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the header builder: `.inl 0` the slice header, `.inl 1`, `.inl 2` the outputs;
`.inr (.inr j)` the W3 adder's scratch. -/
abbrev HK (ma : ℕ) : Type := KLoc (Fin 3) (HS ⊕ Fin ma)

section Hdr

variable {ma : ℕ}

/-- Copy `P, d, r, w`; duplicate the six tail fields onto stack `2`; restore the header; `8d`. -/
def part1 (ma : ℕ) : SProg (HK ma) :=
  .seq (copyField (.inl 0) (.inr (.inl .cp)) (.inr (.inl .pk)) (.inr (.inl .tmp)))
  (.seq (copyField (.inl 0) (.inr (.inl .cd)) (.inr (.inl .pk)) (.inr (.inl .tmp)))
  (.seq (copyField (.inl 0) (.inr (.inl .cr)) (.inr (.inl .pk)) (.inr (.inl .tmp)))
  (.seq (copyField (.inl 0) (.inr (.inl .cw)) (.inr (.inl .pk)) (.inr (.inl .tmp)))
  (.seq (WalshCnot1.skipFields (.inl 0) (.inr (.inl .pk2)) 6)
  (.seq (dupDrain (.inr (.inl .pk2)) (.inl 0) (.inl 2))
  (.seq (WalshLift.drain (.inr (.inl .pk)) (.inl 0))
  (.seq (copyBlock (.inr (.inl .cd)) (.inr (.inl .d8)) (.inr (.inl .tmp)))
    (times8 (.inr (.inl .d8))))))))))

/-- Push the remaining output fields and clear the scratch. -/
def part3 (ma : ℕ) : SProg (HK ma) :=
  .seq (pushField (.inr (.inl .ws)) (.inl 2) (.inr (.inl .tmp)))
  (.seq (pushField (.inr (.inl .cr)) (.inl 2) (.inr (.inl .tmp)))
  (.seq (pushField (.inr (.inl .cd)) (.inl 2) (.inr (.inl .tmp)))
  (.seq (pushField (.inr (.inl .ps)) (.inl 2) (.inr (.inl .tmp)))
  (.seq (pushField (.inr (.inl .d8)) (.inl 1) (.inr (.inl .tmp)))
  (.seq (pushField (.inr (.inl .cw)) (.inl 1) (.inr (.inl .tmp)))
  (.seq (WalshLift.clear (.inr (.inl .cp))) (.seq (WalshLift.clear (.inr (.inl .cd)))
  (.seq (WalshLift.clear (.inr (.inl .cr))) (.seq (WalshLift.clear (.inr (.inl .cw)))
  (.seq (WalshLift.clear (.inr (.inl .d8))) (.seq (WalshLift.clear (.inr (.inl .ps)))
    (WalshLift.clear (.inr (.inl .ws))))))))))))))

/-- The adder's stack map: operands `x`, `y`, destination `z`; its scratch to `Fin ma`. -/
def ιAdd (ma : ℕ) (x y z : HS) : Loc 3 ma → HK ma
  | .inl ⟨0, _⟩ => .inr (.inl x)
  | .inl ⟨1, _⟩ => .inr (.inl y)
  | .inl ⟨_ + 2, _⟩ => .inr (.inl z)
  | .inr j => .inr (.inr j)

theorem ιAdd_injective {x y z : HS} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (ιAdd ma x y z) := by
  rintro (⟨i, hi⟩ | e) (⟨j, hj⟩ | f) h
  · interval_cases i <;> interval_cases j <;> simp_all [ιAdd]
  · interval_cases i <;> simp [ιAdd] at h
  · interval_cases j <;> simp [ιAdd] at h
  · simp only [ιAdd, Sum.inr.injEq] at h
    rw [h]

/-- The header builder around a W3 adder program `PA`. -/
def hdrProg {Ra : Type} (PA : Prog (Loc 3 ma) (fun _ => Sym) Ra) :
    Prog (HK ma) (fun _ => Sym) (Option Sym × Ra) :=
  .seq (callInj id (Lens.fst _ _) (part1 ma))
  (.seq (callInj (ιAdd ma .cp .d8 .ps) (Lens.snd _ _) PA)
  (.seq (callInj (ιAdd ma .cw .d8 .ws) (Lens.snd _ _) PA)
    (callInj id (Lens.fst _ _) (part3 ma))))

theorem closed_part1 : (part1 ma).Closed := by
  refine WP.W9comp.closed_seq (closed_copyField _ _ _ _) (WP.W9comp.closed_seq
    (closed_copyField _ _ _ _) (WP.W9comp.closed_seq (closed_copyField _ _ _ _)
    (WP.W9comp.closed_seq (closed_copyField _ _ _ _) (WP.W9comp.closed_seq
    (WalshCnot1.closed_skipFields _ _ _) (WP.W9comp.closed_seq (closed_dupDrain _ _ _)
    (WP.W9comp.closed_seq (WalshLift.closed_drain _ _) (WP.W9comp.closed_seq ?_
      (closed_times8 _))))))))
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, pushR, popR, pushC, skip]

theorem closed_part3 : (part3 ma).Closed := by
  refine WP.W9comp.closed_seq (closed_pushField _ _ _) (WP.W9comp.closed_seq
    (closed_pushField _ _ _) (WP.W9comp.closed_seq (closed_pushField _ _ _)
    (WP.W9comp.closed_seq (closed_pushField _ _ _) (WP.W9comp.closed_seq (closed_pushField _ _ _)
    (WP.W9comp.closed_seq (closed_pushField _ _ _) ?_)))))
  exact WP.W9comp.closed_seq (WalshLift.closed_clear _) (WP.W9comp.closed_seq
    (WalshLift.closed_clear _) (WP.W9comp.closed_seq (WalshLift.closed_clear _)
    (WP.W9comp.closed_seq (WalshLift.closed_clear _) (WP.W9comp.closed_seq
    (WalshLift.closed_clear _) (WP.W9comp.closed_seq (WalshLift.closed_clear _)
    (WalshLift.closed_clear _))))))

theorem closed_hdrProg {Ra : Type} {PA : Prog (Loc 3 ma) (fun _ => Sym) Ra} (hPA : PA.Closed) :
    (hdrProg PA).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ closed_part1) (WP.W9comp.closed_seq
    (closed_callInj _ _ hPA) (WP.W9comp.closed_seq (closed_callInj _ _ hPA)
      (closed_callInj _ _ closed_part3)))

/-- One embedded W3 addition: `z += x + y` on the scratch stacks (`z` initially anything). -/
theorem runs_add {Ra : Type} {Ca : ℕ} {PA : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    (hPA : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 ma → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs PA S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
        (Ca * (bitLen a + bitLen b + 1)))
    {x y z : HS} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (B : HK ma → List Sym) (a b : ℕ)
    (hx : B (.inr (.inl x)) = natSyms a) (hy : B (.inr (.inl y)) = natSyms b) :
    Runs (callInj (ιAdd ma x y z) (Lens.snd (Option Sym) Ra) PA) B
      (Function.update B (.inr (.inl z)) (natSyms (a + b) ++ B (.inr (.inl z)))) (fun _ => True)
      (Ca * (bitLen a + bitLen b + 1)) := by
  have h := hPA a b [] [] (B ∘ ιAdd ma x y z) TermOK.nil TermOK.nil
    (by simp [ιAdd, hx]) (by simp [ιAdd, hy])
  exact runs_callInj_update (x := (.inl 2 : Loc 3 ma)) (ιAdd_injective hxy hxz hyz) _ h

theorem length_sliceHdr (P d r w K m j₀ D nS ρ : ℕ) :
    (sliceHdr P d r w K m j₀ D nS ρ).length = bitLen P + bitLen d + bitLen r + bitLen w + 4 +
      (hdrSyms [K, m, j₀, D, nS, ρ]).length := by
  simp only [sliceHdr, hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
    List.length_singleton]
  omega

end Hdr

/-- **K3.4a, the header builder of a CNOT batch, proved** (`CnotHdrStmt`, `Walsh/CnotLeaf.lean`;
Lemma 5.3 (`lem:walsh-lift`) and Proposition 5.5 (`prop:cnot-batch`)). Five-stage program `hdrProg` around the
proved W3 adder `WP.W3.W3_addNat_holds`; scratch `HS ⊕ Fin m_add` (clean). -/
theorem cnotHdr_holds : CnotHdrStmt := by
  obtain ⟨Ca, hAc⟩ := WP.W3.W3_addNat_holds
  obtain ⟨ma, Ra, obsA, PA, -, hRaf, hRan, hPAc, hPA⟩ := hAc ()
  refine ⟨10 * Ca + 400, fun _ => ⟨HS ⊕ Fin ma, inferInstance, inferInstance, Option Sym × Ra,
    hdrProg PA, inferInstance, inferInstance, closed_hdrProg hPAc, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ hrest S hclean hS0
  have hcl : ∀ e : HS, S (.inr (.inl e)) = [] := fun e => hclean (.inl e)
  have hH : S (.inl 0) = natSyms P ++ Sym.mark :: (natSyms d ++ Sym.mark :: (natSyms r ++
      Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)))) := by
    rw [hS0]
    simp [sliceHdr, hdrSyms]
  have R1 := runs_seq (runs_copyField (h := (.inl 0 : HK ma)) (c := .inr (.inl .cp))
      (pk := .inr (.inl .pk)) (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (by simp)
      P _ S hH)
    (runs_seq (runs_copyField (h := (.inl 0 : HK ma)) (c := .inr (.inl .cd))
      (pk := .inr (.inl .pk)) (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (by simp)
      d (natSyms r ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++
        hrest))) _ (by simp))
    (runs_seq (runs_copyField (h := (.inl 0 : HK ma)) (c := .inr (.inl .cr))
      (pk := .inr (.inl .pk)) (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (by simp)
      r (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)) _ (by simp))
    (runs_seq (runs_copyField (h := (.inl 0 : HK ma)) (c := .inr (.inl .cw))
      (pk := .inr (.inl .pk)) (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (by simp)
      w (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest) _ (by simp))
    (runs_seq (runs_skipFields (src := (.inl 0 : HK ma)) (pk := .inr (.inl .pk2)) (by simp)
      hrest [K, m, j₀, D, nS, ρ] _ (by simp))
    (runs_seq (runs_dupDrain (src := (.inr (.inl .pk2) : HK ma)) (d1 := .inl 0) (d2 := .inl 2)
      (by simp) (by simp) (by simp) (hdrSyms [K, m, j₀, D, nS, ρ]).reverse _ (by simp [hcl]))
    (runs_seq (runs_drain (src := (.inr (.inl .pk) : HK ma)) (dst := .inl 0) (by simp)
      (hdrSyms [P, d, r, w]).reverse _ (by simp [hcl, hdrSyms]))
    (runs_seq (runs_copyBlock (src := (.inr (.inl .cd) : HK ma)) (dst := .inr (.inl .d8))
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) d _ (by simp [hcl]))
      (runs_times8 (.inr (.inl .d8) : HK ma) d _ (by simp [hcl])))))))))
  have R := runs_seq (runs_callInj_id (Lens.fst (Option Sym) Ra) R1)
    (runs_seq (runs_add hPA (x := .cp) (y := .d8) (z := .ps) (by simp) (by simp) (by simp) _ P
      (8 * d) (by simp [hcl]) (by simp))
    (runs_seq (runs_add hPA (x := .cw) (y := .d8) (z := .ws) (by simp) (by simp) (by simp) _ w
      (8 * d) (by simp [hcl]) (by simp))
    (runs_callInj_id (Lens.fst (Option Sym) Ra)
    (runs_seq (runs_pushField (src := (.inr (.inl .ws) : HK ma)) (dst := .inl 2)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (w + 8 * d) _ (by simp [hcl]))
    (runs_seq (runs_pushField (src := (.inr (.inl .cr) : HK ma)) (dst := .inl 2)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) r _ (by simp [hcl]))
    (runs_seq (runs_pushField (src := (.inr (.inl .cd) : HK ma)) (dst := .inl 2)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) d _ (by simp [hcl]))
    (runs_seq (runs_pushField (src := (.inr (.inl .ps) : HK ma)) (dst := .inl 2)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (P + 8 * d) _ (by simp [hcl]))
    (runs_seq (runs_pushField (src := (.inr (.inl .d8) : HK ma)) (dst := .inl 1)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) (8 * d) _ (by simp [hcl]))
    (runs_seq (runs_pushField (src := (.inr (.inl .cw) : HK ma)) (dst := .inl 1)
      (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) w _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .cp) : HK ma) (natSyms P) _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .cd) : HK ma) (natSyms d) _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .cr) : HK ma) (natSyms r) _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .cw) : HK ma) (natSyms w) _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .d8) : HK ma) (natSyms (8 * d)) _ (by simp [hcl]))
    (runs_seq (runs_clear (.inr (.inl .ps) : HK ma) (natSyms (P + 8 * d)) _ (by simp [hcl]))
      (runs_clear (.inr (.inl .ws) : HK ma) (natSyms (w + 8 * d)) _ (by simp [hcl])))))))))))))))))
  refine runs_mono (runs_congr R ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | (e | j)
    · fin_cases i
      · simp [hS0, sliceHdr, hdrSyms]
      · simp [hdrSyms]
      · simp [sliceHdr, hdrSyms]
    · cases e <;> simp [hcl]
    · simp
  · have hb8 := bitLen_eight_mul d
    have hbp := bitLen_add_le P (8 * d)
    have hbw := bitLen_add_le w (8 * d)
    have hL := length_sliceHdr P d r w K m j₀ D nS ρ
    simp only [List.length_reverse, length_natSyms, hdrSyms, List.flatMap_cons,
      List.flatMap_nil, List.length_append, List.length_singleton, List.length_nil] at hL ⊢
    nlinarith

end SubNLogN.Machine.WalshScanAux
