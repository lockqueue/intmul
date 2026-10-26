import IntMulTM.Framework.Lib.Counter
import IntMulTM.Framework.Compose

/-!
# IntMulTM.Framework.Lib.Compare — compare two delimited binary numbers

Stacks `k₁ k₂ t₁ t₂` (distinct), alphabet `Sym`; registers `CReg = Option Sym × Option Sym ×
Ordering`. Numbers are normalized LSB-first bit blocks `A.map Sym.bit ++ ra` on `k₁` and
`B.map Sym.bit ++ rb` on `k₂` (e.g. `A = encodeNat x`).

`cmpNum k₁ k₂ t₁ t₂` scans both numbers in lockstep from the LSB (later differences override
earlier ones), then a longer number wins; both numbers and both temporaries are restored. Result
register `= ordOf (bitsVal A) (bitsVal B)` (`= compare`), cost `12 · min |A| |B| + 15`.

The restore phases reuse `Lib.moveBits` / `Lib.restoreR` through register lenses
(`Prog.liftRegs`), exercising the composition layer.
-/

namespace TMFw

namespace Lib

open Turing Computability

/-! ## Pure specification -/

/-- Trichotomy as an `Ordering`. -/
def ordOf (a b : ℕ) : Ordering := if a < b then .lt else if a = b then .eq else .gt

/-- One lockstep position (LSB first): a difference overrides the result so far. -/
def cmpStep (res : Ordering) (x y : Bool) : Ordering :=
  if x = y then res else if x then .gt else .lt

/-- Lockstep scan of the common prefix. -/
def cmpFold : Ordering → List Bool → List Bool → Ordering
  | res, x :: A, y :: B => cmpFold (cmpStep res x y) A B
  | res, _, _ => res

/-- Scan, then the longer list wins. -/
def cmpAll : Ordering → List Bool → List Bool → Ordering
  | res, x :: A, y :: B => cmpAll (cmpStep res x y) A B
  | _, _ :: _, [] => .gt
  | _, [], _ :: _ => .lt
  | res, [], [] => res

theorem ordOf_self (a : ℕ) : ordOf a a = .eq := by simp [ordOf]

theorem bitsVal_lt_two_pow : ∀ L : List Bool, bitsVal L < 2 ^ L.length
  | [] => by simp
  | b :: L => by
    have := bitsVal_lt_two_pow L
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    simp only [bitsVal_cons, List.length_cons, Nat.pow_succ]
    omega

theorem two_pow_le_bitsVal : ∀ L : List Bool, normBits L = L → L ≠ [] →
    2 ^ (L.length - 1) ≤ bitsVal L
  | [], _, h => absurd rfl h
  | b :: L, hn, _ => by
    by_cases hL : L = []
    · subst hL
      cases b
      · simp [normBits] at hn
      · simp
    · have hn' : normBits L = L := by
        cases b
        · simp only [normBits] at hn
          by_cases h0 : normBits L = []
          · simp [h0] at hn
          · rw [if_neg (by simp [h0])] at hn
            exact List.cons.inj hn |>.2
        · simp only [normBits] at hn
          simpa using hn
      have ih := two_pow_le_bitsVal L hn' hL
      have hlen : L.length ≠ 0 := by simpa using hL
      simp only [bitsVal_cons, List.length_cons, Nat.add_sub_cancel]
      have : 2 ^ L.length = 2 ^ (L.length - 1) + 2 ^ (L.length - 1) := by
        rw [← Nat.two_mul, ← Nat.pow_succ']
        congr 1
        omega
      omega

theorem cmpAll_same_length (res : Ordering) : ∀ (A B : List Bool), A.length = B.length →
    cmpAll res A B = if bitsVal A = bitsVal B then res else ordOf (bitsVal A) (bitsVal B)
  | [], [], _ => by simp [cmpAll]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: A, y :: B, h => by
    have ih := cmpAll_same_length (cmpStep res x y) A B (by simpa using h)
    simp only [cmpAll]
    rw [ih]
    rw [bitsVal_cons, bitsVal_cons]
    have hx : x.toNat ≤ 1 := by cases x <;> simp
    have hy : y.toNat ≤ 1 := by cases y <;> simp
    by_cases hv : bitsVal A = bitsVal B
    · rw [if_pos hv, hv]
      cases x <;> cases y <;>
        simp [cmpStep, ordOf]
    · rw [if_neg hv]
      have hne : bitsVal A + bitsVal A + x.toNat ≠ bitsVal B + bitsVal B + y.toNat := by omega
      rw [if_neg hne]
      unfold ordOf
      by_cases hlt : bitsVal A < bitsVal B
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg hv, if_neg (by omega), if_neg hne]

theorem cmpAll_longer_left (res : Ordering) : ∀ (A B : List Bool), B.length < A.length →
    cmpAll res A B = .gt
  | [], _, h => by simp at h
  | _ :: _, [], _ => by simp [cmpAll]
  | x :: A, y :: B, h => by
    simp only [cmpAll]
    exact cmpAll_longer_left _ A B (by simpa using h)

theorem cmpAll_longer_right (res : Ordering) : ∀ (A B : List Bool), A.length < B.length →
    cmpAll res A B = .lt
  | _, [], h => by simp at h
  | [], _ :: _, _ => by simp [cmpAll]
  | x :: A, y :: B, h => by
    simp only [cmpAll]
    exact cmpAll_longer_right _ A B (by simpa using h)

/-- **Value lemma**: for normalized numbers, the scan computes the comparison of the values. -/
theorem cmpAll_eq_ordOf (A B : List Bool) (hA : normBits A = A) (hB : normBits B = B) :
    cmpAll .eq A B = ordOf (bitsVal A) (bitsVal B) := by
  rcases Nat.lt_trichotomy A.length B.length with h | h | h
  · rw [cmpAll_longer_right _ A B h]
    have h1 := bitsVal_lt_two_pow A
    have h2 := two_pow_le_bitsVal B hB (by intro e; subst e; simp at h)
    have h3 : 2 ^ A.length ≤ 2 ^ (B.length - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [ordOf]
    rw [if_pos (by omega)]
  · rw [cmpAll_same_length _ A B h]
    split_ifs with hv
    · rw [hv, ordOf_self]
    · rfl
  · rw [cmpAll_longer_left _ A B h]
    have h1 := bitsVal_lt_two_pow B
    have h2 := two_pow_le_bitsVal A hA (by intro e; subst e; simp at h)
    have h3 : 2 ^ B.length ≤ 2 ^ (A.length - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [ordOf]
    rw [if_neg (by omega), if_neg (by omega)]

theorem cmpFold_finReg (res : Ordering) (ra rb : List Sym) (hra : TermOK ra) (hrb : TermOK rb) :
    ∀ A B : List Bool,
      (if optIsBit ((A.drop (min A.length B.length)).map Sym.bit ++ ra).head? then Ordering.gt
        else if optIsBit ((B.drop (min A.length B.length)).map Sym.bit ++ rb).head? then .lt
        else cmpFold res A B) = cmpAll res A B
  | [], [] => by simp [optIsBit_head?_of_termOK hra, optIsBit_head?_of_termOK hrb, cmpFold, cmpAll]
  | [], y :: B => by simp [optIsBit_head?_of_termOK hra, cmpAll]
  | x :: A, [] => by simp [cmpAll]
  | x :: A, y :: B => by
    have := cmpFold_finReg (cmpStep res x y) ra rb hra hrb A B
    simpa [cmpFold, cmpAll, Nat.succ_min_succ] using this

/-! ## Program -/

/-- Registers: two symbol registers and the running result. -/
abbrev CReg := Option Sym × Option Sym × Ordering

/-- Programs with `CReg` registers. -/
abbrev CProg (K : Type) := Prog K (fun _ => Sym) CReg

/-- Lens on the first symbol register. -/
def L1 : Lens CReg (Option Sym) := Lens.fst _ _

/-- Lens on the second symbol register. -/
def L2 : Lens CReg (Option Sym) := (Lens.snd _ _).comp (Lens.fst _ _)

variable {K : Type}

/-- One lockstep iteration: update the result, save both bits, pop the next ones. -/
def cmpBody (k₁ k₂ t₁ t₂ : K) : CProg K :=
  .seq (.load fun v => (v.1, v.2.1, cmpStep v.2.2 (optBit v.1) (optBit v.2.1)))
    (.seq (Prog.liftRegs L1 (pushR t₁)) (.seq (Prog.liftRegs L2 (pushR t₂))
      (.seq (Prog.liftRegs L1 (popR k₁)) (Prog.liftRegs L2 (popR k₂)))))

/-- Both registers hold bits. -/
def bothBits (v : CReg) : Bool := optIsBit v.1 && optIsBit v.2.1

/-- After the scan: a longer number wins. -/
def finReg (v : CReg) : CReg :=
  (v.1, v.2.1, if optIsBit v.1 then .gt else if optIsBit v.2.1 then .lt else v.2.2)

/-- **Compare** the numbers on `k₁` and `k₂`; result in the third register. -/
def cmpNum (k₁ k₂ t₁ t₂ : K) : CProg K :=
  .seq (Prog.liftRegs L1 (pushC t₁ .mark)) (.seq (Prog.liftRegs L1 (pushC t₂ .mark))
    (.seq (.load fun v => (v.1, v.2.1, .eq))
      (.seq (Prog.liftRegs L1 (popR k₁)) (.seq (Prog.liftRegs L2 (popR k₂))
        (.seq (.loop bothBits (cmpBody k₁ k₂ t₁ t₂))
          (.seq (.load finReg) (.seq (Prog.liftRegs L1 (restoreR k₁))
            (.seq (Prog.liftRegs L2 (restoreR k₂))
              (.seq (Prog.liftRegs L1 (moveBits t₁ k₁)) (Prog.liftRegs L2 (moveBits t₂ k₂)))))))))))

variable [DecidableEq K]

section Proofs

variable {k₁ k₂ t₁ t₂ : K} (h12 : k₁ ≠ k₂) (h1a : k₁ ≠ t₁) (h1b : k₁ ≠ t₂) (h2a : k₂ ≠ t₁)
  (h2b : k₂ ≠ t₂) (hab : t₁ ≠ t₂)

include h12 h1a h1b h2a h2b hab in
theorem cmpLoop_eval (ra rb : List Sym) (hra : TermOK ra) (hrb : TermOK rb) :
    ∀ (A B : List Bool) (res : Ordering) (S : K → List Sym),
      S k₁ = (A.map Sym.bit ++ ra).tail → S k₂ = (B.map Sym.bit ++ rb).tail →
      Eval [] (.loop bothBits (cmpBody k₁ k₂ t₁ t₂))
        ⟨((A.map Sym.bit ++ ra).head?, (B.map Sym.bit ++ rb).head?, res), S⟩
        ⟨(((A.drop (min A.length B.length)).map Sym.bit ++ ra).head?,
          ((B.drop (min A.length B.length)).map Sym.bit ++ rb).head?, cmpFold res A B),
          Function.update (Function.update (Function.update (Function.update S
            k₁ ((A.drop (min A.length B.length)).map Sym.bit ++ ra).tail)
            k₂ ((B.drop (min A.length B.length)).map Sym.bit ++ rb).tail)
            t₁ ((A.take (min A.length B.length)).reverse.map Sym.bit ++ S t₁))
            t₂ ((B.take (min A.length B.length)).reverse.map Sym.bit ++ S t₂)⟩
        (6 * min A.length B.length + 1)
  | [], B, res, S, hA, hB => by
    refine (Eval.loop_false ?_).of_eq ?_ (by simp)
    · simp [bothBits, optIsBit_head?_of_termOK hra]
    · congr 1
      funext k
      simp only [List.length_nil, Nat.zero_min, List.drop_zero, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append, Function.update_apply]
      split_ifs <;> simp_all
  | x :: A, [], res, S, hA, hB => by
    refine (Eval.loop_false ?_).of_eq ?_ (by simp)
    · simp [bothBits, optIsBit_head?_of_termOK hrb]
    · congr 1
      funext k
      simp only [List.length_nil, Nat.min_zero, List.drop_zero, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append, Function.update_apply]
      split_ifs <;> simp_all
  | x :: A, y :: B, res, S, hA, hB => by
    have hA' : S k₁ = A.map Sym.bit ++ ra := hA
    have hB' : S k₂ = B.map Sym.bit ++ rb := hB
    -- the body, atom by atom
    set v0 : CReg := (some (.bit x), some (.bit y), res)
    set v1 : CReg := (some (.bit x), some (.bit y), cmpStep res x y)
    have b1 : Eval [] (.load fun v : CReg => (v.1, v.2.1, cmpStep v.2.2 (optBit v.1) (optBit v.2.1)))
        ⟨v0, S⟩ ⟨v1, S⟩ 1 := Eval.load _ _ _ _
    set S1 := Function.update S t₁ (.bit x :: S t₁) with hS1
    have b2 : Eval [] (Prog.liftRegs L1 (pushR t₁)) ⟨v1, S⟩ ⟨v1, S1⟩ 1 :=
      (Eval.push [] t₁ _ v1 S).of_eq rfl rfl
    set S2 := Function.update S1 t₂ (.bit y :: S1 t₂) with hS2
    have b3 : Eval [] (Prog.liftRegs L2 (pushR t₂)) ⟨v1, S1⟩ ⟨v1, S2⟩ 1 :=
      (Eval.push [] t₂ _ v1 S1).of_eq rfl rfl
    have hS2k1 : S2 k₁ = A.map Sym.bit ++ ra := by
      rw [hS2, Function.update_of_ne h1b, hS1, Function.update_of_ne h1a, hA']
    set S3 := Function.update S2 k₁ (A.map Sym.bit ++ ra).tail with hS3
    have b4 : Eval [] (Prog.liftRegs L1 (popR k₁)) ⟨v1, S2⟩
        ⟨((A.map Sym.bit ++ ra).head?, some (.bit y), cmpStep res x y), S3⟩ 1 := by
      refine (Eval.pop [] k₁ _ v1 S2).of_eq ?_ rfl
      show (⟨((S2 k₁).head?, some (.bit y), cmpStep res x y), Function.update S2 k₁ (S2 k₁).tail⟩ :
        St K (fun _ => Sym) CReg) = _
      rw [hS2k1]
    have hS3k2 : S3 k₂ = B.map Sym.bit ++ rb := by
      rw [hS3, Function.update_of_ne (Ne.symm h12), hS2, Function.update_of_ne h2b, hS1,
        Function.update_of_ne h2a, hB']
    set S4 := Function.update S3 k₂ (B.map Sym.bit ++ rb).tail with hS4
    have b5 : Eval [] (Prog.liftRegs L2 (popR k₂))
        ⟨((A.map Sym.bit ++ ra).head?, some (.bit y), cmpStep res x y), S3⟩
        ⟨((A.map Sym.bit ++ ra).head?, (B.map Sym.bit ++ rb).head?, cmpStep res x y), S4⟩ 1 := by
      refine (Eval.pop [] k₂ _ _ S3).of_eq ?_ rfl
      show (⟨((A.map Sym.bit ++ ra).head?, (S3 k₂).head?, cmpStep res x y),
        Function.update S3 k₂ (S3 k₂).tail⟩ : St K (fun _ => Sym) CReg) = _
      rw [hS3k2]
    have ih := cmpLoop_eval ra rb hra hrb A B (cmpStep res x y) S4
      (by rw [hS4, Function.update_of_ne h12, hS3, Function.update_self])
      (by rw [hS4, Function.update_self])
    have hbody := Eval.seq b1 (Eval.seq b2 (Eval.seq b3 (Eval.seq b4 b5)))
    refine (Eval.loop_true (by rfl) hbody ih).of_eq ?_ ?_
    · simp only [List.length_cons, Nat.succ_min_succ, List.drop_succ_cons, List.take_succ_cons,
        cmpFold]
      congr 1
      funext k
      simp only [hS4, hS3, hS2, hS1, Function.update_apply, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons, Nat.succ_min_succ]
      omega

end Proofs

end Lib

end TMFw
