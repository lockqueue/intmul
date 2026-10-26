import Contracts.Machine.Common
import IntMulTM.Framework.Lib.CompareEval
import IntMulTM.Framework.Lib.Counter

/-!
# Contracts.Machine.W3 — binary arithmetic on the machine, linear cost

Conventions: `Contracts.Machine.Common`. In short:
* unsigned `n` = `natSyms n ++ rest` (LSB on top, canonical, `0 ↦ []`, `TermOK rest`);
* signed `z` = `intSyms z ++ rest` (sign symbol on top: `neg` iff `z < 0`, zero = `[pos]`; then the
  magnitude LSB-first; then a terminator);
* every contract is an `MContract`: a closed program over local stacks `Loc n m`, named stacks
  `.inl 0, .inl 1, …` in the order listed in its docstring, `m ≤ 4` scratch stacks (arbitrary
  content, restored), private finite registers; exact final stacks, so all other stacks are
  untouched;
* costs are `C · (sum of operand bit lengths + 1)`, plus the shift amount for shifts, with one
  constant `C` per contract (uniform in compile-time parameters).

**Proved instances** (non-vacuity, from the seed library; bottom of the file): `W3_copyNat`,
`W3_cmpNat`, `W3_isZeroNat`, `W3_incNat`, `W3_decNat`, `W3_natToInt`, `W3_splitSign`.

**Mutation-test ideas** (to run against any implementation):
* `add` returning `a + b + 1`, or dropping the final carry: the exact post-state fails at
  `a = b = 1`.
* A quadratic `add` that rescans from the LSB for every bit: `Triple.cost_ge` against
  `C·(|a|+|b|+1)` fails for `|a| > 2C`. This is the `Test.Mutation` pattern.
* `shrVar` that pops `c` bits without stopping at the terminator: it eats the terminator, so the
  post-state is wrong when `c > |a|`.
* `negInt` that flips the sign of zero: produces `[neg]`, which violates canonicity (`intSyms 0 = [pos]`).
* `splitAt` that leaves high zeros in the low part: not `natSyms (a % 2^c)`.
-/

namespace TMFw.Contracts

open Computability TMFw.Lib

/-! ## Unsigned: data movement, normalization, tests -/

/-- **copy** `y += a` (source preserved). Stacks: `x` source, `y` destination. Cost `C·(|a|+1)`. -/
def W3_copyNat : Prop :=
  MContract Unit 2 4 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
        (C * (bitLen a + 1))

/-- **drop** (in place): pop the number on `x`, keeping its terminator. Cost `C·(|a|+1)`. -/
def W3_dropNat : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0) rx) (fun _ => True) (C * (bitLen a + 1))

/-- **normalize** (in place): an arbitrary LSB-first bit block `l` (high zeros allowed) becomes the
canonical `natSyms (bitsVal l)`. Cost `C·(|l|+1)`. -/
def W3_normNat : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (l : List Bool) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = l.map Sym.bit ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms (bitsVal l) ++ rx)) (fun _ => True)
        (C * (l.length + 1))

/-- **zero test**: `obs = decide (a = 0)`; stacks unchanged. Cost `C`. -/
def W3_isZeroNat : Prop :=
  MContract Unit 1 4 Bool fun _ m _ C obs P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S S (fun r => obs r = decide (a = 0)) C

/-- **compare** `obs = ordOf a b` (`if a < b then lt else if a = b then eq else gt`); stacks
unchanged. Stacks `x`, `y`. Cost `C·(|a|+|b|+1)`. -/
def W3_cmpNat : Prop :=
  MContract Unit 2 4 Ordering fun _ m _ C obs P =>
    ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S S (fun r => obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

/-! ## Unsigned arithmetic -/

/-- **add** `z += a + b`. Stacks `x`, `y` (operands, restored), `z` (destination).
Cost `C·(|a|+|b|+1)`. -/
def W3_addNat : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1))

/-- **subtract** `z += a - b`, for `b ≤ a`. Stacks `x`, `y` (restored), `z`. Cost `C·(|a|+|b|+1)`. -/
def W3_subNat : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry → b ≤ a →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a + bitLen b + 1))

/-! ## Shifts, split, concatenation -/

/-- **shift left by a compile-time constant** `k` (in place): `a ↦ a·2^k`. Cost `C·(k+1)`. LSB on
top, so this pushes `k` zeros unless `a = 0`. -/
def W3_shlConst : Prop :=
  MContract ℕ 1 4 Unit fun k m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms (a * 2 ^ k) ++ rx)) (fun _ => True)
        (C * (k + 1))

/-- **shift right by a compile-time constant** `k` (in place): `a ↦ a / 2^k`. Cost `C·(k+1)`. -/
def W3_shrConst : Prop :=
  MContract ℕ 1 4 Unit fun k m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms (a / 2 ^ k) ++ rx)) (fun _ => True)
        (C * (k + 1))

/-- **shift left by a counter** (in place): stacks `x` (number), `c` (counter, restored);
`a ↦ a·2^c`. Cost `C·(c + |c| + 1)`. -/
def W3_shlVar : Prop :=
  MContract Unit 2 4 Unit fun _ m _ C _ P =>
    ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (C * (c + bitLen c + 1))

/-- **shift right by a counter** (in place): stacks `x`, `c` (restored); `a ↦ a / 2^c`.
Cost `C·(min c |a| + |c| + 1)`. -/
def W3_shrVar : Prop :=
  MContract Unit 2 4 Unit fun _ m _ C _ P =>
    ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
        (C * (min c (bitLen a) + bitLen c + 1))

/-- **split at a counter position**. Stacks: `x` (number; keeps the high part), `c` (counter,
restored), `y` (receives the canonical low part). Effect: `x ↦ a / 2^c`, `y += a % 2^c`.
Cost `C·(min c |a| + |c| + 1)`. -/
def W3_splitAt : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
          (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
        (C * (min c (bitLen a) + bitLen c + 1))

/-- **concatenate at a counter position**. Stacks: `x` (high part `hi`; receives the result), `c`
(counter, restored), `y` (low part `lo < 2^c`, consumed down to its terminator). Effect:
`x ↦ lo + hi·2^c`. Cost `C·(c + |c| + 1)`. -/
def W3_concatAt : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (hi lo c : ℕ) (rx rc ry : List Sym) (S : Loc 3 m → List Sym),
      TermOK rx → TermOK rc → TermOK ry → lo < 2 ^ c →
      S (.inl 0) = natSyms hi ++ rx → S (.inl 1) = natSyms c ++ rc →
      S (.inl 2) = natSyms lo ++ ry →
      Runs P S (Function.update (Function.update S (.inl 0) (natSyms (lo + hi * 2 ^ c) ++ rx))
          (.inl 2) ry) (fun _ => True)
        (C * (c + bitLen c + 1))

/-! ## Counters (binary, LSB on top) -/

/-- **increment** (in place) `a ↦ a + 1`. Cost `C·(ones (encodeNat a) + 1)`, the carry run.
Amortised: by `incSeqCost_le`, `m` increments from `0` cost `≤ 2C·m`. -/
def W3_incNat : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
        (C * (ones (encodeNat a) + 1))

/-- **decrement** (in place) `a + 1 ↦ a`. Cost `C·(zerosLead (encodeNat (a+1)) + 1)`, the borrow
run. Amortised: `W3_dec_amortised`. -/
def W3_decNat : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (C * (zerosLead (encodeNat (a + 1)) + 1))

/-- **Amortisation of decrements** (pure statement, open; owner W3). `k ≤ c` consecutive
decrements starting at `c` cost `O(k + |c|)`. -/
def W3_dec_amortised : Prop :=
  ∀ c k : ℕ, k ≤ c →
    ((List.range k).map fun i => zerosLead (encodeNat (c - i)) + 1).sum ≤ 2 * k + bitLen c

/-! ## Signed (sign-magnitude) -/

/-- **ℕ → ℤ** (in place): `natSyms a ↦ intSyms a` (push `pos`). Cost `C`. -/
def W3_natToInt : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0) (intSyms (a : ℤ) ++ rx)) (fun _ => True) C

/-- **attach a compile-time sign** (in place): `natSyms a ↦ intSyms (±a)`; zero stays `[pos]`.
Cost `C`. -/
def W3_attachSign : Prop :=
  MContract Bool 1 4 Unit fun isNeg m _ C _ P =>
    ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs P S (Function.update S (.inl 0)
          (intSyms (if isNeg then -(a : ℤ) else (a : ℤ)) ++ rx)) (fun _ => True) C

/-- **split off the sign** (in place): `intSyms z ↦ natSyms |z|`, `obs = decide (z < 0)`.
Cost `C`. -/
def W3_splitSign : Prop :=
  MContract Unit 1 4 Bool fun _ m _ C obs P =>
    ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = intSyms z ++ rx →
      Runs P S (Function.update S (.inl 0) (natSyms z.natAbs ++ rx))
        (fun r => obs r = decide (z < 0)) C

/-- **negate** (in place): `z ↦ -z`; zero stays `[pos]`. Cost `C`. -/
def W3_negInt : Prop :=
  MContract Unit 1 4 Unit fun _ m _ C _ P =>
    ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = intSyms z ++ rx →
      Runs P S (Function.update S (.inl 0) (intSyms (-z) ++ rx)) (fun _ => True) C

/-- **sign / zero test**: `obs = cmpZ z 0`; stacks unchanged. Cost `C`. -/
def W3_signInt : Prop :=
  MContract Unit 1 4 Ordering fun _ m _ C obs P =>
    ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx →
      S (.inl 0) = intSyms z ++ rx →
      Runs P S S (fun r => obs r = cmpZ z 0) C

/-- **add** (signed) `z += a + b`. Stacks `x`, `y` (restored), `z`. Cost `C·(|a|+|b|+1)`, bit
lengths of the magnitudes. -/
def W3_addInt : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- **subtract** (signed) `z += a - b`. Cost `C·(|a|+|b|+1)`. -/
def W3_subInt : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
      Runs P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- **compare** (signed) `obs = cmpZ a b`; stacks unchanged. Cost `C·(|a|+|b|+1)`. -/
def W3_cmpInt : Prop :=
  MContract Unit 2 4 Ordering fun _ m _ C obs P =>
    ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
      Runs P S S (fun r => obs r = cmpZ a b) (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- The constant multiplications / exact divisions that Toom-3 evaluation and interpolation use. -/
inductive SmallOp
  | mul2
  | mul3
  | div2
  | div3

/-- Meaning of a `SmallOp` (`/` on `ℤ` is exact under `SmallOp.ok`). -/
def SmallOp.apply : SmallOp → ℤ → ℤ
  | .mul2, z => 2 * z
  | .mul3, z => 3 * z
  | .div2, z => z / 2
  | .div3, z => z / 3

/-- Precondition of a `SmallOp`: divisions must be exact. -/
def SmallOp.ok : SmallOp → ℤ → Prop
  | .div2, z => 2 ∣ z
  | .div3, z => 3 ∣ z
  | _, _ => True

/-- **multiply by 2 or 3, exact divide by 2 or 3** (signed, in place; compile-time `op`).
Cost `C·(|z|+1)`. -/
def W3_smallOpInt : Prop :=
  MContract SmallOp 1 4 Unit fun op m _ C _ P =>
    ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 m → List Sym), TermOK rx → op.ok z →
      S (.inl 0) = intSyms z ++ rx →
      Runs P S (Function.update S (.inl 0) (intSyms (op.apply z) ++ rx)) (fun _ => True)
        (C * (bitLen z.natAbs + 1))

/-! ## Proved instances (non-vacuity) -/

theorem w3_copyNat : W3_copyNat := by
  refine ⟨7, fun _ => ⟨1, Option Sym, fun _ => (), copyBlock (.inl 0) (.inl 1) (.inr 0),
    by decide, inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
      dupBody, pushC, pushR, popR, restoreR, skip]
  · intro a rx S hrx hx
    refine Runs.of_eval fun v => ⟨some .mark, _,
      copyBlock_eval (src := .inl 0) (dst := .inl 1) (tmp := .inr 0) (by decide) (by decide)
        (by decide) [] v (encodeNat a) rx S hrx hx, trivial, ?_⟩
    simp only [bitLen]
    omega

theorem w3_cmpNat : W3_cmpNat := by
  refine ⟨15, fun _ => ⟨2, CReg, fun v => v.2.2, cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1),
    by decide, inferInstance, ⟨(none, none, .eq)⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, Prog.liftRegs, pushC, pushR, popR,
      restoreR, moveBits, moveBitsBody, skip]
  · intro a b rx ry S hrx hry hx hy
    refine Runs.of_eval fun v => ⟨_, _,
      cmpNum_eval (k₁ := .inl 0) (k₂ := .inl 1) (t₁ := .inr 0) (t₂ := .inr 1) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) v (encodeNat a) (encodeNat b)
        rx ry S hrx hry hx hy, ?_, ?_⟩
    · show cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b
      rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
        bitsVal_encodeNat]
    · simp only [bitLen]
      omega

theorem w3_isZeroNat : W3_isZeroNat := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun r => !optIsBit r, zeroTest (.inl 0), Nat.zero_le _,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, zeroTest, peekR]
  · intro a rx S hrx hx
    refine Runs.of_eval fun v => ?_
    obtain ⟨r, hr, e⟩ := zeroTest_eval (k := .inl 0) [] v a rx S hrx hx
    exact ⟨r, 1, e, by simp [hr], le_refl _⟩

theorem w3_incNat : W3_incNat := by
  refine ⟨9, fun _ => ⟨1, Option Sym, fun _ => (), inc (.inl 0) (.inr 0), by decide,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, restoreR,
      pushR, skip, moveBits, moveBitsBody]
  · intro a rx S hrx hx
    refine Runs.of_eval fun v => ?_
    obtain ⟨c, hc, e⟩ := inc_eval (k := .inl 0) (t := .inr 0) (by decide) [] v (encodeNat a) rx S
      hrx hx
    refine ⟨some .mark, c, ?_, trivial, by omega⟩
    rw [natSyms, encodeNat_succ]
    exact e

theorem w3_decNat : W3_decNat := by
  refine ⟨8, fun _ => ⟨1, Option Sym, fun _ => (), dec (.inl 0) (.inr 0), by decide,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, pushC, popR, peekR,
      pushR, skip, moveBits, moveBitsBody]
  · intro a rx S hrx hx
    exact Runs.of_eval fun v => ⟨some .mark, _,
      dec_eval (k := .inl 0) (t := .inr 0) (by decide) [] v a rx S hrx hx, trivial, by omega⟩

theorem w3_natToInt : W3_natToInt := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun _ => (), pushC (.inl 0) .pos, Nat.zero_le _,
    inferInstance, ⟨none⟩, by simp [Prog.Closed, Prog.FreeBelow, pushC], ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_refl _⟩
  have e : Eval [] (pushC (.inl 0 : Loc 1 0) .pos) ⟨v, S⟩
      ⟨v, Function.update S (.inl 0) (Sym.pos :: S (.inl 0))⟩ 1 := Eval.push _ _ _ _ _
  refine e.of_eq ?_ rfl
  rw [intSyms_natCast, hx, List.cons_append]

theorem w3_splitSign : W3_splitSign := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun r => decide (r = some Sym.neg), popR (.inl 0),
    Nat.zero_le _, inferInstance, ⟨none⟩, by simp [Prog.Closed, Prog.FreeBelow, popR], ?_⟩⟩
  intro z rx S hrx hx
  refine Runs.of_eval fun v => ⟨some (sgnSym z), 1, ?_, ?_, le_refl _⟩
  · have e : Eval [] (popR (.inl 0 : Loc 1 0)) ⟨v, S⟩
        ⟨(S (.inl 0)).head?, Function.update S (.inl 0) (S (.inl 0)).tail⟩ 1 := Eval.pop _ _ _ _ _
    refine e.of_eq ?_ rfl
    simp [hx, intSyms]
  · by_cases h : z < 0 <;> simp [sgnSym, h]

#assert_std_axioms w3_copyNat w3_cmpNat w3_isZeroNat w3_incNat w3_decNat w3_natToInt w3_splitSign

end TMFw.Contracts
