/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermLeaf
import IntMulTM.Framework.Bits

/-!
# Schedule compiler IO, pure part: list identities for the schedule encoding and number emission

Pure (machine-free) facts used by the IO programs of the runtime schedule compiler
(`PosPermSchedStmt`, `PosPermLeaf.lean`):

* `hdrSyms_cons`, `hdrSyms_append`, `foldl_emit_eq_hdrSyms`: a header block is built in an
  accumulator (which holds the *reverse* of the emitted text) by emitting its fields last first,
  each field `n` contributing `natSyms n ++ [mark]`.
* `cmdSyms_batch_reverse`, `cmdSyms_one_reverse`, `schedSyms_concat_reverse`: the accumulator
  gains `(cmdSyms c).reverse` per command; `schedSyms` of a command list is their concatenation.
* `natSyms_halve`, `halvePush_eq`: halving produces the canonical bits LSB first; pushing them on
  a stack in that order leaves `(natSyms n).reverse` (MSB on top), so one more move (reversal)
  puts `natSyms n` on the accumulator.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-! ## Headers -/

theorem hdrSyms_nil : hdrSyms [] = [] := rfl

theorem hdrSyms_cons (n : ℕ) (fs : List ℕ) :
    hdrSyms (n :: fs) = natSyms n ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

/-- One field emission on the accumulator: `acc ↦ natSyms n ++ [mark] ++ acc`. -/
def emitAcc (acc : List Sym) (n : ℕ) : List Sym := natSyms n ++ Sym.mark :: acc

/-- Emitting the fields of `fs` last first builds `hdrSyms fs` on top of the accumulator. -/
theorem foldl_emit_eq_hdrSyms (fs : List ℕ) (acc : List Sym) :
    fs.reverse.foldl emitAcc acc = hdrSyms fs ++ acc := by
  induction fs generalizing acc with
  | nil => rfl
  | cons n fs ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp [emitAcc, hdrSyms_cons]

theorem pairsSyms_eq {m : ℕ} (ps : List (Fin m × Fin m)) :
    pairsSyms ps = hdrSyms (ps.length :: ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) := rfl

/-! ## Commands and schedules -/

/-- The accumulator gain of a batch command: `[sep2] ++ pairsSyms ps ++ [sep2] ++
hdrSyms [j₀, D, nS, ρ] ++ [tag 0]`. -/
theorem cmdSyms_batch_reverse {m K : ℕ} (j₀ D nS : ℕ) (ρ : Fin K) (ps : List (Fin m × Fin m)) :
    (cmdSyms (PosCmd.batch j₀ D nS ρ ps)).reverse =
      Sym.sep2 :: (pairsSyms ps ++ Sym.sep2 :: (hdrSyms [j₀, D, nS, (ρ : ℕ)] ++ [Sym.tag 0])) := by
  simp [cmdSyms]

/-- The accumulator gain of a single flip: `[sep2] ++ pairsSyms [(c, t)] ++ [tag 1]`. -/
theorem cmdSyms_one_reverse {m K : ℕ} (c t : Fin m) :
    (cmdSyms (PosCmd.one c t : PosCmd m K)).reverse =
      Sym.sep2 :: (pairsSyms [(c, t)] ++ [Sym.tag 1]) := by
  simp [cmdSyms]

theorem schedSyms_nil {m K : ℕ} : schedSyms ([] : List (PosCmd m K)) = [] := rfl

theorem schedSyms_append {m K : ℕ} (l₁ l₂ : List (PosCmd m K)) :
    schedSyms (l₁ ++ l₂) = schedSyms l₁ ++ schedSyms l₂ := by
  simp [schedSyms]

theorem schedSyms_append_reverse {m K : ℕ} (l₁ l₂ : List (PosCmd m K)) :
    (schedSyms (l₁ ++ l₂)).reverse = (schedSyms l₂).reverse ++ (schedSyms l₁).reverse := by
  rw [schedSyms_append, List.reverse_append]

/-- Emitting one more command `c` adds `(cmdSyms c).reverse` on top of the accumulator. -/
theorem schedSyms_concat_reverse {m K : ℕ} (l : List (PosCmd m K)) (c : PosCmd m K) :
    (schedSyms (l ++ [c])).reverse = (cmdSyms c).reverse ++ (schedSyms l).reverse := by
  rw [schedSyms_append_reverse]
  simp [schedSyms]

/-- The final move (reversal) of the accumulator `(schedSyms l).reverse` onto a stack `out`. -/
theorem final_move (w out : List Sym) : w.reverse.reverse ++ out = w ++ out := by
  rw [List.reverse_reverse]

/-! ## Numbers: halving and MSB-first emission -/

/-- Halving step: for `n ≠ 0`, the canonical bits are `n % 2` followed by those of `n / 2`. -/
theorem natSyms_halve (n : ℕ) (hn : n ≠ 0) :
    natSyms n = Sym.bit (decide (n % 2 = 1)) :: natSyms (n / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : k ≠ 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    have h3 : 2 * k % 2 = 0 := by omega
    have hne : encodeNat k ≠ [] := fun h => hk ((TMFw.encodeNat_eq_nil_iff k).1 h)
    simp only [natSyms, h2, h3]
    rw [two_mul, TMFw.encodeNat_add, if_neg hne]
    simp
  · have h2 : (2 * k + 1) / 2 = k := by omega
    have h3 : (2 * k + 1) % 2 = 1 := by omega
    simp only [natSyms, h2, h3]
    rw [two_mul, TMFw.encodeNat_add_add_one]
    simp

/-- The halving loop: push the bits of `n` (LSB first) on a stack `t`. -/
def halvePush : ℕ → List Sym → List Sym
  | 0, t => t
  | n + 1, t => halvePush ((n + 1) / 2) (Sym.bit (decide ((n + 1) % 2 = 1)) :: t)
termination_by n => n
decreasing_by omega

theorem halvePush_zero (t : List Sym) : halvePush 0 t = t := by
  rw [halvePush]

theorem halvePush_pos (n : ℕ) (hn : n ≠ 0) (t : List Sym) :
    halvePush n t = halvePush (n / 2) (Sym.bit (decide (n % 2 = 1)) :: t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [halvePush]

/-- **MSB-first digits.** Pushing the bits of `n` LSB first leaves `(natSyms n).reverse`
(most significant bit on top). -/
theorem halvePush_eq (n : ℕ) (t : List Sym) : halvePush n t = (natSyms n).reverse ++ t := by
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [halvePush_zero]
      simp [natSyms, TMFw.encodeNat_zero]
    · rw [halvePush_pos n hn.ne', ih (n / 2) (Nat.div_lt_self hn (by norm_num)),
        natSyms_halve n hn.ne']
      simp

/-- Moving a whole stack `t` onto `a` (pop/push until `t` is empty) gives `t.reverse ++ a`; for
`t = (natSyms n).reverse` this is `natSyms n ++ a`. -/
theorem move_halvePush (n : ℕ) (a : List Sym) :
    (halvePush n []).reverse ++ a = natSyms n ++ a := by
  rw [halvePush_eq, List.append_nil, List.reverse_reverse]

end SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO
