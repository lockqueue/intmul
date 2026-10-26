/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Names
import SubNLogN.Machine.K1.Twos
import WP.W9b.Macros
import WP.Top.Clear

/-!
# K7 conversions (`Machine/Pipe/ConvBase.lean`): shared setup of `ConvIn` / `ConvOut`

Helpers for `Pipe.convIn_holds : ConvInStmt` (`ConvIn.lean`) and `Pipe.convOut_holds : ConvOutStmt`
(`ConvOut.lean`); all declarations live in the auxiliary namespace `SubNLogN.Machine.Pipe.ConvAux`.

* Private scratch stacks `CE` (`ra rb`: unary width rulers of ticks `bit true`; `t`: output
  accumulator; `f g`: field buffers of `ConvOut`; `cn tmp`: the width counter and its temporary),
  registers `CReg = Option Sym × Bool × Bool` (current symbol, sign flag, carry).
* The bit ripple `rip neg c`: output `a xor (neg ∧ c)`, carry `a ∨ c`; it is the identity for
  `neg = false` and LSB-first two's-complement negation for `neg = true` (`K1.ripOut_neg`).
* Pure facts: `bitsLE_eq_encodeNat_append` (a `w`-bit field of `n < 2^w` is the minimal binary
  code padded with zeros), `rip_bitsLE` / `rip_twosBits` (sign-magnitude ↔ two's complement), and
  `twosBits_reverse_head` (the most significant bit of a fitting field is the sign).
* The ruler builder `rulerProg` (`rulerProg_runs`): `w` ticks from the binary width `natSyms w`.
-/

namespace SubNLogN.Machine.Pipe.ConvAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
  SubNLogN.Machine.Pipe

/-! ## Bit lists -/

/-- The conversion ripple: output bit `a xor (neg ∧ c)`, carry `a ∨ c`. -/
def rip (neg : Bool) : Bool → List Bool → List Bool
  | _, [] => []
  | c, a :: as => xor a (neg && c) :: rip neg (a || c) as

@[simp] theorem rip_nil (neg c : Bool) : rip neg c [] = [] := rfl

@[simp] theorem rip_cons (neg c a : Bool) (as : List Bool) :
    rip neg c (a :: as) = xor a (neg && c) :: rip neg (a || c) as := rfl

theorem rip_false : ∀ (c : Bool) (as : List Bool), rip false c as = as
  | _, [] => rfl
  | c, a :: as => by rw [rip_cons, rip_false (a || c) as]; simp

theorem rip_true_eq : ∀ (c : Bool) (as : List Bool), rip true c as = K1.ripOut K1.negBit c as as
  | _, [] => rfl
  | c, a :: as => by
    rw [rip_cons, K1.ripOut_cons, rip_true_eq (a || c) as]
    simp [K1.negBit]

theorem length_rip (neg : Bool) : ∀ (c : Bool) (as : List Bool), (rip neg c as).length = as.length
  | _, [] => rfl
  | c, a :: as => by rw [rip_cons, List.length_cons, length_rip neg (a || c) as, List.length_cons]

theorem rip_append (neg : Bool) : ∀ (c : Bool) (as bs : List Bool),
    rip neg c (as ++ bs) = rip neg c as ++ rip neg (as.any id || c) bs
  | c, [], bs => by simp
  | c, a :: as, bs => by
    rw [List.cons_append, rip_cons, rip_cons, rip_append neg (a || c) as bs, List.cons_append]
    congr 2
    cases a <;> cases c <;> simp

theorem rip_replicate_false (neg c : Bool) :
    ∀ n : ℕ, rip neg c (List.replicate n false) = List.replicate n (neg && c)
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, rip_cons, Bool.false_or, rip_replicate_false neg c n,
      List.replicate_succ, Bool.false_xor]

/-! ## Binary codes and fields -/

theorem encodeNat_eq_cons {n : ℕ} (hn : n ≠ 0) : encodeNat n = n.testBit 0 :: encodeNat (n / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : k ≠ 0 := by omega
    have hne : encodeNat k ≠ [] := fun h => hk ((encodeNat_eq_nil_iff k).1 h)
    rw [two_mul, encodeNat_add, if_neg hne]
    have h1 : (k + k) / 2 = k := by omega
    have h2 : (k + k).testBit 0 = false := by
      rw [Nat.testBit_zero]; exact decide_eq_false (by omega)
    rw [h1, h2]
  · rw [two_mul, encodeNat_add_add_one]
    have h1 : (k + k + 1) / 2 = k := by omega
    have h2 : (k + k + 1).testBit 0 = true := by
      rw [Nat.testBit_zero]; exact decide_eq_true (by omega)
    rw [h1, h2]

theorem bitLen_eq_succ {n : ℕ} (hn : n ≠ 0) : bitLen n = bitLen (n / 2) + 1 := by
  unfold bitLen
  rw [encodeNat_eq_cons hn, List.length_cons]

theorem bitLen_zero' : bitLen 0 = 0 := by
  unfold bitLen
  rw [encodeNat_zero]
  rfl

theorem bitLen_le_of_lt : ∀ (w n : ℕ), n < 2 ^ w → bitLen n ≤ w
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this
    rw [bitLen_zero']
  | w + 1, n, h => by
    by_cases hn : n = 0
    · subst hn
      rw [bitLen_zero']
      omega
    · rw [bitLen_eq_succ hn]
      have := bitLen_le_of_lt w (n / 2) (by rw [pow_succ] at h; omega)
      omega

theorem bitsLE_zero_eq (w : ℕ) : bitsLE w 0 = List.replicate w false := by
  simp [bitsLE]

/-- A `w`-bit field of `n < 2^w` is the minimal binary code of `n` padded with zeros. -/
theorem bitsLE_eq_encodeNat_append : ∀ (w n : ℕ), n < 2 ^ w →
    bitsLE w n = encodeNat n ++ List.replicate (w - bitLen n) false
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this
    rw [bitLen_zero', encodeNat_zero]
    rfl
  | w + 1, n, h => by
    by_cases hn : n = 0
    · subst hn
      rw [bitsLE_zero_eq, encodeNat_zero, bitLen_zero', Nat.sub_zero, List.nil_append]
    · rw [K1.bitsLE_succ]
      have h2 : n / 2 < 2 ^ w := by rw [pow_succ] at h; omega
      rw [bitsLE_eq_encodeNat_append w (n / 2) h2, encodeNat_eq_cons hn, bitLen_eq_succ hn]
      have := bitLen_le_of_lt w (n / 2) h2
      have e : w + 1 - (bitLen (n / 2) + 1) = w - bitLen (n / 2) := by omega
      rw [e, List.cons_append]

theorem natAbs_lt_two_pow {w : ℕ} {u : ℤ} (h : FitsTwos w u) (hw : 1 ≤ w) :
    u.natAbs < 2 ^ w := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have h1 := h.1
  have h2 := h.2
  simp only [Nat.add_sub_cancel] at h1 h2
  have e : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; rfl
  have hle : u.natAbs ≤ 2 ^ k := by
    rcases Int.natAbs_eq u with hu | hu <;> omega
  rw [pow_succ]
  have : 0 < 2 ^ k := by positivity
  omega

theorem twosBits_of_nonneg {w : ℕ} {u : ℤ} (h0 : 0 ≤ u) (h1 : u < 2 ^ w) :
    twosBits w u = bitsLE w u.natAbs := by
  unfold twosBits
  rw [Int.emod_eq_of_lt h0 h1]
  congr 1
  have e1 := Int.toNat_of_nonneg h0
  have e2 := Int.natAbs_of_nonneg h0
  omega

theorem lt_two_pow_of_fits {w : ℕ} {u : ℤ} (h : FitsTwos w u) (hw : 1 ≤ w) : u < 2 ^ w := by
  have h2 := h.2
  have : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (by omega)
  omega

/-- Sign-magnitude to two's complement: the ripple of the padded magnitude. -/
theorem rip_bitsLE {w : ℕ} {u : ℤ} (h : FitsTwos w u) (hw : 1 ≤ w) :
    rip (decide (u < 0)) false (bitsLE w u.natAbs) = twosBits w u := by
  by_cases hu : u < 0
  · rw [decide_eq_true hu, rip_true_eq]
    have hpos : (0 : ℤ) ≤ (u.natAbs : ℤ) := by positivity
    have hlt : ((u.natAbs : ℕ) : ℤ) < 2 ^ w := by
      have := natAbs_lt_two_pow h hw
      exact_mod_cast this
    have e : twosBits w (u.natAbs : ℤ) = bitsLE w u.natAbs := by
      rw [twosBits_of_nonneg hpos hlt, Int.natAbs_natCast]
    rw [← e, K1.ripOut_neg]
    congr 1
    have := Int.ofNat_natAbs_of_nonpos hu.le
    omega
  · rw [decide_eq_false hu, rip_false]
    exact (twosBits_of_nonneg (by omega) (lt_two_pow_of_fits h hw)).symm

/-- Two's complement to sign-magnitude: the ripple of the field is the magnitude field. -/
theorem rip_twosBits {w : ℕ} {u : ℤ} (h : FitsTwos w u) (hw : 1 ≤ w) :
    rip (decide (u < 0)) false (twosBits w u) = bitsLE w u.natAbs := by
  by_cases hu : u < 0
  · rw [decide_eq_true hu, rip_true_eq, K1.ripOut_neg]
    have hpos : (0 : ℤ) ≤ -u := by omega
    have hlt : -u < 2 ^ w := by
      have := natAbs_lt_two_pow h hw
      have e := Int.ofNat_natAbs_of_nonpos hu.le
      have : ((u.natAbs : ℕ) : ℤ) < 2 ^ w := by exact_mod_cast this
      omega
    rw [twosBits_of_nonneg hpos hlt, Int.natAbs_neg]
  · rw [decide_eq_false hu, rip_false]
    exact twosBits_of_nonneg (by omega) (lt_two_pow_of_fits h hw)

/-- The most significant bit of a fitting field is the sign. -/
theorem twosBits_reverse_head {w : ℕ} {u : ℤ} (h : FitsTwos w u) (hw : 1 ≤ w) :
    ∃ rest, (twosBits w u).reverse = decide (u < 0) :: rest := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold twosBits bitsLE
  rw [List.range_succ, List.map_append, List.reverse_append]
  refine ⟨(List.map (fun i => (u % 2 ^ (k + 1)).toNat.testBit i) (List.range k)).reverse, ?_⟩
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  congr 1
  have h1 := h.1
  have h2 := h.2
  simp only [Nat.add_sub_cancel] at h1 h2
  have hM : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have hm0 := Int.emod_nonneg u hM.ne'
  have hm1 := Int.emod_lt_of_pos u hM
  set m := u % 2 ^ (k + 1) with hm
  have e := Int.toNat_of_nonneg hm0
  have hpow : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have ek : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; rfl
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hu : u < 0
  · rw [decide_eq_true hu]
    have hmv : m = u + 2 ^ (k + 1) := by
      rw [hm, Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    have hq : m.toNat / 2 ^ k = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    rw [hq]
    rfl
  · rw [decide_eq_false hu]
    have hmv : m = u := by rw [hm, Int.emod_eq_of_lt (by omega) (by omega)]
    have hq : m.toNat / 2 ^ k = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [hq]
    rfl


/-! ## Scratch stacks, registers, names -/

/-- Private scratch stacks of the conversion kernels. -/
inductive CE
  | ra | rb | t | f | g | cn | tmp
  deriving DecidableEq

instance : Fintype CE where
  elems := {CE.ra, CE.rb, CE.t, CE.f, CE.g, CE.cn, CE.tmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the conversion kernels. -/
abbrev CK : Type := KLoc PN CE

/-- Registers: the current symbol, the sign flag, the carry. -/
abbrev CReg : Type := Option Sym × Bool × Bool

/-- Programs of the conversion kernels. -/
abbrev CProg : Type := Prog CK (fun _ => Sym) CReg

/-- Lens onto the current-symbol register (for the `Option Sym` library macros). -/
def lC : Lens CReg (Option Sym) := Lens.fst _ _

abbrev kS : CK := .inl PN.S
abbrev kSrc : CK := .inl PN.src
abbrev kWin : CK := .inl PN.win
abbrev kDst : CK := .inl PN.dst
abbrev kWout : CK := .inl PN.wout
abbrev kRA : CK := .inr CE.ra
abbrev kRB : CK := .inr CE.rb
abbrev kT : CK := .inr CE.t
abbrev kF : CK := .inr CE.f
abbrev kG : CK := .inr CE.g
abbrev kCN : CK := .inr CE.cn
abbrev kTmp : CK := .inr CE.tmp

/-- A ruler tick. -/
abbrev tick : Sym := .bit true

/-- A unary ruler of `n` ticks. -/
abbrev ruler (n : ℕ) : List Sym := List.replicate n tick

theorem ruler_succ (n : ℕ) : ruler (n + 1) = tick :: ruler n := rfl

theorem ruler_eq_map (n : ℕ) : ruler n = (List.replicate n true).map Sym.bit := by
  simp [ruler]

/-! ## Atoms in `Runs` form -/

theorem runs_pushK (k : CK) (x : Sym) (St : CK → List Sym) :
    Runs (.push k (fun _ => x) : CProg) St (Function.update St k (x :: St k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push _ _ _ _ _, trivial, le_rfl⟩

theorem runs_popK (k : CK) (x : Sym) (tl : List Sym) (St : CK → List Sym) (h : St k = x :: tl) :
    Runs (.pop k (fun v _ => v) : CProg) St (Function.update St k tl) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, (Eval.pop _ _ _ _ _).of_eq (by rw [h]; rfl) rfl, trivial, le_rfl⟩

theorem runs_peekK (k : CK) (St : CK → List Sym) :
    Runs (.peek k (fun v o => (o, v.2)) : CProg) St St (fun v => v.1 = (St k).head?) 1 :=
  Runs.of_eval fun v => ⟨((St k).head?, v.2), 1, Eval.peek _ _ _ _ _, rfl, le_rfl⟩

/-- Sequencing a `Runs` component with a loop specified by `Eval` from the registers it leaves. -/
theorem runs_seq_eval {P L : CProg} {S1 S2 S3 : CK → List Sym} {Q1 Q3 : CReg → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1)
    (h2 : ∀ v, Q1 v → ∃ v' t, Eval [] L ⟨v, S2⟩ ⟨v', S3⟩ t ∧ Q3 v' ∧ t ≤ T2) :
    Runs (.seq P L) S1 S3 Q3 (T1 + T2) := by
  intro s hs
  obtain ⟨⟨var1, stk1⟩, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := h1 s hs
  change stk1 = S2 at hs1
  subst hs1
  obtain ⟨v', t, e2, hq, ht⟩ := h2 var1 hq1
  exact ⟨⟨v', S3⟩, t1 + t, Eval.seq e1 e2, ⟨rfl, hq⟩, by omega⟩

/-- A library macro (`Option Sym` registers, exact `Eval` from every register) in `Runs` form,
through `lC`. -/
theorem runs_libC {p : SProg CK} {S S' : CK → List Sym} {T : ℕ}
    (h : ∀ r : Option Sym, ∃ r' t, Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t ∧ t ≤ T) :
    Runs (p.liftRegs lC) S S' (fun _ => True) T :=
  WP.W9b.runs_mono (WP.W9b.runs_liftMacro lC (Qr := fun _ => True)
    (fun r => by obtain ⟨r', t, e, ht⟩ := h r; exact ⟨r', t, e, trivial, ht⟩))
    (fun _ _ => trivial) le_rfl

/-! ## The width ruler -/

/-- Build a ruler of `w` ticks on `ra` from the binary width `natSyms w` on top of `kw` (restored):
copy `w` to the counter `cn`, then push one tick per count-down step. -/
def rulerProg (kw : CK) : CProg :=
  .seq ((copyBlock kw kCN kTmp).liftRegs lC)
    (WP.W9b.cdLoop lC kCN kTmp ((pushC kRA tick).liftRegs lC))

theorem closed_rulerProg (kw : CK) : (rulerProg kw).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lC (by
      simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
        moveBitsDup, dupBody, pushC, pushR, popR, restoreR, Lib.skip]))
    (WP.W9b.closed_cdLoop lC kCN kTmp
      (WP.W9comp.closed_liftRegs lC (by simp [Prog.Closed, Prog.FreeBelow, pushC])))

theorem rulerProg_runs (kw : CK) (hw1 : kw ≠ kCN) (hw2 : kw ≠ kTmp) (w : ℕ) (rest : List Sym)
    (St : CK → List Sym) (hrest : TermOK rest) (hkw : St kw = natSyms w ++ rest)
    (hcn : St kCN = []) :
    Runs (rulerProg kw) St (Function.update St kRA (ruler w ++ St kRA)) (fun _ => True)
      (7 * bitLen w + 7 + (w + WP.W9b.decSum w + 2 * w + 2)) := by
  have e1 := WP.W9b.runs_lift lC (WP.W9b.rs_copy hw1 hw2 (by decide) w rest St hrest hkw)
  rw [hcn, List.append_nil] at e1
  have hbody : ∀ (done : List Unit) (a : Unit) (todo : List Unit), True →
      Runs ((pushC kRA tick).liftRegs lC)
        (Function.update (Function.update St kRA (ruler done.length ++ St kRA)) kCN
          (natSyms (todo.length + 1) ++ []))
        (Function.update (Function.update St kRA (ruler (done ++ [a]).length ++ St kRA)) kCN
          (natSyms (todo.length + 1) ++ []))
        (fun _ => True) 1 := by
    intro done a todo _
    refine WP.W9b.runs_post (WP.W9b.runs_lift lC (WP.W9b.rs_push kRA tick _)) ?_ le_rfl
    funext k
    simp only [Function.update_apply, List.length_append, List.length_singleton, ruler_succ]
    split_ifs <;> simp_all
  have e2 := WP.W9b.cdLoop_runs lC (k := kCN) (t := kTmp) (by decide)
    ((pushC kRA tick).liftRegs lC) (α := Unit)
    (fun done _ => Function.update St kRA (ruler done.length ++ St kRA)) (fun _ => True) []
    TermOK.nil (fun _ => 1) hbody
    (List.replicate w ()) [] (fun _ _ => trivial)
  refine WP.W9b.runs_post (WP.W9b.runs_seq e1 (WP.W9b.runs_pre e2 ?_)) ?_ ?_
  · funext k
    simp only [Function.update_apply, List.length_replicate, List.length_nil, ruler,
      List.replicate_zero, List.nil_append, List.append_nil]
    split_ifs <;> simp_all
  · funext k
    simp only [Function.update_apply, List.length_replicate, WP.W9b.natSyms_zero,
      List.nil_append]
    split_ifs <;> simp_all
  · simp [List.map_replicate, List.sum_replicate]

theorem ruler_rev (w : ℕ) : (List.replicate w true).reverse.map Sym.bit = ruler w := by
  simp [ruler]

/-- Move the ruler back from `rb` to `ra`. -/
theorem moveBack_eval (r : CReg) (n : ℕ) (St : CK → List Sym) (hB : St kRB = ruler n)
    (hA : St kRA = []) :
    Eval [] ((moveBlock kRB kRA).liftRegs lC) ⟨r, St⟩
      ⟨(none, r.2), Function.update (Function.update St kRB []) kRA (ruler n)⟩ (3 * n + 4) := by
  have e := Eval.liftRegs lC (moveBlock_eval (src := kRB) (dst := kRA) (by decide) [] r.1
    (List.replicate n true) [] St TermOK.nil (by rw [hB]; simp [ruler])) r rfl
  refine e.of_eq ?_ (by simp)
  congr 1
  rw [hA, ruler_rev, List.append_nil]

theorem carrSyms_cons (w : ℕ) (z : ℤ × ℤ) (zs : List (ℤ × ℤ)) :
    carrSyms w ((z :: zs).map fun z => [z]) =
      recSyms (crecBits w [z]) ++ carrSyms w (zs.map fun z => [z]) := by
  simp [carrSyms, arrSyms, blk]

theorem carrSyms_nil (w : ℕ) : carrSyms w (List.map (fun z : ℤ × ℤ => [z]) []) = [] := by
  simp [carrSyms, arrSyms, blk]

theorem bitLen_le_self (w : ℕ) : bitLen w ≤ w := bitLen_le_of_lt w w Nat.lt_two_pow_self

end SubNLogN.Machine.Pipe.ConvAux
