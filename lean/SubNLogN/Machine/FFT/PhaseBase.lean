/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W7k2.B.Base
import SubNLogN.Machine.Contracts.Streams

/-!
# K4-TW (`Machine/FFT/PhaseBase.lean`): generic host-level tools for the K4 phase table

**Scope (honest summary).** Algorithm-free machine tools, all proved (no `sorry`), on top of the
proved host-call layer of `WP.W7k2` (`callI`, `HT`, `HT.callI_upd`, `cdLoop`, …):
* `SpecSubNat`, `SpecShrVar`: the bodies of `W3_subNat`, `W3_shrVar` (`Contracts/Machine/W3.lean`)
  for one instance, with host rules `HT.subNat`, `HT.shrVar`.
* `HT.cdLoop'`: the counted loop `cdLoop` of `WP/W7k2/Loops.lean` with the body hypothesis needed
  only for the iterations that run (`i < N`).
* `emitStep`, `emitBits`: emit the `w`-bit field `bitsLE w N` of a natural `N < 2^w` (LSB first)
  onto a stack, bit by bit, from `natSyms N` (consumed). `HT.emitBits`.
* `moveF`: `TMFw.Lib.moveBlock` (move a bit block, reversing it) inside a host program.

Design of the phase-table builder that uses these tools: `Machine/FFT/PhaseTable.lean`.
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts WP.W7k2 Computability

/-! ## 1. Two more W3 contract bodies -/

/-- Body of `W3_subNat` for one instance (`Contracts/Machine/W3.lean:90`). -/
def SpecSubNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_shrVar` for one instance (`Contracts/Machine/W3.lean:127`). -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

theorem SpecSubNat.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubNat I C) (hC : C ≤ C') :
    SpecSubNat I C' := fun a b rx ry S h1 h2 h3 h4 h5 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4 h5) (Nat.mul_le_mul_right _ hC)

theorem SpecShrVar.mono {I : Inst 2 4 Unit} {C C' : ℕ} (h : SpecShrVar I C) (hC : C ≤ C') :
    SpecShrVar I C' := fun a c rx rc S h1 h2 h3 h4 =>
  runs_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

variable {a b : ℕ} {σ : Type}

theorem HT.subNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSubNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hyx : y ≤ x) (hx : B sx = natSyms x ++ rx) (hy : B sy = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (natSyms (x - y) ++ B sz))
      (C * (bitLen x + bitLen y + 1)) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _
    (hI x y rx ry _ hrx hry hyx hx hy) ρ

theorem HT.shrVar {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecShrVar I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s c : Loc a b) (hnd : [s, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hB : B s = natSyms x ++ rx) (hC : B c = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s, c] dflt l) (Function.update B s (natSyms (x / 2 ^ y) ++ rx))
      (C * (min y (bitLen x) + bitLen y + 1)) :=
  HT.callI_upd I [s, c] dflt hnd rfl hcap l B (.inl 0) _ (hI x y rx ry _ hrx hry hB hC) ρ

/-! ## 2. Counted loop, body needed only for the iterations that run -/

/-- **Counted loop rule** (`cdLoop`, `WP/W7k2/Loops.lean`), with the body hypothesis only for
`i < N`. `St i` is the state with counter `i`; the body turns `St (i+1)` with the counter already
decremented to `i` into `St i`. -/
theorem HT.cdLoop' {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : Loc a b)
    (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc) (St : ℕ → Loc a b → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (cb : ℕ → ℕ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (N : ℕ)
    (hbody : ∀ i, i < N →
      HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT ρ (St N) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) N) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) ρ
  have h0 : Triple ρ (fun s => s.stk = St N) (callI Iz [ctr] dflt lz)
      (fun s => N ≤ N ∧ s.stk = St N ∧ Iz.obs (lz.get s.var) = decide (N = 0)) Cz :=
    Triple.post (htest N) (fun s hs => ⟨le_rfl, hs.1, hs.2⟩)
  refine Triple.seq h0 ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ N ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) ?_ ?_ ?_ N
  · exact Triple.post hloop (fun s hs => hs.2.1)
  · intro k
    by_cases hk : k < N
    · have hdec : HT ρ (St (k + 1)) (callI Id [ctr] dflt ld)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
          (hd k rc _ hrc (hSt (k + 1))) ρ
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k hk)) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤
          Cd * (bitLen (k + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      show _ ≤ Cd * (bitLen (k + 1) + 1) + cb k + Cz
      omega
    · intro s hs
      exact absurd hs.1 (by omega)
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

/-! ## 3. Emitting a fixed-width field -/

/-- One emission step: if the top of `X` is a bit, move it onto `F`; otherwise push `0` onto `F`
(the number on `X` is exhausted; its terminator stays). -/
def emitStep (lS : Lens σ (Option Sym)) (X F : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (Prog.peek X (fun v o => lS.set v o)).seq
    (.ite (fun v => optIsBit (lS.get v))
      ((popR' lS X).seq (Prog.push F (fun v => (lS.get v).getD Sym.sep)))
      (WP.W7k2.pushS F (Sym.bit false)))

theorem emitStep_closed (lS : Lens σ (Option Sym)) (X F : Loc a b) :
    (emitStep lS X F).Closed :=
  ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩

theorem HT.emitStep_bit (lS : Lens σ (Option Sym)) (X F : Loc a b) (hXF : X ≠ F)
    (B : Loc a b → List Sym) (c : Bool) (rest : List Sym) (hB : B X = Sym.bit c :: rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (emitStep lS X F)
      (Function.update (Function.update B X rest) F (Sym.bit c :: B F)) 4 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 : Eval ρ (Prog.peek X (fun v o => lS.set v o)) ⟨v, S⟩
      ⟨lS.set v (some (Sym.bit c)), S⟩ 1 := by
    have := Eval.peek ρ X (fun v o => lS.set v o) v S
    rw [hB] at this
    exact this
  have e2 : Eval ρ (popR' lS X) ⟨lS.set v (some (Sym.bit c)), S⟩
      ⟨lS.set (lS.set v (some (Sym.bit c))) (some (Sym.bit c)), Function.update S X rest⟩ 1 := by
    have := Eval.pop ρ X (fun v o => lS.set v o) (lS.set v (some (Sym.bit c))) S
    rw [hB] at this
    exact this
  have e3 := Eval.push ρ F (fun v => (lS.get v).getD Sym.sep)
    (lS.set (lS.set v (some (Sym.bit c))) (some (Sym.bit c))) (Function.update S X rest)
  have hc : optIsBit (lS.get (lS.set v (some (Sym.bit c)))) = true := by
    rw [lS.get_set]; rfl
  refine ⟨_, 1 + ((1 + 1) + 1), Eval.seq e1 (Eval.ite_true hc (Eval.seq e2 e3)), ?_, le_rfl⟩
  show Function.update (Function.update S X rest) F
      ((lS.get (lS.set (lS.set v (some (Sym.bit c))) (some (Sym.bit c)))).getD Sym.sep ::
        Function.update S X rest F) = _
  rw [lS.get_set, Function.update_of_ne (Ne.symm hXF)]
  rfl

theorem HT.emitStep_end (lS : Lens σ (Option Sym)) (X F : Loc a b)
    (B : Loc a b → List Sym) (hB : TermOK (B X))
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (emitStep lS X F) (Function.update B F (Sym.bit false :: B F)) 3 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.peek ρ X (fun v o => lS.set v o) v S
  have e2 := Eval.push ρ F (fun _ => Sym.bit false) (lS.set v (S X).head?) S
  have hc : optIsBit (lS.get (lS.set v (S X).head?)) = false := by
    rw [lS.get_set]; exact optIsBit_head?_of_termOK hB
  exact ⟨_, 1 + (1 + 1), Eval.seq e1 (Eval.ite_false hc e2), rfl, le_rfl⟩

/-! ## 4. `natSyms` peeling -/

theorem bitLen_one' : bitLen 1 = 1 := by simpa using bitLen_two_pow 0

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, TMFw.encodeNat_zero]

/-- A positive number: its least significant bit, then the rest. -/
theorem natSyms_pos {m : ℕ} (hm : m ≠ 0) :
    natSyms m = Sym.bit (decide (m % 2 = 1)) :: natSyms (m / 2) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hn : n ≠ 0 := by omega
    have hne : encodeNat n ≠ [] := fun h => hn ((TMFw.encodeNat_eq_nil_iff n).mp h)
    have e1 : 2 * n = n + n := by ring
    have e2 : 2 * n % 2 = 0 := by omega
    have e3 : 2 * n / 2 = n := by omega
    unfold natSyms
    rw [e2, e3, e1, TMFw.encodeNat_add, if_neg hne]
    rfl
  · have e1 : 2 * n + 1 = n + n + 1 := by ring
    have e2 : (2 * n + 1) % 2 = 1 := by omega
    have e3 : (2 * n + 1) / 2 = n := by omega
    unfold natSyms
    rw [e2, e3, e1, TMFw.encodeNat_add_add_one]
    rfl

theorem termOK_natSyms_zero_append {r : List Sym} (h : TermOK r) : TermOK (natSyms 0 ++ r) := by
  rw [natSyms_zero', List.nil_append]; exact h

/-! ## 5. `emitBits`: a `w`-bit field, from a number -/

/-- Emit the `w`-bit field `bitsLE w N` of the number `N` on `X` onto `F`, least significant bit
first, so that `F` receives the field reversed (most significant bit on top). The count is a copy
of `w` (stack `vw`) on the counter stack `wc`. -/
def emitBits (Icp : Inst 2 4 Unit) (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit)
    (lS : Lens σ (Option Sym)) (lcp : Lens σ Icp.R) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (vw wc X F dflt : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (callI Icp [vw, wc] dflt lcp).seq (cdLoop Iz Id lz ld wc dflt (emitStep lS X F))

theorem emitBits_closed (Icp : Inst 2 4 Unit) (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit)
    (lS : Lens σ (Option Sym)) (lcp : Lens σ Icp.R) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (vw wc X F dflt : Loc a b) : (emitBits Icp Iz Id lS lcp lz ld vw wc X F dflt).Closed :=
  ⟨callI_closed _ _ _ _, cdLoop_closed _ _ _ _ _ _ _ (emitStep_closed _ _ _)⟩

/-- The emission state with counter `i` (`w - i` bits emitted). -/
def emitSt (B : Loc a b → List Sym) (wc X F : Loc a b) (rx : List Sym) (w N i : ℕ) :
    Loc a b → List Sym :=
  Function.update (Function.update (Function.update B wc (natSyms i ++ B wc)) X
    (natSyms (N / 2 ^ (w - i)) ++ rx)) F
    (((List.range (w - i)).map N.testBit).reverse.map Sym.bit ++ B F)

theorem upd3_collapse {α β : Type} [DecidableEq α] (B0 : α → β) (p q r : α) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (v1 v2 v3 v4 v5 v6 : β) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update B0 p v1) q v2) r v3) p v4) q v5) r v6 =
      Function.update (Function.update (Function.update B0 p v4) q v5) r v6 := by
  funext g
  by_cases h1 : g = r
  · subst h1; simp only [Function.update_self]
  · by_cases h2 : g = q
    · subst h2; simp only [Function.update_self, Function.update_of_ne h1]
    · by_cases h3 : g = p
      · subst h3
        simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

theorem upd2_collapse {α β : Type} [DecidableEq α] (B0 : α → β) (p q r : α) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (v1 v2 v3 v4 v6 : β) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update B0 p v1) q v2) r v3) p v4) r v6 =
      Function.update (Function.update (Function.update B0 p v4) q v2) r v6 := by
  funext g
  by_cases h1 : g = r
  · subst h1; simp only [Function.update_self]
  · by_cases h2 : g = q
    · subst h2
      simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne hpq.symm]
    · by_cases h3 : g = p
      · subst h3
        simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

theorem emitSt_step (B : Loc a b → List Sym) (wc X F : Loc a b) (hXF : X ≠ F) (hXw : X ≠ wc)
    (hFw : F ≠ wc) (rx : List Sym) (hrx : TermOK rx) (w N i : ℕ) (hi : i < w)
    (lS : Lens σ (Option Sym)) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ (Function.update (emitSt B wc X F rx w N (i + 1)) wc (natSyms i ++ B wc))
      (emitStep lS X F) (emitSt B wc X F rx w N i) 4 := by
  obtain ⟨k, hk⟩ : ∃ k, w - (i + 1) = k := ⟨_, rfl⟩
  have hk1 : w - i = k + 1 := by omega
  set S' := Function.update (emitSt B wc X F rx w N (i + 1)) wc (natSyms i ++ B wc) with hS'
  have hSX : S' X = natSyms (N / 2 ^ k) ++ rx := by
    rw [hS', Function.update_of_ne hXw, emitSt, Function.update_of_ne hXF, Function.update_self, hk]
  have hSF : S' F = ((List.range k).map N.testBit).reverse.map Sym.bit ++ B F := by
    rw [hS', Function.update_of_ne hFw, emitSt, Function.update_self, hk]
  have hrange : ((List.range (k + 1)).map N.testBit).reverse.map Sym.bit =
      Sym.bit (N.testBit k) :: ((List.range k).map N.testBit).reverse.map Sym.bit := by
    simp [List.range_succ]
  have hdiv : N / 2 ^ (k + 1) = N / 2 ^ k / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  by_cases h0 : N / 2 ^ k = 0
  · have hX0 : S' X = rx := by rw [hSX, h0, natSyms_zero', List.nil_append]
    have hb : N.testBit k = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, h0]; rfl
    refine (HT.emitStep_end lS X F S' (by rw [hX0]; exact hrx) ρ).of_eq ?_ (by norm_num)
    have h1 : N / 2 ^ (k + 1) = 0 := by rw [hdiv, h0]
    rw [hSF, hS', emitSt, hk, upd2_collapse B wc X F (Ne.symm hXw) (Ne.symm hFw) hXF, emitSt, hk1,
      hrange, hb, h0, h1]
    rfl
  · have hbit := natSyms_pos h0
    have hX1 : S' X = Sym.bit (decide (N / 2 ^ k % 2 = 1)) :: (natSyms (N / 2 ^ k / 2) ++ rx) := by
      rw [hSX, hbit]; rfl
    refine (HT.emitStep_bit lS X F hXF S' _ _ hX1 ρ).of_eq ?_ le_rfl
    have hb : N.testBit k = decide (N / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    rw [hSF, hS', emitSt, hk, upd3_collapse B wc X F (Ne.symm hXw) (Ne.symm hFw) hXF, emitSt, hk1,
      hrange, hb, hdiv]
    rfl

/-- Cost of `emitBits` with counter constants `Cc` (copy), `Cz` (zero test), `Cd` (decrement). -/
def emitCost (Cc Cz Cd w : ℕ) : ℕ :=
  Cc * (bitLen w + 1) + (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + 4 + Cz) w)

/-- **`emitBits`**: from `natSyms N ++ rx` on `X` (`N < 2^w`), `F` receives the reversed field
`(bitsLE w N).reverse` and `X` keeps `rx`; every other stack (including the counter `wc`) is
unchanged. -/
theorem HT.emitBits {Icp : Inst 2 4 Unit} {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit}
    {Cc Cz Cd : ℕ} (hcp : SpecCopy Icp Cc) (hz : SpecIsZero Iz Cz) (hd : SpecDec Id Cd)
    (lS : Lens σ (Option Sym)) (lcp : Lens σ Icp.R) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (vw wc X F dflt : Loc a b) (hnd : [vw, wc, X, F].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (w N : ℕ) (rw rx : List Sym) (hrw : TermOK rw) (hrx : TermOK rx)
    (hwc : TermOK (B wc)) (hvw : B vw = natSyms w ++ rw) (hX : B X = natSyms N ++ rx)
    (hN : N < 2 ^ w) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (emitBits Icp Iz Id lS lcp lz ld vw wc X F dflt)
      (Function.update (Function.update B X rx) F ((bitsLE w N).reverse.map Sym.bit ++ B F))
      (emitCost Cc Cz Cd w) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hvwc, hvX, hvF⟩, ⟨hwX, hwF⟩, hXF, -⟩ := hnd
  have hcopy := HT.copyNat hcp dflt lcp vw wc (by simp [hvwc]) (by omega) B w rw hrw hvw ρ
  have hSt : ∀ i, emitSt B wc X F rx w N i wc = natSyms i ++ B wc := by
    intro i
    rw [emitSt, Function.update_of_ne hwF, Function.update_of_ne hwX, Function.update_self]
  have hloop := HT.cdLoop' hz hd lz ld wc dflt (by omega) (B wc) hwc (emitSt B wc X F rx w N) hSt
    (emitStep lS X F) (fun _ => 4) ρ w
    (fun i hi => emitSt_step B wc X F hXF (Ne.symm hwX) (Ne.symm hwF) rx hrx w N i hi lS ρ)
  have hstart : Function.update B wc (natSyms w ++ B wc) = emitSt B wc X F rx w N w := by
    funext g
    rw [emitSt, Nat.sub_self, pow_zero, Nat.div_one, List.range_zero, List.map_nil,
      List.reverse_nil, List.map_nil, List.nil_append]
    by_cases hgF : g = F
    · subst hgF
      rw [Function.update_self, Function.update_of_ne (Ne.symm hwF)]
    · rw [Function.update_of_ne hgF]
      by_cases hgX : g = X
      · subst hgX
        rw [Function.update_self, Function.update_of_ne (Ne.symm hwX), hX]
      · rw [Function.update_of_ne hgX]
  have hend : emitSt B wc X F rx w N 0 =
      Function.update (Function.update B X rx) F ((bitsLE w N).reverse.map Sym.bit ++ B F) := by
    have h0 : N / 2 ^ w = 0 := Nat.div_eq_of_lt hN
    funext g
    rw [emitSt, Nat.sub_zero, h0, natSyms_zero', List.nil_append, List.nil_append]
    by_cases hgF : g = F
    · subst hgF
      rw [Function.update_self, Function.update_self]
      rfl
    · rw [Function.update_of_ne hgF, Function.update_of_ne hgF]
      by_cases hgX : g = X
      · subst hgX
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hgX, Function.update_of_ne hgX]
        by_cases hgw : g = wc
        · subst hgw; rw [Function.update_self]
        · rw [Function.update_of_ne hgw]
  rw [hstart] at hcopy
  rw [hend] at hloop
  exact HT.seq hcopy hloop

/-! ## 6. `moveF`: move a bit block (reversed) -/

/-- `TMFw.Lib.moveBlock src dst` on host registers (through the symbol lens `lS`). -/
def moveF (lS : Lens σ (Option Sym)) (src dst : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  (TMFw.Lib.moveBlock src dst).liftRegs lS

theorem moveF_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) : (moveF lS src dst).Closed :=
  freeBelow_liftRegs lS _ 0 (by simp [TMFw.Lib.moveBlock, TMFw.Lib.moveBits, TMFw.Lib.moveBitsBody,
    TMFw.Lib.restoreR, TMFw.Lib.popR, TMFw.Lib.pushR, TMFw.Lib.skip, Prog.FreeBelow])

/-- **`moveF`**: the bit block on top of `src` is moved, reversed, onto `dst`; its terminator
stays on `src`. -/
theorem HT.moveF (lS : Lens σ (Option Sym)) (src dst : Loc a b) (hne : src ≠ dst)
    (B : Loc a b → List Sym) (es : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hB : B src = es.map Sym.bit ++ rest) :
    HT [] B (moveF lS src dst)
      (Function.update (Function.update B src rest) dst (es.reverse.map Sym.bit ++ B dst))
      (3 * es.length + 4) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e := TMFw.Lib.moveBlock_eval hne [] (lS.get v) es rest S hrest hB
  have e' := Eval.liftRegs lS e v rfl
  exact ⟨_, _, e', rfl, le_rfl⟩

end SubNLogN.Machine.FFT.Phase
