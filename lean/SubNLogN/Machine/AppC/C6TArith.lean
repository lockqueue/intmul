/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6QLeaves
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.Calculus.Loops

/-!
# Lemma A.8 join/unjoin: the threshold `t = c6T q e` on a counter stack (`Machine/AppC/C6TArith.lean`)

Machine computation of `c6K e = ⌈log_m e⌉` and `c6T q e = ⌈log_{q²} W_b^k⌉` (`C6QLeaves.lean`)
on mark-floored `natSyms` counters, with the `NatArith` library (`C5StreamArith.lean`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

* `clogP b X D …` (generic stack type, registers `NatArith.Reg`): pushes `natSyms (Nat.clog b x)`
  above a `mark` on `D` (`x` read from `X`, restored; seven temporaries, restored). It is a while
  loop (`RunsIn.seq_while_det`): `Z := 1`; while `Z < x`: `Z := Z·b`, `D := D + 1` (`Lib.inc`).
  Proved: `runs_clogP`, cost `clogCost b x`.
* `tKerP q` on `KLoc (Fin 2) TS`: stack `0` holds `e` (restored), `natSyms (c6T q e)` is pushed on
  stack `1`. Proved: `runs_tKerP`; the cost `tCost q e ≤ tC q · (e + 1)^3` (`tCost_le`).
* `C6TPushSpec q` (an internal kernel specification of this file) and its proof
  `c6TPush_holds (hq : 2 ≤ q)`: the kernel in `KContract` form, constant `tC q`.

All helpers are in `SubNLogN.Machine.AppC.C6JoinAux`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

namespace AppC.C6JoinAux

open NatArith

/-! ## Comparison and increment as `Runs` facts -/

section Generic

variable {K : Type} [DecidableEq K]

/-- The loop flag of `clogP`: the last comparison returned `lt`. -/
def cltR (r : NatArith.Reg) : Bool := decide ((NatArith.lC.get r).2.2 = Ordering.lt)

theorem ordOf_lt_iff (a b : ℕ) : ordOf a b = Ordering.lt ↔ a < b := by
  unfold ordOf
  split_ifs with h1 h2 <;> simp_all

omit [DecidableEq K] in
theorem closed_cmpN (x y t1 t2 : K) : (cmpN x y t1 t2).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)

/-- `cmpN` as a `Runs` fact: stacks unchanged, `cltR = decide (a < b)`. -/
theorem runs_cmpN {x y t1 t2 : K} (h : [x, y, t1, t2].Nodup) (a b : ℕ) (rx ry : List Sym)
    (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs (cmpN x y t1 t2) S S (fun r => cltR r = decide (a < b)) (12 * bitLen b + 15) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hx1, hx2⟩, ⟨hy1, hy2⟩, h12⟩ := h
  have hc : Runs (cmpNum x y t1 t2) S S (fun r : CReg => r.2.2 = ordOf a b)
      (12 * bitLen b + 15) := by
    intro s hs
    obtain ⟨v, stk⟩ := s
    change stk = S at hs
    subst hs
    obtain ⟨s', t, e, ⟨h1, h2⟩, ht⟩ :=
      cmpNum_triple hxy hx1 hx2 hy1 hy2 h12 v a b rx ry stk hrx hry hx hy ⟨v, stk⟩ rfl
    refine ⟨s', t, e, ⟨h1, h2⟩, ?_⟩
    have hm : min (encodeNat a).length (encodeNat b).length ≤ bitLen b := min_le_right _ _
    omega
  have hc' : Runs (cmpN x y t1 t2) S S (fun v => (NatArith.lC.get v).2.2 = ordOf a b)
      (12 * bitLen b + 15) := RunsIn.liftRegs NatArith.lC (RunsIn.iff_runs.2 hc)
  refine WP.W9comp.runs_mono hc' (fun r hr => ?_) le_rfl
  show decide ((NatArith.lC.get r).2.2 = Ordering.lt) = decide (a < b)
  rw [hr]
  exact decide_eq_decide.2 (ordOf_lt_iff a b)

/-- `Lib.inc` through the work register: the counter `i` on `D` becomes `i + 1`. -/
theorem runs_incW {D T : K} (hDT : D ≠ T) (i : ℕ) (rest : List Sym) (hrest : TermOK rest)
    (S : K → List Sym) (hS : S D = natSyms i ++ rest) :
    Runs ((Lib.inc D T).liftRegs NatArith.lW) S (Function.update S D (natSyms (i + 1) ++ rest))
      (fun _ => True) (6 * bitLen i + 9) := by
  have h := RunsIn.runs_inc hDT (encodeNat i) rest hrest S hS
  rw [← encodeNat_succ] at h
  have h' : Runs ((Lib.inc D T).liftRegs NatArith.lW) S
      (Function.update S D ((encodeNat (i + 1)).map Sym.bit ++ rest)) (fun _ => True)
      (6 * ones (encodeNat i) + 9) := RunsIn.liftRegs NatArith.lW (RunsIn.iff_runs.2 h)
  refine WP.W9comp.runs_mono h' (fun _ _ => trivial) ?_
  have := ones_le_length (encodeNat i)
  show 6 * ones (encodeNat i) + 9 ≤ 6 * (encodeNat i).length + 9
  omega

/-! ## `clogP`: `⌈log_b x⌉` by repeated multiplication -/

/-- Setup of `clogP`: a `mark` floor on `D` (the counter `0`) and on `Z`, `Z := 1`, compare. -/
def clogSetup (X D Z Q Td : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark D) (.seq (pushMark Z) (.seq (pushNat Z 1) (cmpN Z X Q Td)))

/-- Body of `clogP`: `Z := Z·b`, `D := D + 1`, compare `Z` with `X`. -/
def clogBody (b : ℕ) (X D Z Q Td A Bs Acc Tm : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (mulConstN Z b Q Td A Bs Acc Tm)
    (.seq ((Lib.inc D Tm).liftRegs NatArith.lW) (cmpN Z X Q Td))

/-- **`⌈log_b x⌉` on a counter stack.** Pushes `natSyms (Nat.clog b x)` above a `mark` on `D`
(`x` read from `X`, restored); `Z, Q, Td, A, Bs, Acc, Tm` are temporaries (restored). -/
def clogP (b : ℕ) (X D Z Q Td A Bs Acc Tm : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (.seq (clogSetup X D Z Q Td) (.loop cltR (clogBody b X D Z Q Td A Bs Acc Tm))) (dropF Z)

omit [DecidableEq K] in
theorem closed_clogP (b : ℕ) (X D Z Q Td A Bs Acc Tm : K) :
    (clogP b X D Z Q Td A Bs Acc Tm).Closed :=
  ⟨⟨⟨closed_pushMark D, closed_pushMark Z, closed_pushNat Z 1, closed_cmpN Z X Q Td⟩,
    ⟨closed_mulConstN Z b Q Td A Bs Acc Tm, WP.W9comp.closed_liftRegs _ (Loops.closed_inc D Tm),
      closed_cmpN Z X Q Td⟩⟩, closed_dropF Z⟩

/-- The loop states of `clogP`: the counter `i` on `D`, `b^i` on `Z` (both above a `mark`). -/
def clogSt (S : K → List Sym) (D Z : K) (b i : ℕ) : K → List Sym :=
  Function.update (Function.update S D (natSyms i ++ Sym.mark :: S D)) Z
    (natSyms (b ^ i) ++ Sym.mark :: S Z)

theorem clogSt_Z (S : K → List Sym) (D Z : K) (b i : ℕ) :
    clogSt S D Z b i Z = natSyms (b ^ i) ++ Sym.mark :: S Z := by
  simp [clogSt]

theorem clogSt_D {D Z : K} (h : D ≠ Z) (S : K → List Sym) (b i : ℕ) :
    clogSt S D Z b i D = natSyms i ++ Sym.mark :: S D := by
  simp [clogSt, h]

theorem clogSt_of_ne {D Z k : K} (hD : k ≠ D) (hZ : k ≠ Z) (S : K → List Sym) (b i : ℕ) :
    clogSt S D Z b i k = S k := by
  simp [clogSt, hD, hZ]

theorem bitLen_one : bitLen 1 = 1 := by
  rw [bitLen, IntMulTM.length_encodeNat, Nat.size_one]

theorem runs_clogSetup {X D Z Q Td : K} (hXD : X ≠ D) (hXZ : X ≠ Z) (hDZ : D ≠ Z)
    (hcmp : [Z, X, Q, Td].Nodup) (b x : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hX : S X = natSyms x ++ rx) :
    Runs (clogSetup X D Z Q Td) S (clogSt S D Z b 0) (fun r => cltR r = decide (1 < x))
      (12 * bitLen x + 19) := by
  have r1 := runs_pushMark D S
  have r2 := runs_pushMark Z (Function.update S D (Sym.mark :: S D))
  rw [Function.update_of_ne hDZ.symm] at r2
  have r3 := runs_pushNat Z 1 (Function.update (Function.update S D (Sym.mark :: S D)) Z
    (Sym.mark :: S Z))
  rw [Function.update_self, Function.update_idem] at r3
  have e3 : Function.update (Function.update S D (Sym.mark :: S D)) Z
      (natSyms 1 ++ Sym.mark :: S Z) = clogSt S D Z b 0 := by
    simp only [clogSt, pow_zero, natSyms_zero, List.nil_append]
  rw [e3] at r3
  have r4 := runs_cmpN hcmp 1 x (Sym.mark :: S Z) rx (clogSt S D Z b 0) (termOK_mark _) hrx
    (by rw [clogSt_Z, pow_zero]) (by rw [clogSt_of_ne hXD hXZ]; exact hX)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 r4))) (fun _ h => h) ?_
  have := bitLen_one
  omega

theorem runs_clogBody {X D Z Q Td A Bs Acc Tm : K} (hmc : [Z, Q, Td, A, Bs, Acc, Tm].Nodup)
    (hcmp : [Z, X, Q, Td].Nodup) (hXD : X ≠ D) (hXZ : X ≠ Z) (hDZ : D ≠ Z) (hDM : D ≠ Tm)
    (b x i : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hX : S X = natSyms x ++ rx) :
    Runs (clogBody b X D Z Q Td A Bs Acc Tm) (clogSt S D Z b i) (clogSt S D Z b (i + 1))
      (fun r => cltR r = decide (b ^ (i + 1) < x))
      (mulConstCost (b ^ i) b + ((6 * bitLen i + 9) + (12 * bitLen x + 15))) := by
  have r1 := runs_mulConstN hmc b (b ^ i) (Sym.mark :: S Z) (clogSt S D Z b i) (termOK_mark _)
    (clogSt_Z S D Z b i)
  have r2 := runs_incW hDM i (Sym.mark :: S D) (termOK_mark _)
    (Function.update (clogSt S D Z b i) Z (natSyms (b ^ i * b) ++ Sym.mark :: S Z))
    (by rw [Function.update_of_ne hDZ, clogSt_D hDZ])
  have e2 : Function.update (Function.update (clogSt S D Z b i) Z
      (natSyms (b ^ i * b) ++ Sym.mark :: S Z)) D (natSyms (i + 1) ++ Sym.mark :: S D) =
      clogSt S D Z b (i + 1) := by
    rw [← pow_succ]
    funext k
    by_cases hkZ : k = Z
    · subst hkZ
      simp [clogSt, Ne.symm hDZ]
    · by_cases hkD : k = D
      · subst hkD
        simp [clogSt, hkZ]
      · simp [clogSt, hkZ, hkD]
  have r3 := runs_cmpN hcmp (b ^ (i + 1)) x (Sym.mark :: S Z) rx (clogSt S D Z b (i + 1))
    (termOK_mark _) hrx (clogSt_Z S D Z b (i + 1)) (by rw [clogSt_of_ne hXD hXZ]; exact hX)
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr r2 e2) r3)

/-- Per-iteration cost bound of `clogP`. -/
def clogB (b x : ℕ) : ℕ := 200 * (bitLen x + bitLen b + 2) ^ 2

/-- Cost bound of `clogP`. -/
def clogCost (b x : ℕ) : ℕ := (Nat.clog b x + 1) * (clogB b x + 1) + 40

theorem bitLen_pow_clog_le {b : ℕ} (hb : 2 ≤ b) (x : ℕ) :
    bitLen (b ^ Nat.clog b x) ≤ bitLen x + bitLen b + 2 := by
  have h1 : b ^ Nat.clog b x ≤ (x + 1) * b := by
    rcases Nat.eq_zero_or_pos (Nat.clog b x) with h0 | hpos
    · rw [h0, pow_zero]
      nlinarith
    · have hlt : b ^ (Nat.clog b x - 1) < x := Nat.pow_lt_of_lt_clog (by omega)
      have he : b ^ Nat.clog b x = b ^ (Nat.clog b x - 1) * b := by
        rw [← pow_succ]
        congr 1
        omega
      rw [he]
      exact Nat.mul_le_mul_right _ (by omega)
  calc bitLen (b ^ Nat.clog b x) ≤ bitLen ((x + 1) * b) := bitLen_mono'' h1
    _ ≤ bitLen (x + 1) + bitLen b := bitLen_mul_le' _ _
    _ ≤ bitLen x + bitLen b + 2 := by
        have := bitLen_add_le' x 1
        rw [bitLen_one] at this
        omega

/-- **`clogP` pushes `⌈log_b x⌉`** above a `mark` on `D`; every other stack is unchanged. -/
theorem runs_clogP {X D Z Q Td A Bs Acc Tm : K} (hnd : [X, D, Z, Q, Td, A, Bs, Acc, Tm].Nodup)
    {b : ℕ} (hb : 2 ≤ b) (x : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hX : S X = natSyms x ++ rx) :
    Runs (clogP b X D Z Q Td A Bs Acc Tm) S
      (Function.update S D (natSyms (Nat.clog b x) ++ Sym.mark :: S D)) (fun _ => True)
      (clogCost b x) := by
  have hmc : [Z, Q, Td, A, Bs, Acc, Tm].Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).2
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hXD, hXZ, hXQ, hXT, -, -, -, -⟩, ⟨hDZ, -, -, -, -, -, hDM⟩, ⟨hZQ, hZT, -, -, -, -⟩,
    ⟨hQT, -, -, -, -⟩, -, -, -, -⟩ := hnd'
  have hcmp : [Z, X, Q, Td].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm hXZ, hZQ, hZT⟩, ⟨hXQ, hXT⟩, hQT⟩
  have hb1 : 1 < b := by omega
  set cl := Nat.clog b x with hcl
  have hcont : ∀ i, decide (b ^ i < x) = decide (i < cl) := fun i =>
    decide_eq_decide.2 (Nat.lt_clog_iff_pow_lt hb1).symm
  have hclx : cl ≤ x := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb1).le
  set B := clogB b x with hB
  have h0 : RunsIn [] (clogSetup X D Z Q Td) S (clogSt S D Z b 0)
      (fun r => cltR r = decide (0 < cl)) (12 * bitLen x + 19) := by
    have h := runs_clogSetup hXD hXZ hDZ hcmp b x rx S hrx hX
    refine RunsIn.iff_runs.2 (WP.W9comp.runs_mono h (fun r hr => ?_) le_rfl)
    rw [hr, ← hcont 0, pow_zero]
  have hbody : ∀ i, i < cl → RunsIn [] (clogBody b X D Z Q Td A Bs Acc Tm) (clogSt S D Z b i)
      (clogSt S D Z b (i + 1)) (fun r => cltR r = decide (i + 1 < cl)) B := by
    intro i hi
    have h := runs_clogBody hmc hcmp hXD hXZ hDZ hDM b x i rx S hrx hX
    refine RunsIn.iff_runs.2 (WP.W9comp.runs_mono h (fun r hr => by rw [hr, hcont]) ?_)
    have hbi : b ^ i < x := Nat.pow_lt_of_lt_clog hi
    have hL1 : bitLen (b ^ i) ≤ bitLen x := bitLen_mono'' hbi.le
    have hL2 : bitLen (b ^ i * b) ≤ bitLen x + bitLen b :=
      (bitLen_mul_le' _ _).trans (by omega)
    have hL3 : bitLen i ≤ bitLen x := bitLen_mono'' (by omega)
    have hmcc := mulConstCost_le (c := b) hL1
    have hS2 : 2 ≤ bitLen x + bitLen b + 2 := by omega
    have hSq : 2 * (bitLen x + bitLen b + 2) ≤ (bitLen x + bitLen b + 2) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right _ hS2
    show mulConstCost (b ^ i) b + ((6 * bitLen i + 9) + (12 * bitLen x + 15)) ≤
      200 * (bitLen x + bitLen b + 2) ^ 2
    nlinarith
  have hloop : RunsIn [] (.seq (clogSetup X D Z Q Td)
      (.loop cltR (clogBody b X D Z Q Td A Bs Acc Tm)))
      S (clogSt S D Z b cl) (fun r => cltR r = false)
      (12 * bitLen x + 19 + ((cl - 0) * (B + 1) + 1)) := by
    refine RunsIn.congr (RunsIn.seq_while_det (st := clogSt S D Z b)
      (cont := fun i => decide (i < cl)) (fun i => i + 1) (fun i => max i cl) (fun i => cl - i)
      (fun i => (cl - i) * (B + 1) + 1) (x₀ := 0) h0 ?_ ?_ ?_ ?_) ?_ le_rfl
    · intro i hi
      have : ¬ i < cl := by simpa using hi
      exact max_eq_left (by omega)
    · intro i hi
      have : i < cl := by simpa using hi
      show max (i + 1) cl = max i cl
      rw [max_eq_right (by omega), max_eq_right (by omega)]
    · intro i _
      show 1 ≤ (cl - i) * (B + 1) + 1
      omega
    · intro i hi
      have hi' : i < cl := by simpa using hi
      refine ⟨B, by show cl - (i + 1) < cl - i; omega, ?_, hbody i hi'⟩
      show B + 1 + ((cl - (i + 1)) * (B + 1) + 1) ≤ (cl - i) * (B + 1) + 1
      have e : (cl - i) * (B + 1) = (cl - (i + 1)) * (B + 1) + (B + 1) := by
        rw [show cl - i = (cl - (i + 1)) + 1 by omega, Nat.succ_mul]
      omega
    · show clogSt S D Z b (max 0 cl) = clogSt S D Z b cl
      rw [max_eq_right (Nat.zero_le _)]
  have r5 := runs_dropF Z (b ^ cl) Sym.mark (S Z) (clogSt S D Z b cl) rfl (clogSt_Z S D Z b cl)
  have e5 : Function.update (clogSt S D Z b cl) Z (S Z) =
      Function.update S D (natSyms cl ++ Sym.mark :: S D) := by
    funext k
    by_cases hkZ : k = Z
    · subst hkZ
      simp [clogSt, Ne.symm hDZ]
    · simp [clogSt, hkZ]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr
    (WP.W9comp.runs_seq (RunsIn.iff_runs.1 hloop) r5) e5)
    (fun _ _ => trivial) ?_
  have hbl := bitLen_pow_clog_le hb x
  rw [← hcl] at hbl
  have hS1 : 1 ≤ bitLen x + bitLen b + 2 := by omega
  have hSq : (bitLen x + bitLen b + 2) ≤ (bitLen x + bitLen b + 2) ^ 2 := by
    rw [sq]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hBge : 14 * bitLen x + 2 * bitLen b + 4 ≤ B := by
    rw [hB, clogB]
    nlinarith
  show 12 * bitLen x + 19 + ((cl - 0) * (B + 1) + 1) + (2 * bitLen (b ^ cl) + 2) ≤
    (cl + 1) * (B + 1) + 40
  have e : (cl + 1) * (B + 1) = cl * (B + 1) + (B + 1) := Nat.succ_mul _ _
  rw [Nat.sub_zero]
  omega

end Generic

/-! ## Cost helpers -/

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt' Nat.lt_two_pow_self

theorem bitLen_pow_le' (a : ℕ) : ∀ n, bitLen (a ^ n) ≤ n * bitLen a + 1
  | 0 => by simp [bitLen_one]
  | n + 1 => by
    have ih := bitLen_pow_le' a n
    have h := bitLen_mul_le' (a ^ n) a
    rw [pow_succ]
    nlinarith

theorem cube_le {x y E α β : ℕ} (hE : 1 ≤ E) (hx : x ≤ α * E) (hy : y ≤ β * E) :
    x * (200 * y ^ 2 + 1) ≤ α * (200 * β ^ 2 + 1) * E ^ 3 := by
  have h1 : y ^ 2 ≤ β ^ 2 * E ^ 2 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hy 2
  have h2 : 1 ≤ E ^ 2 := Nat.one_le_pow _ _ hE
  have h3 : 200 * y ^ 2 + 1 ≤ (200 * β ^ 2 + 1) * E ^ 2 := by nlinarith
  calc x * (200 * y ^ 2 + 1) ≤ (α * E) * ((200 * β ^ 2 + 1) * E ^ 2) := Nat.mul_le_mul hx h3
    _ = α * (200 * β ^ 2 + 1) * E ^ 3 := by ring

theorem clogCost_le {b x E α β : ℕ} (hE : 1 ≤ E) (hc : Nat.clog b x + 1 ≤ α * E)
    (hy : bitLen x + bitLen b + 2 ≤ β * E) :
    clogCost b x ≤ (α * (200 * β ^ 2 + 1) + 40) * E ^ 3 := by
  have h := cube_le hE hc hy
  have h3 : 1 ≤ E ^ 3 := Nat.one_le_pow _ _ hE
  unfold clogCost clogB
  nlinarith

theorem powCost_le {c a n E α β : ℕ} (hE : 1 ≤ E) (hn : n + 1 ≤ α * E)
    (hy : bitLen (a * c ^ n) + bitLen c + 2 ≤ β * E) :
    powCost c a n ≤ α * (200 * β ^ 2 + 1) * E ^ 3 := by
  have h := cube_le hE hn hy
  unfold powCost
  nlinarith

/-! ## The threshold kernels -/

/-- Private stacks of the threshold kernels. -/
inductive TS where
  | kS | Y | D | Z | Kc2 | Q | Td | A | Bs | Acc | Tm
  deriving DecidableEq

instance : Fintype TS where
  elems := {.kS, .Y, .D, .Z, .Kc2, .Q, .Td, .A, .Bs, .Acc, .Tm}
  complete := fun x => by cases x <;> simp

/-- Layout of the threshold kernels: stack `0` holds `e`, stack `1` receives the result. -/
abbrev KT : Type := KLoc (Fin 2) TS

/-- `k := ⌈log_m e⌉` on `kS`, then `Y := W_b^k` (both above a `mark`). -/
def kwP : Prog KT (fun _ => Sym) NatArith.Reg :=
  .seq (clogP (tripleM 100) (.inl 0) (.inr .kS) (.inr .Z) (.inr .Q) (.inr .Td) (.inr .A)
      (.inr .Bs) (.inr .Acc) (.inr .Tm))
    (.seq (pushMark (.inr .Y)) (.seq (pushNat (.inr .Y) 1)
      (powMulN (.inr .Y) (tripleWb 100) (.inr .kS) (.inr .Kc2) (.inr .Tm) (.inr .Q) (.inr .Td)
        (.inr .A) (.inr .Bs) (.inr .Acc))))

theorem closed_kwP : kwP.Closed :=
  ⟨closed_clogP _ _ _ _ _ _ _ _ _ _, closed_pushMark _, closed_pushNat _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

/-- The stacks after `kwP`. -/
def kwSt (S : KT → List Sym) (e : ℕ) : KT → List Sym :=
  Function.update (Function.update S (.inr .kS) (natSyms (c6K e) ++ Sym.mark :: S (.inr .kS)))
    (.inr .Y) (natSyms (tripleWb 100 ^ c6K e) ++ Sym.mark :: S (.inr .Y))

theorem runs_kwP (e : ℕ) (r0 : List Sym) (S : KT → List Sym) (hr0 : TermOK r0)
    (hS : S (.inl 0) = natSyms e ++ r0) :
    Runs kwP S (kwSt S e) (fun _ => True)
      (clogCost (tripleM 100) e + (1 + ((bitLen 1 + 1) + powCost (tripleWb 100) 1 (c6K e)))) := by
  have hm : 2 ≤ tripleM 100 := by decide
  have hW : 1 ≤ tripleWb 100 := by decide
  set S1 : KT → List Sym :=
    Function.update S (.inr .kS) (natSyms (c6K e) ++ Sym.mark :: S (.inr .kS)) with hS1
  have h1 : Runs (clogP (tripleM 100) (.inl 0) (.inr .kS) (.inr .Z) (.inr .Q) (.inr .Td)
      (.inr .A) (.inr .Bs) (.inr .Acc) (.inr .Tm)) S S1 (fun _ => True)
      (clogCost (tripleM 100) e) :=
    runs_clogP (by decide) hm e r0 S hr0 hS
  have hY : S1 (.inr .Y) = S (.inr .Y) := by simp [hS1]
  have h2 := runs_pushMark (.inr .Y : KT) S1
  rw [hY] at h2
  have h3 := runs_pushNat (.inr .Y : KT) 1
    (Function.update S1 (.inr .Y) (Sym.mark :: S (.inr .Y)))
  rw [Function.update_self, Function.update_idem] at h3
  have h4 := runs_powMulN (K := KT) (k := .inr .Y) (ns := .inr .kS) (Kc := .inr .Kc2)
    (t := .inr .Tm) (Q := .inr .Q) (Tdst := .inr .Td) (A := .inr .A) (Bs := .inr .Bs)
    (Acc := .inr .Acc) (by decide) (tripleWb 100) hW 1 (c6K e) (Sym.mark :: S (.inr .Y))
    (Sym.mark :: S (.inr .kS))
    (Function.update S1 (.inr .Y) (natSyms 1 ++ Sym.mark :: S (.inr .Y))) (termOK_mark _)
    (termOK_mark _) (by simp) (by simp [hS1])
  rw [Function.update_idem, one_mul] at h4
  exact WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3 h4))

/-- **The threshold kernel.** `kwP`; `D := ⌈log_{q²} Y⌉ = c6T q e`; copy it onto stack `1`; drop
the scratch counters `D, Y, kS` with their floors. -/
def tKerP (q : ℕ) : Prog KT (fun _ => Sym) NatArith.Reg :=
  .seq kwP (.seq (clogP (q ^ 2) (.inr .Y) (.inr .D) (.inr .Z) (.inr .Q) (.inr .Td) (.inr .A)
      (.inr .Bs) (.inr .Acc) (.inr .Tm))
    (.seq (copyN (.inr .D) (.inl 1) (.inr .Q))
      (.seq (dropF (.inr .D)) (.seq (dropF (.inr .Y)) (dropF (.inr .kS))))))

/-- **The `W_b^k` kernel.** `kwP`; copy `Y` onto stack `1`; drop `Y, kS` with their floors. -/
def wKerP : Prog KT (fun _ => Sym) NatArith.Reg :=
  .seq kwP (.seq (copyN (.inr .Y) (.inl 1) (.inr .Q)) (.seq (dropF (.inr .Y)) (dropF (.inr .kS))))

theorem closed_tKerP (q : ℕ) : (tKerP q).Closed :=
  ⟨closed_kwP, closed_clogP _ _ _ _ _ _ _ _ _ _, closed_copyN _ _ _, closed_dropF _,
    closed_dropF _, closed_dropF _⟩

theorem closed_wKerP : wKerP.Closed :=
  ⟨closed_kwP, closed_copyN _ _ _, closed_dropF _, closed_dropF _⟩

/-- Cost of the threshold kernel. -/
def tCost (q e : ℕ) : ℕ :=
  clogCost (tripleM 100) e + powCost (tripleWb 100) 1 (c6K e) +
    clogCost (q ^ 2) (tripleWb 100 ^ c6K e) + 9 * bitLen (c6T q e) +
    2 * bitLen (tripleWb 100 ^ c6K e) + 2 * bitLen (c6K e) + 20

/-- Cost of the `W_b^k` kernel. -/
def wCost (e : ℕ) : ℕ :=
  clogCost (tripleM 100) e + powCost (tripleWb 100) 1 (c6K e) +
    9 * bitLen (tripleWb 100 ^ c6K e) + 2 * bitLen (c6K e) + 20

theorem runs_tKerP {q : ℕ} (hq : 2 ≤ q) (e : ℕ) (r0 : List Sym) (S : KT → List Sym)
    (hr0 : TermOK r0) (hS : S (.inl 0) = natSyms e ++ r0) :
    Runs (tKerP q) S (Function.update S (.inl 1) (natSyms (c6T q e) ++ S (.inl 1)))
      (fun _ => True) (tCost q e) := by
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have h1 := runs_kwP e r0 S hr0 hS
  have h5 := runs_clogP (K := KT) (X := .inr .Y) (D := .inr .D) (Z := .inr .Z) (Q := .inr .Q)
    (Td := .inr .Td) (A := .inr .A) (Bs := .inr .Bs) (Acc := .inr .Acc) (Tm := .inr .Tm)
    (by decide) hq2 (tripleWb 100 ^ c6K e) (Sym.mark :: S (.inr .Y)) (kwSt S e) (termOK_mark _)
    (by simp [kwSt])
  have hD : kwSt S e (.inr .D) = S (.inr .D) := by simp [kwSt]
  rw [hD] at h5
  set S5 : KT → List Sym :=
    Function.update (kwSt S e) (.inr .D) (natSyms (c6T q e) ++ Sym.mark :: S (.inr .D)) with hS5
  have h5' : Runs (clogP (q ^ 2) (.inr .Y) (.inr .D) (.inr .Z) (.inr .Q) (.inr .Td) (.inr .A)
      (.inr .Bs) (.inr .Acc) (.inr .Tm)) (kwSt S e) S5 (fun _ => True)
      (clogCost (q ^ 2) (tripleWb 100 ^ c6K e)) := h5
  have h6 := runs_copyN (K := KT) (src := .inr .D) (dst := .inl 1) (tmp := .inr .Q) (by decide)
    (by decide) (by decide) (c6T q e) (Sym.mark :: S (.inr .D)) S5 (termOK_mark _)
    (by simp [hS5])
  have h61 : S5 (.inl 1) = S (.inl 1) := by simp [hS5, kwSt]
  rw [h61] at h6
  set S6 : KT → List Sym := Function.update S5 (.inl 1) (natSyms (c6T q e) ++ S (.inl 1))
    with hS6
  have h7 := runs_dropF (K := KT) (.inr .D) (c6T q e) Sym.mark (S (.inr .D)) S6 rfl
    (by simp [hS6, hS5])
  have h8 := runs_dropF (K := KT) (.inr .Y) (tripleWb 100 ^ c6K e) Sym.mark (S (.inr .Y))
    (Function.update S6 (.inr .D) (S (.inr .D))) rfl (by simp [hS6, hS5, kwSt])
  have h9 := runs_dropF (K := KT) (.inr .kS) (c6K e) Sym.mark (S (.inr .kS))
    (Function.update (Function.update S6 (.inr .D) (S (.inr .D))) (.inr .Y) (S (.inr .Y))) rfl
    (by simp [hS6, hS5, kwSt])
  have hfin : Function.update (Function.update (Function.update S6 (.inr .D) (S (.inr .D)))
      (.inr .Y) (S (.inr .Y))) (.inr .kS) (S (.inr .kS)) =
      Function.update S (.inl 1) (natSyms (c6T q e) ++ S (.inl 1)) := by
    funext k
    rcases k with i | x
    · fin_cases i <;> simp [hS6, hS5, kwSt]
    · cases x <;> simp [hS6, hS5, kwSt]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1
    (WP.W9comp.runs_seq h5' (WP.W9comp.runs_seq h6 (WP.W9comp.runs_seq h7
      (WP.W9comp.runs_seq h8 h9))))) hfin) (fun _ _ => trivial) ?_
  have := bitLen_one
  unfold tCost
  omega

theorem runs_wKerP (e : ℕ) (r0 : List Sym) (S : KT → List Sym) (hr0 : TermOK r0)
    (hS : S (.inl 0) = natSyms e ++ r0) :
    Runs wKerP S (Function.update S (.inl 1) (natSyms (tripleWb 100 ^ c6K e) ++ S (.inl 1)))
      (fun _ => True) (wCost e) := by
  have h1 := runs_kwP e r0 S hr0 hS
  have h2 := runs_copyN (K := KT) (src := .inr .Y) (dst := .inl 1) (tmp := .inr .Q) (by decide)
    (by decide) (by decide) (tripleWb 100 ^ c6K e) (Sym.mark :: S (.inr .Y)) (kwSt S e)
    (termOK_mark _) (by simp [kwSt])
  have h21 : kwSt S e (.inl 1) = S (.inl 1) := by simp [kwSt]
  rw [h21] at h2
  set S2 : KT → List Sym :=
    Function.update (kwSt S e) (.inl 1) (natSyms (tripleWb 100 ^ c6K e) ++ S (.inl 1)) with hS2
  have h3 := runs_dropF (K := KT) (.inr .Y) (tripleWb 100 ^ c6K e) Sym.mark (S (.inr .Y)) S2 rfl
    (by simp [hS2, kwSt])
  have h4 := runs_dropF (K := KT) (.inr .kS) (c6K e) Sym.mark (S (.inr .kS))
    (Function.update S2 (.inr .Y) (S (.inr .Y))) rfl (by simp [hS2, kwSt])
  have hfin : Function.update (Function.update S2 (.inr .Y) (S (.inr .Y))) (.inr .kS)
      (S (.inr .kS)) =
      Function.update S (.inl 1) (natSyms (tripleWb 100 ^ c6K e) ++ S (.inl 1)) := by
    funext k
    rcases k with i | x
    · fin_cases i <;> simp [hS2, kwSt]
    · cases x <;> simp [hS2, kwSt]
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1
    (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3 h4))) hfin) (fun _ _ => trivial) ?_
  have := bitLen_one
  unfold wCost
  omega

/-! ## Cost bounds -/

/-- The constant of the threshold kernel. -/
def tC (q : ℕ) : ℕ := 1200000 + 7100 * (bitLen (q ^ 2) + 71) ^ 2

/-- The constant of the `W_b^k` kernel. -/
def wC : ℕ := 1200000

theorem c6K_le_self (e : ℕ) : c6K e ≤ e :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < tripleM 100)).le

theorem bitLen_W_pow_le (e : ℕ) : bitLen (tripleWb 100 ^ c6K e) ≤ 68 * e + 1 := by
  have h1 := bitLen_pow_le' (tripleWb 100) (c6K e)
  have h2 : bitLen (tripleWb 100) ≤ 68 := bitLen_le_of_lt' (by decide)
  have h3 := c6K_le_self e
  have h4 : c6K e * bitLen (tripleWb 100) ≤ e * 68 := Nat.mul_le_mul h3 h2
  omega

theorem kw_bounds (e : ℕ) :
    clogCost (tripleM 100) e ≤ (1 * (200 * 22 ^ 2 + 1) + 40) * (e + 1) ^ 3 ∧
      powCost (tripleWb 100) 1 (c6K e) ≤ 1 * (200 * 71 ^ 2 + 1) * (e + 1) ^ 3 := by
  have hk := c6K_le_self e
  have hbm : bitLen (tripleM 100) ≤ 20 := bitLen_le_of_lt' (by decide)
  have hbW : bitLen (tripleWb 100) ≤ 68 := bitLen_le_of_lt' (by decide)
  have hbe := bitLen_le_self' e
  have hWk := bitLen_W_pow_le e
  have hE : 1 ≤ e + 1 := by omega
  refine ⟨clogCost_le hE (by show c6K e + 1 ≤ 1 * (e + 1); omega) (by omega),
    powCost_le hE (by omega) (by rw [one_mul]; omega)⟩

theorem tCost_le {q : ℕ} (hq : 2 ≤ q) (e : ℕ) : tCost q e ≤ tC q * (e + 1) ^ 3 := by
  obtain ⟨c1, c2⟩ := kw_bounds e
  have hk := c6K_le_self e
  have ht : c6T q e ≤ 34 * e := (AppC.C6Aux.c6T_le hq e).trans (by omega)
  have hbk := bitLen_le_self' (c6K e)
  have hbt := bitLen_le_self' (c6T q e)
  have hWk := bitLen_W_pow_le e
  have hE : 1 ≤ e + 1 := by omega
  have hE3 : e + 1 ≤ (e + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have c3 : clogCost (q ^ 2) (tripleWb 100 ^ c6K e) ≤
      (35 * (200 * (bitLen (q ^ 2) + 71) ^ 2 + 1) + 40) * (e + 1) ^ 3 :=
    clogCost_le hE (by show c6T q e + 1 ≤ 35 * (e + 1); omega)
      (by nlinarith [Nat.zero_le (bitLen (q ^ 2) * e)])
  have hrest : 9 * bitLen (c6T q e) + 2 * bitLen (tripleWb 100 ^ c6K e) + 2 * bitLen (c6K e) +
      20 ≤ 466 * (e + 1) ^ 3 := by omega
  generalize hY : (bitLen (q ^ 2) + 71) ^ 2 = Y at c3
  generalize hE3' : (e + 1) ^ 3 = E3 at c1 c2 c3 hrest ⊢
  have hsum : tCost q e ≤ 1105600 * E3 + 7000 * (Y * E3) := by
    unfold tCost
    nlinarith
  calc tCost q e ≤ 1105600 * E3 + 7000 * (Y * E3) := hsum
    _ ≤ tC q * E3 := by
      rw [tC, hY]
      nlinarith [Nat.zero_le (Y * E3), Nat.zero_le E3]

theorem wCost_le (e : ℕ) : wCost e ≤ wC * (e + 1) ^ 3 := by
  obtain ⟨c1, c2⟩ := kw_bounds e
  have hbk := bitLen_le_self' (c6K e)
  have hk := c6K_le_self e
  have hWk := bitLen_W_pow_le e
  have hE3 : e + 1 ≤ (e + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hrest : 9 * bitLen (tripleWb 100 ^ c6K e) + 2 * bitLen (c6K e) + 20 ≤
      700 * (e + 1) ^ 3 := by omega
  generalize hE3' : (e + 1) ^ 3 = E3 at c1 c2 hrest ⊢
  unfold wCost wC
  linarith

/-! ## The kernels in `KContract` form -/

/-- **Threshold kernel** (an internal kernel specification of this file): stack `0`
holds `e` (restored), `natSyms (c6T q e)` is pushed on stack `1`, every other stack is restored.
Cost `C·(e + 1)^3`. -/
def C6TPushSpec (q : ℕ) : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (e : ℕ) (r0 : List Sym) (S : KLoc (Fin 2) E → List Sym), TermOK r0 →
      S (.inl 0) = natSyms e ++ r0 →
      Runs P S (Function.update S (.inl 1) (natSyms (c6T q e) ++ S (.inl 1))) (fun _ => True)
        (C * (e + 1) ^ 3)

/-- **`W_b^k` kernel** (an internal kernel specification of this file): as
`C6TPushSpec`, pushing `natSyms (tripleWb 100 ^ c6K e)` (independent of `q`). -/
def C6WPushSpec : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (e : ℕ) (r0 : List Sym) (S : KLoc (Fin 2) E → List Sym), TermOK r0 →
      S (.inl 0) = natSyms e ++ r0 →
      Runs P S (Function.update S (.inl 1) (natSyms (tripleWb 100 ^ c6K e) ++ S (.inl 1)))
        (fun _ => True) (C * (e + 1) ^ 3)

/-- The threshold kernel `tKerP q` (registers `NatArith.Reg`, scratch `TS`), constant `tC q`. -/
theorem c6TPush_holds {q : ℕ} (hq : 2 ≤ q) : C6TPushSpec q :=
  ⟨tC q, fun _ => ⟨TS, inferInstance, inferInstance, NatArith.Reg, tKerP q, inferInstance,
    inferInstance, closed_tKerP q, fun e r0 S hr0 hS =>
      WP.W9comp.runs_mono (runs_tKerP hq e r0 S hr0 hS) (fun _ _ => trivial) (tCost_le hq e)⟩⟩

/-- The `W_b^k` kernel `wKerP` (registers `NatArith.Reg`, scratch `TS`), constant `wC`. -/
theorem c6WPush_holds : C6WPushSpec :=
  ⟨wC, fun _ => ⟨TS, inferInstance, inferInstance, NatArith.Reg, wKerP, inferInstance,
    inferInstance, closed_wKerP, fun e r0 S hr0 hS =>
      WP.W9comp.runs_mono (runs_wKerP e r0 S hr0 hS) (fun _ _ => trivial) (wCost_le e)⟩⟩

end AppC.C6JoinAux

end SubNLogN.Machine
