import WP.W9g.Macros
import Contracts.Machine.W3
import Contracts.Machine.W5

/-!
# WP.W9g.Ops — the contract programs used by the leaf kernel, and their call rules

The leaf kernel multiplies with `W5_mulAt Mul` and does linear arithmetic with four W3 contracts:
`W3_addInt`, `W3_subInt`, `W3_shlVar`, `W3_shrVar`. Everything else (copies, counters, sign
symbols, records) uses the framework library or `WP.W9g.Macros`.

* `Inst n cap`: one witness of a contract with `n` named stacks and `≤ cap` scratch stacks.
* `Prims`: the five witnesses; `Prims.Reg` their registers; programs of the kernel have registers
  `Option Sym × X.Reg`.
* `MulOK`, `AddOK`, `SubOK`, `ShlOK`, `ShrOK`: the contract bodies for one witness. `prims_of`
  extracts witnesses (and one cost constant per contract) from the contract hypotheses.
* `emb3`/`emb2`: place a callee's named stacks on given host stacks and its scratch stacks on a host
  *pool* `Fin 8 → K` (scratch content is arbitrary and restored, so the pool is shared by all calls).
* `callMul` … `callShr` and their rules `callMul_rs` … `callShr_rs` (exact single-stack updates).
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts

/-! ## Witnesses -/

/-- One witness of a contract with `n` named stacks and at most `cap` scratch stacks. -/
structure Inst (n cap : ℕ) : Type 1 where
  /-- number of scratch stacks -/
  m : ℕ
  /-- register type -/
  R : Type
  /-- the program -/
  P : Prog (Loc n m) (fun _ => Sym) R
  hm : m ≤ cap
  fin : Finite R
  ne : Nonempty R
  cl : P.Closed

/-- The contract programs of the leaf kernel. -/
structure Prims : Type 1 where
  /-- `W5_mulAt` -/
  mul : Inst 3 8
  /-- `W3_addInt` -/
  add : Inst 3 4
  /-- `W3_subInt` -/
  sub : Inst 3 4
  /-- `W3_shlVar` -/
  shl : Inst 2 4
  /-- `W3_shrVar` -/
  shr : Inst 2 4

/-- Registers of the contract programs. -/
abbrev Prims.Reg (X : Prims) : Type := X.mul.R × X.add.R × X.sub.R × X.shl.R × X.shr.R

theorem Prims.reg_finite (X : Prims) : Finite X.Reg := by
  haveI := X.mul.fin; haveI := X.add.fin; haveI := X.sub.fin; haveI := X.shl.fin
  haveI := X.shr.fin
  infer_instance

theorem Prims.reg_nonempty (X : Prims) : Nonempty X.Reg := by
  haveI := X.mul.ne; haveI := X.add.ne; haveI := X.sub.ne; haveI := X.shl.ne; haveI := X.shr.ne
  infer_instance

/-- Lenses onto the contract registers inside `Option Sym × X.Reg`. -/
def lMul (X : Prims) : Lens (Option Sym × X.Reg) X.mul.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lAdd (X : Prims) : Lens (Option Sym × X.Reg) X.add.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lSub (X : Prims) : Lens (Option Sym × X.Reg) X.sub.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lShl (X : Prims) : Lens (Option Sym × X.Reg) X.shl.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lShr (X : Prims) : Lens (Option Sym × X.Reg) X.shr.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

/-! ## Contract bodies for one witness -/

/-- `W5_mulAt` body. -/
def MulOK (Mul : ℕ → ℕ) (I : Inst 3 8) (C : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (C * Mul w + C)

/-- `W3_addInt` body. -/
def AddOK (I : Inst 3 4) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- `W3_subInt` body. -/
def SubOK (I : Inst 3 4) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- `W3_shlVar` body. -/
def ShlOK (I : Inst 2 4) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1))

/-- `W3_shrVar` body. -/
def ShrOK (I : Inst 2 4) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- All five bodies, with cost constants. -/
def Prims.OK (X : Prims) (Mul : ℕ → ℕ) (CM CA CS CL CR : ℕ) : Prop :=
  MulOK Mul X.mul CM ∧ AddOK X.add CA ∧ SubOK X.sub CS ∧ ShlOK X.shl CL ∧ ShrOK X.shr CR

/-- **Witness extraction** from the contract hypotheses. -/
theorem prims_of (Mul : ℕ → ℕ) (hM : W5_mulAt Mul) (hA : W3_addInt) (hS : W3_subInt)
    (hL : W3_shlVar) (hR : W3_shrVar) :
    ∃ (X : Prims) (CM CA CS CL CR : ℕ), X.OK Mul CM CA CS CL CR := by
  obtain ⟨CM, hM⟩ := hM
  obtain ⟨m1, R1, -, P1, hm1, f1, n1, c1, s1⟩ := hM ()
  obtain ⟨CA, hA⟩ := hA
  obtain ⟨m2, R2, -, P2, hm2, f2, n2, c2, s2⟩ := hA ()
  obtain ⟨CS, hS⟩ := hS
  obtain ⟨m3, R3, -, P3, hm3, f3, n3, c3, s3⟩ := hS ()
  obtain ⟨CL, hL⟩ := hL
  obtain ⟨m4, R4, -, P4, hm4, f4, n4, c4, s4⟩ := hL ()
  obtain ⟨CR, hR⟩ := hR
  obtain ⟨m5, R5, -, P5, hm5, f5, n5, c5, s5⟩ := hR ()
  exact ⟨⟨⟨m1, R1, P1, hm1, f1, n1, c1⟩, ⟨m2, R2, P2, hm2, f2, n2, c2⟩,
    ⟨m3, R3, P3, hm3, f3, n3, c3⟩, ⟨m4, R4, P4, hm4, f4, n4, c4⟩, ⟨m5, R5, P5, hm5, f5, n5, c5⟩⟩,
    CM, CA, CS, CL, CR, s1, s2, s3, s4, s5⟩

/-! ## Embeddings -/

section Emb

variable {K : Type}

/-- Callee with three named stacks: named stacks on `x y z`, scratch on the pool. -/
def emb3 (pool : Fin 8 → K) {m : ℕ} (hm : m ≤ 8) (x y z : K) : Loc 3 m → K
  | .inl i => if i.1 = 0 then x else if i.1 = 1 then y else z
  | .inr j => pool ⟨j.1, by have := j.2; omega⟩

/-- Callee with two named stacks. -/
def emb2 (pool : Fin 8 → K) {m : ℕ} (hm : m ≤ 8) (x y : K) : Loc 2 m → K
  | .inl i => if i.1 = 0 then x else y
  | .inr j => pool ⟨j.1, by have := j.2; omega⟩

theorem emb3_inj (pool : Fin 8 → K) (hp : Function.Injective pool) {m : ℕ} (hm : m ≤ 8)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : ∀ j, pool j ≠ x)
    (hy : ∀ j, pool j ≠ y) (hz : ∀ j, pool j ≠ z) : Function.Injective (emb3 pool hm x y z) := by
  intro a b h
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩ <;> rcases b with ⟨i', hi'⟩ | ⟨j', hj'⟩ <;>
    simp only [emb3] at h
  · have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have h3' : i' = 0 ∨ i' = 1 ∨ i' = 2 := by omega
    rcases h3 with rfl | rfl | rfl <;> rcases h3' with rfl | rfl | rfl <;> simp_all
  · exfalso
    split_ifs at h
    · exact hx _ h.symm
    · exact hy _ h.symm
    · exact hz _ h.symm
  · exfalso
    split_ifs at h
    · exact hx _ h
    · exact hy _ h
    · exact hz _ h
  · have := Fin.mk.inj (hp h)
    subst this
    rfl

theorem emb2_inj (pool : Fin 8 → K) (hp : Function.Injective pool) {m : ℕ} (hm : m ≤ 8)
    {x y : K} (hxy : x ≠ y) (hx : ∀ j, pool j ≠ x) (hy : ∀ j, pool j ≠ y) :
    Function.Injective (emb2 pool hm x y) := by
  intro a b h
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩ <;> rcases b with ⟨i', hi'⟩ | ⟨j', hj'⟩ <;>
    simp only [emb2] at h
  · have h2 : i = 0 ∨ i = 1 := by omega
    have h2' : i' = 0 ∨ i' = 1 := by omega
    rcases h2 with rfl | rfl <;> rcases h2' with rfl | rfl <;> simp_all
  · exfalso
    split_ifs at h
    · exact hx _ h.symm
    · exact hy _ h.symm
  · exfalso
    split_ifs at h
    · exact hx _ h
    · exact hy _ h
  · have := Fin.mk.inj (hp h)
    subst this
    rfl

theorem le8_of_le4 {m : ℕ} (h : m ≤ 4) : m ≤ 8 := h.trans (by decide)

end Emb

/-! ## Calls -/

section Calls

variable {K : Type} (X : Prims) (pool : Fin 8 → K)

/-- `z += x * y` (W5). -/
def callMul (x y z : K) : MProg K X.Reg := WP.W6a.call (emb3 pool X.mul.hm x y z) (lMul X) X.mul.P

/-- `z += x + y` (W3, signed). -/
def callAdd (x y z : K) : MProg K X.Reg :=
  WP.W6a.call (emb3 pool (le8_of_le4 X.add.hm) x y z) (lAdd X) X.add.P

/-- `z += x - y` (W3, signed). -/
def callSub (x y z : K) : MProg K X.Reg :=
  WP.W6a.call (emb3 pool (le8_of_le4 X.sub.hm) x y z) (lSub X) X.sub.P

/-- `x := x · 2^c` (W3, unsigned, counter on `c`). -/
def callShl (x c : K) : MProg K X.Reg :=
  WP.W6a.call (emb2 pool (le8_of_le4 X.shl.hm) x c) (lShl X) X.shl.P

/-- `x := x / 2^c` (W3, unsigned, counter on `c`). -/
def callShr (x c : K) : MProg K X.Reg :=
  WP.W6a.call (emb2 pool (le8_of_le4 X.shr.hm) x c) (lShr X) X.shr.P

theorem callMul_closed (x y z : K) : (callMul X pool x y z).Closed :=
  WP.W6a.closed_call _ _ X.mul.cl
theorem callAdd_closed (x y z : K) : (callAdd X pool x y z).Closed :=
  WP.W6a.closed_call _ _ X.add.cl
theorem callSub_closed (x y z : K) : (callSub X pool x y z).Closed :=
  WP.W6a.closed_call _ _ X.sub.cl
theorem callShl_closed (x c : K) : (callShl X pool x c).Closed :=
  WP.W6a.closed_call _ _ X.shl.cl
theorem callShr_closed (x c : K) : (callShr X pool x c).Closed :=
  WP.W6a.closed_call _ _ X.shr.cl

variable [DecidableEq K] {X} {pool}

theorem callMul_rs {Mul : ℕ → ℕ} {C : ℕ} (hM : MulOK Mul X.mul C) (hp : Function.Injective pool)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : ∀ j, pool j ≠ x)
    (hy : ∀ j, pool j ≠ y) (hz : ∀ j, pool j ≠ z) (w : ℕ) (a b : ℤ) (ra rb : List Sym)
    (σ : K → List Sym) (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w) (hra : TermOK ra)
    (hrb : TermOK rb) (hX : σ x = intSyms a ++ ra) (hY : σ y = intSyms b ++ rb) :
    RS [] (callMul X pool x y z) σ (Function.update σ z (intSyms (a * b) ++ σ z))
      (C * Mul w + C) :=
  rs_call (emb3_inj pool hp X.mul.hm hxy hxz hyz hx hy hz) (lMul X) (.inl 2) _
    (hM w a b ra rb _ hwa hwb hra hrb hX hY)

theorem callAdd_rs {C : ℕ} (hA : AddOK X.add C) (hp : Function.Injective pool)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : ∀ j, pool j ≠ x)
    (hy : ∀ j, pool j ≠ y) (hz : ∀ j, pool j ≠ z) (a b : ℤ) (ra rb : List Sym)
    (σ : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb) (hX : σ x = intSyms a ++ ra)
    (hY : σ y = intSyms b ++ rb) :
    RS [] (callAdd X pool x y z) σ (Function.update σ z (intSyms (a + b) ++ σ z))
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1)) :=
  rs_call (emb3_inj pool hp _ hxy hxz hyz hx hy hz) (lAdd X) (.inl 2) _
    (hA a b ra rb _ hra hrb hX hY)

theorem callSub_rs {C : ℕ} (hS : SubOK X.sub C) (hp : Function.Injective pool)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : ∀ j, pool j ≠ x)
    (hy : ∀ j, pool j ≠ y) (hz : ∀ j, pool j ≠ z) (a b : ℤ) (ra rb : List Sym)
    (σ : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb) (hX : σ x = intSyms a ++ ra)
    (hY : σ y = intSyms b ++ rb) :
    RS [] (callSub X pool x y z) σ (Function.update σ z (intSyms (a - b) ++ σ z))
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1)) :=
  rs_call (emb3_inj pool hp _ hxy hxz hyz hx hy hz) (lSub X) (.inl 2) _
    (hS a b ra rb _ hra hrb hX hY)

theorem callShl_rs {C : ℕ} (hL : ShlOK X.shl C) (hp : Function.Injective pool)
    {x c : K} (hxc : x ≠ c) (hx : ∀ j, pool j ≠ x) (hc : ∀ j, pool j ≠ c) (a k : ℕ)
    (rx rc : List Sym) (σ : K → List Sym) (hrx : TermOK rx) (hrc : TermOK rc)
    (hX : σ x = natSyms a ++ rx) (hC : σ c = natSyms k ++ rc) :
    RS [] (callShl X pool x c) σ (Function.update σ x (natSyms (a * 2 ^ k) ++ rx))
      (C * (k + bitLen k + 1)) :=
  rs_call (emb2_inj pool hp _ hxc hx hc) (lShl X) (.inl 0) _ (hL a k rx rc _ hrx hrc hX hC)

theorem callShr_rs {C : ℕ} (hR : ShrOK X.shr C) (hp : Function.Injective pool)
    {x c : K} (hxc : x ≠ c) (hx : ∀ j, pool j ≠ x) (hc : ∀ j, pool j ≠ c) (a k : ℕ)
    (rx rc : List Sym) (σ : K → List Sym) (hrx : TermOK rx) (hrc : TermOK rc)
    (hX : σ x = natSyms a ++ rx) (hC : σ c = natSyms k ++ rc) :
    RS [] (callShr X pool x c) σ (Function.update σ x (natSyms (a / 2 ^ k) ++ rx))
      (C * (min k (bitLen a) + bitLen k + 1)) :=
  rs_call (emb2_inj pool hp _ hxc hx hc) (lShr X) (.inl 0) _ (hR a k rx rc _ hrx hrc hX hC)

end Calls

#assert_std_axioms Prims.reg_finite Prims.reg_nonempty prims_of emb3_inj emb2_inj le8_of_le4
  callMul_closed callAdd_closed callSub_closed callShl_closed callShr_closed callMul_rs callAdd_rs
  callSub_rs callShl_rs callShr_rs

end WP.W9g
