import WP.W7k2.Ops2
import WP.W7k2.Arith

/-!
# WP.W7k3t.Base — instances, uniform operation costs, update-chain normalisation

`W7_sincGaussianTap` is built from sub-kernels: closed programs on their own hosts `Loc n (24 - n)`,
packaged as instances (`mkInst`) and called with `callI … (lid I.R)` (`tsub_ht`). They call the
frozen machine contracts through the instance bundle `TI`.

* `TI`: one instance per contract used; register file `TI.R`; lenses.
* `TI.Ok I U`: all instance bodies with one constant `U` (multiplication at `U·(w+1)²`).
* `uc U W = U·(W+1)²` bounds the cost of any single operation whose operands have bit length `≤ W`,
  and of a raw push / pop.
* `Big a b`: hosts with at least 24 stacks (room for every callee's scratch stacks).
* `lix`, `uswap`, `uself`: sorting / merging / dropping of `Function.update` chains.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-! ## Contract bodies not in W7k2 -/

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_cmpInt`. -/
def SpecCmpInt (I : Inst 2 4 Ordering) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S S (fun r => I.obs r = cmpZ a b) (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W6a_divRound`. -/
def SpecDivRound (I : Inst 3 6 Unit) (C : ℕ) : Prop :=
  ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), 0 < den →
    TermOK ra → TermOK rb →
    S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
      (fun _ => True)
      (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

/-- Body of `W5_mulAt`, at the quadratic cost `U·(w+1)²`. -/
def SpecMulQ (I : Inst 3 8 Unit) (U : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (U * (w + 1) ^ 2)

/-! ## The instance bundle -/

/-- The contract instances the tap kernel calls (one per contract). -/
structure TI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sv : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  ai : Inst 3 4 Unit
  si : Inst 3 4 Unit
  ci : Inst 2 4 Ordering
  mu : Inst 3 8 Unit
  dv : Inst 3 6 Unit

/-- Push a lens one product component to the right. -/
def lsc {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- The identity lens: sub-kernels share the host's register file. -/
def lid (σ : Type) : Lens σ σ where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

namespace TI

variable (I : TI)

/-- Registers: one register file per instance. -/
abbrev R : Type :=
  I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.sv.R × I.cm.R × I.ai.R × I.si.R ×
    I.ci.R × I.mu.R × I.dv.R

def lcp : Lens I.R I.cp.R := Lens.fst _ _
def ldr : Lens I.R I.dr.R := lsc (Lens.fst _ _)
def liz : Lens I.R I.iz.R := lsc (lsc (Lens.fst _ _))
def ldc : Lens I.R I.dc.R := lsc (lsc (lsc (Lens.fst _ _)))
def lic : Lens I.R I.ic.R := lsc (lsc (lsc (lsc (Lens.fst _ _))))
def lad : Lens I.R I.ad.R := lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))
def lsv : Lens I.R I.sv.R := lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))
def lcm : Lens I.R I.cm.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))
def lai : Lens I.R I.ai.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))
def lsi : Lens I.R I.si.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))))
def lci : Lens I.R I.ci.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))))))
def lmu : Lens I.R I.mu.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))))))
def ldv : Lens I.R I.dv.R :=
  lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.snd _ _)))))))))))

theorem R_finite : Finite I.R := by
  haveI := I.cp.fin
  haveI := I.dr.fin
  haveI := I.iz.fin
  haveI := I.dc.fin
  haveI := I.ic.fin
  haveI := I.ad.fin
  haveI := I.sv.fin
  haveI := I.cm.fin
  haveI := I.ai.fin
  haveI := I.si.fin
  haveI := I.ci.fin
  haveI := I.mu.fin
  haveI := I.dv.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  haveI := I.cp.ne
  haveI := I.dr.ne
  haveI := I.iz.ne
  haveI := I.dc.ne
  haveI := I.ic.ne
  haveI := I.ad.ne
  haveI := I.sv.ne
  haveI := I.cm.ne
  haveI := I.ai.ne
  haveI := I.si.ne
  haveI := I.ci.ne
  haveI := I.mu.ne
  haveI := I.dv.ne
  infer_instance

/-- All instance bodies with one constant `U` (multiplication at `U·(w+1)²`). -/
structure Ok (U : ℕ) : Prop where
  cp : SpecCopy I.cp U
  dr : SpecDrop I.dr U
  iz : SpecIsZero I.iz U
  dc : SpecDec I.dc U
  ic : SpecInc I.ic U
  ad : SpecAddNat I.ad U
  sv : SpecShlVar I.sv U
  cm : SpecCmpNat I.cm U
  ai : SpecAddInt I.ai U
  si : SpecSubInt I.si U
  ci : SpecCmpInt I.ci U
  mu : SpecMulQ I.mu U
  dv : SpecDivRound I.dv U
  one : 1 ≤ U

end TI

/-! ## Hosts and uniform costs -/

/-- Hosts with at least 24 stacks: room for every callee's scratch stacks. -/
class Big (a b : ℕ) : Prop where
  le : 24 ≤ a + b

/-- Uniform cost bound of one operation on operands of bit length `≤ W`. -/
def uc (U W : ℕ) : ℕ := U * (W + 1) ^ 2

theorem uc_lin {U W x : ℕ} (h : x ≤ W) : U * (x + 1) ≤ uc U W := by
  unfold uc
  apply Nat.mul_le_mul_left
  nlinarith

theorem uc_lin2 {U W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W) : U * (x + y + 1) ≤ uc U W := by
  unfold uc
  apply Nat.mul_le_mul_left
  nlinarith

theorem uc_quad {U W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W) :
    U * (x * y + x + y + 1) ≤ uc U W := by
  unfold uc
  apply Nat.mul_le_mul_left
  nlinarith [Nat.mul_le_mul hx hy]

theorem uc_const {U W : ℕ} : U ≤ uc U W := by
  unfold uc
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem uc_one {U W : ℕ} (hU : 1 ≤ U) : 1 ≤ uc U W := le_trans hU uc_const

/-! ## Update-chain normalisation -/

/-- A numbering of the stacks of `Loc n m`, used to sort update chains. -/
def lix {n m : ℕ} : Loc n m → ℕ
  | .inl i => i.val
  | .inr j => n + j.val

theorem uswap {n m : ℕ} {f : Loc n m → List Sym} {x y : Loc n m} (v w : List Sym)
    (h : lix y < lix x) :
    Function.update (Function.update f x v) y w = Function.update (Function.update f y w) x v := by
  have hne : x ≠ y := fun e => by rw [e] at h; exact lt_irrefl _ h
  exact Function.update_comm hne v w f

/-- A no-op update (a stack restored to its content) disappears. -/
theorem uself {α : Type} [DecidableEq α] {f : α → List Sym} {x : α} {v : List Sym}
    (h : f x = v) : Function.update f x v = f := by
  rw [← h]
  exact Function.update_eq_self x f

#assert_std_axioms TI.R_finite TI.R_nonempty uc_lin uc_lin2 uc_quad uc_const uc_one uswap uself

end WP.W7k3t
