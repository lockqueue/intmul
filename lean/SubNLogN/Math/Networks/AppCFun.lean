import SubNLogN.Math.Networks.Framed
import SubNLogN.Math.Networks.AppCShear
import SubNLogN.Math.Networks.AppCLayer

/-!
# Networks: functional specifications for Appendix A (serialization of the framed network; Lemma A.9 (`lem:transfer13`) repair)

Functional (value-level) facts that the machine kernels of Appendix A realize; no cost model (machine-level
step bounds are proved in `SubNLogN/Machine/`). Contracts are `def …Stmt : Prop`.

1. **Serialization** (Proposition A.7 (`prop:transfer11`), [OAI26, §3.2, (5)]): the
   framed network `framedNet` (stage-parallel definition) equals the sequential execution of one
   explicit ordered event list `nodeEvents`: for each stage `j = 1, 2, 3`, each invocation `ι` (in
   the fixed order of `Finset.univ.toList`), each time `r = 0, …, 7`: the incoming edge operator of
   every wire touched at `(j, ι, r)` (in the fixed order of roles), then the scalar row of `(j, ι)`
   at time `r`; finally the edge into the sink of every role. This holds for ARBITRARY edge operators
   (no linearity needed) because invocations of one stage act on disjoint roles and every row reads
   and writes only wires touched at its time. A machine executing `nodeEvents` therefore executes the
   framed network.
2. **Lemma A.9 (`lem:transfer13`) repair**: on the full rectangle `[2^L]³` the
   eight packed shifts `S₀` and the ideal map `T₀` are bijections, `S₀` maps the good set (resp. the
   bad set `B`) onto itself; with `PackedAgreeStmt` this makes `T₀ S₀⁻¹` a permutation supported on
   `B`, which the stable radix sort applies. The omitted top selected bit is then flipped by a
   two-digit permutation (`packedTopXor`), and the composite is the full selected-bit XOR.
3. **Guard arithmetic** (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`)): closure of guarded Gaussian dyadics
   under the elementary operations of the exact C-layer, and the depth recurrence
   `A ≤ s·A_child + E_*` over sequential children solved to `C_dep d⁶`.
4. **Lemma A.10 (`lem:transfer-phase`) kernel facts**: the inverse child
   `(C⁻¹)^{⊗f} = (−i)^f Z^{⊗f} C^{⊗f} Z^{⊗f}`, and a coordinate kernel `aI + bX_{e_j}` on `f` columns
   is exactly `C^{⊗f}` on the `f` bits of slot `j` (identity on all other bits).
-/

namespace SubNLogN.Math.Networks

/-! ## 1. Serialization of the framed network -/

/-- Events of the time-ordered serialization of a framed network. -/
inductive NodeEvent (κ : Kind) (h : ℕ) where
  /-- apply the edge of `w` entering vertex `v` (if any) to the value of `w` -/
  | edge (w : Role κ h) (v : Vertex κ h)
  /-- the scalar row of invocation `(j, ι)` at time `r` -/
  | row (j : Stage) (ι : Fix h) (r : Fin 8)

/-- The ordered event list (stages, invocations, times, touched wires, row; then sink edges). -/
noncomputable def nodeEvents (κ : Kind) (h : ℕ) : List (NodeEvent κ h) :=
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix h)).toList.flatMap fun ι =>
    (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role κ h)).toList.filterMap fun w =>
        (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) ++ [NodeEvent.row j ι r]) ++
  (Finset.univ : Finset (Role κ h)).toList.map fun w => NodeEvent.edge w (.sink w)

variable {h : ℕ} {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

open Classical in
/-- Semantics of one event. -/
noncomputable def NodeEvent.run (κ : Kind) (half : R) (E : EdgeOps κ h A) :
    NodeEvent κ h → (Role κ h → A) → (Role κ h → A)
  | .edge w v, s => Function.update s w
      (match edgeInto w v with
       | some e => E w e (s w)
       | none => s w)
  | .row j ι r, s => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : R) s

/-- Sequential execution of an event list. -/
noncomputable def runEvents (κ : Kind) (half : R) (E : EdgeOps κ h A) (evs : List (NodeEvent κ h))
    (s : Role κ h → A) : Role κ h → A :=
  evs.foldl (fun s ev => ev.run κ half E s) s

/-- CONTRACT (serialization). For every `h`, both networks, any coefficient ring, any
module and ARBITRARY edge operators, executing `nodeEvents` sequentially equals `framedNet`. -/
def SerialEqFramedStmt (h : ℕ) : Prop :=
  ∀ (κ : Kind) {Rg Ar : Type} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar] (half : Rg)
    (E : EdgeOps κ h Ar) (s : Role κ h → Ar),
    runEvents κ half E (nodeEvents κ h) s = framedNet κ half E s

/-! ## 2. Lemma A.9 (`lem:transfer13`): the repair permutation and the top selected bit -/

/-- The full rectangle `[2^L]³` of chunk triples. -/
def packedRect (L : ℕ) : Set (ℕ × ℕ × ℕ) := {p | p.1 < 2 ^ L ∧ p.2.1 < 2 ^ L ∧ p.2.2 < 2 ^ L}

/-- The good set (complement of the exceptional set `B`). -/
def packedGoodSet (K ρ f : ℕ) : Set (ℕ × ℕ × ℕ) := {p | packedGood K ρ f p}

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) repair). For `K ≥ 6`, `L = fK`, `ρ < K`:
`S₀` and `T₀` are bijections of `[2^L]³`; `S₀` maps the good part onto itself and the bad part onto
itself. Together with `PackedAgreeStmt` (agreement off `B`) this says that `T₀ ∘ S₀⁻¹` is a
permutation of `[2^L]³` supported on `B`. -/
def PackedRepairStmt : Prop :=
  ∀ (L K ρ f : ℕ), 6 ≤ K → L = f * K → ρ < K →
    Set.BijOn (packedS0 L K ρ f) (packedRect L) (packedRect L) ∧
    Set.BijOn (packedT0 K ρ f) (packedRect L) (packedRect L) ∧
    Set.BijOn (packedS0 L K ρ f) (packedRect L ∩ packedGoodSet K ρ f)
      (packedRect L ∩ packedGoodSet K ρ f) ∧
    Set.BijOn (packedS0 L K ρ f) (packedRect L \ packedGoodSet K ρ f)
      (packedRect L \ packedGoodSet K ρ f)

/-- The omitted top selected bit: `y_{j_{f−1}} ← y_{j_{f−1}} ⊕ x_{j_{f−1}}`, `j_{f−1} = ρ + (f−1)K`
(a fixed permutation of a pair of binary digits, `lem:transfer-streams` (1)). -/
def packedTopXor (K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (xyz.1, Nat.xor xyz.2.1 (2 ^ (ρ + (f - 1) * K) * bitAt xyz.1 (ρ + (f - 1) * K)), xyz.2.2)

/-- The full packed selected-bit addition of Lemma A.9 (`lem:transfer13`): `y_{j_i} ← y_{j_i} ⊕ x_{j_i}` for all `i < f`. -/
def packedFull (K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (xyz.1, Nat.xor xyz.2.1 (∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * bitAt xyz.1 (ρ + i * K)), xyz.2.2)

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) composition). For `f ≥ 1`: the top-bit flip after `T₀` is the full selected-bit
XOR (`x` and `z` unchanged, `z` restored for every initial value). -/
def PackedFullStmt : Prop :=
  ∀ (K ρ f : ℕ), 1 ≤ f → ρ < K → ∀ xyz : ℕ × ℕ × ℕ,
    packedTopXor K ρ f (packedT0 K ρ f xyz) = packedFull K ρ f xyz

/-! ## 3. Guard arithmetic -/

/-- Gaussian dyadics with denominator `2^a` whose real and imaginary parts are at most `2^b` in
absolute value. -/
def GaussDyadic (a b : ℕ) (z : ℂ) : Prop :=
  (∃ m n : ℤ, z = ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a) ∧ |z.re| ≤ 2 ^ b ∧ |z.im| ≤ 2 ^ b

/-- CONTRACT (guard closure, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)): addition and subtraction at most
double the bound, halving adds one denominator bit, sign changes and multiplication by `i` preserve
both bounds; both bounds are monotone. Hence a value at charged depth `j` computed from disk values
on the `2^{-P}` grid satisfies `GaussDyadic (P + j) j`. -/
def GuardDyadicStmt : Prop :=
  ∀ (a b : ℕ) (z w : ℂ), GaussDyadic a b z → GaussDyadic a b w →
    GaussDyadic a (b + 1) (z + w) ∧ GaussDyadic a (b + 1) (z - w) ∧
    GaussDyadic (a + 1) b (z / 2) ∧ GaussDyadic a b (-z) ∧ GaussDyadic a b (Complex.I * z) ∧
    (∀ a', a ≤ a' → GaussDyadic a' b z) ∧ (∀ b', b ≤ b' → GaussDyadic a b' z)

/-- CONTRACT (representation, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)): a value with `GaussDyadic a b z`
has integer numerators `m, n` at denominator `2^a` with `|m|, |n| ≤ 2^{a+b}`, i.e. it is held
exactly by `a` fractional and `b + 2` integer-and-sign bits per real component. -/
def GuardReprStmt : Prop :=
  ∀ (a b : ℕ) (z : ℂ), GaussDyadic a b z →
    ∃ m n : ℤ, z = ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a ∧ |m| ≤ 2 ^ (a + b) ∧ |n| ≤ 2 ^ (a + b)

/-- CONTRACT (depth recurrence over sequential children, Proposition A.11 (`prop:prop14-param`), Appendix A.6
(`sec:transfer-layer`)). Let `m > 1`, `1 < s < m⁵` (`s = s_c`, `sc_lt_m_pow5`), `E ≥ 0` (`E = E_*`), `d ≥ 1`, and
`m^(j_max − 1) ≤ d` (`j_max ≤ ⌈log_m d⌉`). If the leaf depth is `A 0 ≤ 8d` and every internal level
satisfies `A (j+1) ≤ s·A j + E`, then `A j_max ≤ s(8 + E/(s−1))·d⁶ = C_dep d⁶`. -/
def GuardRecurrenceStmt : Prop :=
  ∀ (m s E d : ℝ) (jmax : ℕ) (A : ℕ → ℝ), 1 < m → 1 < s → s < m ^ 5 → 0 ≤ E → 1 ≤ d →
    m ^ (jmax - 1) ≤ d → A 0 ≤ 8 * d → (∀ j < jmax, A (j + 1) ≤ s * A j + E) →
    A jmax ≤ s * (8 + E / (s - 1)) * d ^ 6

/-! ## 4. Lemma A.10 (`lem:transfer-phase`) kernel facts -/

/-- `Z = diag(1, −1)` on one binary coordinate. -/
noncomputable def Zmat : Matrix (ZMod 2) (ZMod 2) ℂ := Matrix.diagonal fun x => (-1 : ℂ) ^ x.val

/-- CONTRACT (inverse child, Lemma A.10 (`lem:transfer-phase`), Appendix A.5 (`sec:transfer-frames`)): `C⁻¹ = −i Z C Z`, hence on `f`
columns `(C^{⊗f})⁻¹ = (−i)^f Z^{⊗f} C^{⊗f} Z^{⊗f}` (one forward child plus address signs and a
constant phase). -/
def InverseKernelStmt : Prop :=
  C2⁻¹ = (-Complex.I) • (Zmat * C2 * Zmat) ∧
  ∀ f : ℕ, (tpow f C2)⁻¹ = (-Complex.I) ^ f • (tpow f Zmat * tpow f C2 * tpow f Zmat)

/-- CONTRACT (coordinate kernel = child on one slot, Lemma A.10 (`lem:transfer-phase`)). On `f`
columns (`x : Fin f → Pt h`), the kernel `aI + bX_{e_j}` acts as `C^{⊗f}` on the `f` bits
`(x c j)_c` of slot `j` and as the identity on all other bits. -/
def KernelSlotStmt (h : ℕ) : Prop :=
  ∀ (f : ℕ) (j : Cube h) (x y : Fin f → Pt h),
    tpow f (Kv (Pi.single j 1) 1) x y =
      if ∀ c, ∀ p, p ≠ j → x c p = y c p then tpow f C2 (fun c => x c j) (fun c => y c j) else 0

end SubNLogN.Math.Networks
