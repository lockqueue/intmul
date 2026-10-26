import SubNLogN.Math.Networks.Basic

/-!
# Networks, part 2: the scalar circuits and [OAI26] Lemma 5

The scalar layer of the two networks ([OAI26, §3.1]; Fact 3.4 (`fact:oai-networks`), Appendix D.2, Proposition D.3 (`oai:networks`)). A state assigns a value
in an `R`-module `M` to every role; `M` may be the scalars themselves or arrays of them (gates act
pointwise, [OAI26, §3.2]), so the array level of the scalar statements is covered by the choice of `M`.

* bit network: `R = ZMod 2` (all coefficients `1`);
* complex network: a commutative ring `R` containing an element `half` with `2 * half = 1`
  (the paper's ring is `ℤ[i, 1/2]`).

Each schedule row is one simultaneous update reading saved inputs (its targets and controls are
disjoint). A stage applies all its invocations; they act on disjoint sets of roles, so the pointwise
definition `stageMap` equals their composition in any order.
-/

namespace SubNLogN.Math.Networks

variable {h : ℕ}

/-- The four update maps of an invocation ([OAI26, §3.1]): copy `V`, gather `G`, side injection
`J`, scatter `R`. -/
inductive Op
  | V
  | G
  | J
  | R
  deriving DecidableEq

/-- Operations of the forward schedule (2) ([OAI26, §3.1, (2)]). -/
def fwdOp : Fin 8 → Op := ![.J, .R, .V, .G, .R, .J, .G, .V]

/-- Signs of the forward schedule (2) ([OAI26, §3.1, (2)]): rows `−J, −R, +V, +G, +R, +J, −G, −V`. -/
def fwdSign : Fin 8 → ℤ := ![-1, -1, 1, 1, 1, 1, -1, -1]

/-- Operation at time `r` of stage `j`; at stage 2 time `r` uses the inverse of forward row
`7 - r` ([OAI26, §3.3]). -/
def rowOp (j : Stage) (r : Fin 8) : Op := if j.isInverse then fwdOp r.rev else fwdOp r

/-- Sign at time `r` of stage `j` (the inverse of a row negates its update). -/
def rowSign (j : Stage) (r : Fin 8) : ℤ := if j.isInverse then -fwdSign r.rev else fwdSign r

/-- Logical source data role `x_S` of invocation `(j, ι)`: bank `X`, bank `Y` at stage 2. -/
def srcRole {κ : Kind} (j : Stage) (ι : Fix h) (S : Tri h) : Role κ h :=
  if j.isInverse then .Y (Addr.mk j ι S) else .X (Addr.mk j ι S)

/-- Logical target data role `y_S` of invocation `(j, ι)`: bank `Y`, bank `X` at stage 2. -/
def tgtRole {κ : Kind} (j : Stage) (ι : Fix h) (S : Tri h) : Role κ h :=
  if j.isInverse then .X (Addr.mk j ι S) else .Y (Addr.mk j ι S)

/-- If `w` is a logical target data role of invocation `(j, ι)`, its varying triple. -/
def tgtTriple? {κ : Kind} (j : Stage) (ι : Fix h) : Role κ h → Option (Tri h)
  | .X a => if j.isInverse = true ∧ a.fix j = ι then some (a.var j) else none
  | .Y a => if j.isInverse = false ∧ a.fix j = ι then some (a.var j) else none
  | _ => none

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Side-injection coefficient of `A_{ST}` in `y_S` ([OAI26, §3.1]): `1` (bit) and
`-(|S ∩ T| - 1)/2 ∈ {1/2, -1/2}` (complex); `half` stands for `1/2`. -/
def coefJ (κ : Kind) (half : R) (S T : Tri h) : R :=
  match κ with
  | .bit => 1
  | .complex => if inter S T = 0 then half else -half

/-- Side-injection value `Σ_{T nbr S} coefJ(S,T) · A_{ST}` added to `y_S`. -/
def sideVal (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) (S : Tri h) : M :=
  ∑ T : {T : Tri h // Nbr κ S T}, coefJ κ half S T.1 • s (.side j ι ⟨(S, T.1), T.2⟩)

/-- Gather value added to a central wire ([OAI26, §3.1]): `Σ_{T ∋ i} x_T` to `C_i`,
`Σ_T x_T` to `C_*`. -/
def gatherVal {κ : Kind} (j : Stage) (ι : Fix h) (s : Role κ h → M) : Center κ h → M
  | .inl i => ∑ T ∈ Finset.univ.filter (fun T : Tri h => i ∈ T.1), s (srcRole j ι T)
  | .inr _ => ∑ T : Tri h, s (srcRole j ι T)

/-- Scatter value added to `y_S` ([OAI26, §3.1]): `Σ_{i∈S} C_i` (bit), `(Σ_{i∈S} C_i − C_*)/2`
(complex). -/
def scatterVal (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) (S : Tri h) : M :=
  match κ, s with
  | .bit, s => ∑ i ∈ S.1, s (.center j ι (.inl i))
  | .complex, s => half • (∑ i ∈ S.1, s (.center j ι (.inl i)) - s (.center j ι (.inr ())))

/-- One schedule row of invocation `(j, ι)`: operation `op` with sign `ε`, reading saved inputs. -/
def rowUpd (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (op : Op) (ε : R) (s : Role κ h → M) :
    Role κ h → M := fun w =>
  match op, w with
  | .V, .side j' ι' p => if j' = j ∧ ι' = ι then s w + ε • s (srcRole j ι p.1.2) else s w
  | .G, .center j' ι' c => if j' = j ∧ ι' = ι then s w + ε • gatherVal j ι s c else s w
  | .J, w => match tgtTriple? j ι w with
      | some S => s w + ε • sideVal κ half j ι s S
      | none => s w
  | .R, w => match tgtTriple? j ι w with
      | some S => s w + ε • scatterVal κ half j ι s S
      | none => s w
  | _, w => s w

/-- One invocation: the eight rows of its schedule in time order. -/
def invocation (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) : Role κ h → M :=
  (List.finRange 8).foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : R) s) s

/-- The invocation of stage `j` containing a role, if any. -/
def invOf {κ : Kind} (j : Stage) : Role κ h → Option (Fix h)
  | .X a => some (a.fix j)
  | .Y a => some (a.fix j)
  | .side j' ι _ => if j' = j then some ι else none
  | .center j' ι _ => if j' = j then some ι else none

/-- Stage `j`: all `v²` invocations of the stage (they act on disjoint role sets). -/
def stageMap (κ : Kind) (half : R) (j : Stage) (s : Role κ h → M) : Role κ h → M := fun w =>
  match invOf j w with
  | some ι => invocation κ half j ι s w
  | none => s w

/-- The whole scalar network: forward stage 1 (`X → Y`), inverse stage 2 (`Y → X`), forward
stage 3 ([OAI26, §3.1, Lemma 5]). -/
def net (κ : Kind) (half : R) (s : Role κ h → M) : Role κ h → M :=
  stageMap κ half .three (stageMap κ half .two (stageMap κ half .one s))

/-! ### Contracts: [OAI26] Lemma 5 (stated as `Prop`s; proved in `Networks/Proofs/`)

Universe convention: the coefficient ring and the module of values range over `Type` (universe 0),
which contains every ring and array module used downstream (`ZMod 2`, `ℤ[i,1/2]`, `ℂ`, arrays). -/

/-- CONTRACT. [OAI26, §3.1, Lemma 5] (first sentence), bit network:
for arbitrary initial values of all auxiliary wires, one invocation changes each logical target
`y_S` to `y_S + x_S` and leaves every other value unchanged (at stage 2, with exchanged banks, this
is `X_S ← X_S − Y_S = X_S + Y_S` over `𝔽₂`). Stated for one `h` (it holds for every `h`) and every
`𝔽₂`-module `M`. -/
def Lemma5InvocationBitStmt (h : ℕ) : Prop :=
  ∀ {Md : Type} [AddCommGroup Md] [Module (ZMod 2) Md] (j : Stage) (ι : Fix h)
    (s : Role .bit h → Md) (w : Role .bit h),
    invocation .bit (0 : ZMod 2) j ι s w =
      match tgtTriple? j ι w with
      | some S => s w + s (srcRole j ι S)
      | none => s w

/-- CONTRACT. [OAI26, §3.1, Lemma 5], complex network: with `2·half = 1`,
for arbitrary auxiliary values a forward invocation (stages 1, 3) sends `y_S ↦ y_S + x_S`, the
inverse schedule at stage 2 sends `X_S ↦ X_S − Y_S`, and every other value is unchanged. -/
def Lemma5InvocationComplexStmt (h : ℕ) : Prop :=
  ∀ {Rg Md : Type} [CommRing Rg] [AddCommGroup Md] [Module Rg Md] (half : Rg), 2 * half = 1 →
    ∀ (j : Stage) (ι : Fix h) (s : Role .complex h → Md) (w : Role .complex h),
    invocation .complex half j ι s w =
      match tgtTriple? j ι w with
      | some S => s w + ((if j.isInverse then -1 else 1 : ℤ) : Rg) • s (srcRole j ι S)
      | none => s w

/-- CONTRACT (B1). [OAI26, §3.1, Lemma 5], bit network: the three stages send
`(X_a, Y_a) ↦ (Y_a, X_a)` (the exchange) and restore every auxiliary value, for arbitrary initial
auxiliary values; i.e. the scalar network is the role permutation `ρ`. -/
def Lemma5BitStmt (h : ℕ) : Prop :=
  ∀ {Md : Type} [AddCommGroup Md] [Module (ZMod 2) Md] (s : Role .bit h → Md) (w : Role .bit h),
    net .bit (0 : ZMod 2) s w.rho = s w

/-- CONTRACT (C1). [OAI26, §3.1, Lemma 5], complex network: with `2·half = 1` the three
stages send `(X_a, Y_a) ↦ (−Y_a, X_a)` and restore every auxiliary value, for arbitrary initial
auxiliary values. -/
def Lemma5ComplexStmt (h : ℕ) : Prop :=
  ∀ {Rg Md : Type} [CommRing Rg] [AddCommGroup Md] [Module Rg Md] (half : Rg), 2 * half = 1 →
    ∀ s : Role .complex h → Md,
    (∀ a : Addr h, net .complex half s (.Y a) = s (.X a)) ∧
    (∀ a : Addr h, net .complex half s (.X a) = -s (.Y a)) ∧
    (∀ w : Role .complex h, w.IsScratch → net .complex half s w = s w)

end SubNLogN.Math.Networks
