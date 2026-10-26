import SubNLogN.Math.Networks.Scalar
import SubNLogN.Math.Networks.PhaseFrames
import SubNLogN.Math.Networks.Bruhat

/-!
# Networks, part 9: framed execution, the frame invariant (5) ([OAI26, §3.2, (5)]) and the array corollaries

The physical execution of a network on wire arrays ([OAI26, §3.2, (5)]; Proposition A.7 (`prop:transfer11`)):
before every gate, each wire it touches is transformed by the operator of its incoming edge; at the
end each wire is transformed by its edge into the sink; gates act pointwise (they are the scalar rows
of `Scalar.lean`, applied in the module of arrays). With edge operators `D_v ∘ D_u⁻¹` the network
implements `D_out ∘ S_Ω ∘ D_in⁻¹` (invariant (5), [OAI26, §3.2, (5)]); with the bit frames `D_v = Φ_{M_v}` every role
undergoes the shear `H ← H + D` (the corollary consumed by Proposition A.7 (`prop:transfer11`)).
-/

namespace SubNLogN.Math.Networks

variable {h : ℕ}

/-- Stage of a gate. -/
def Gate.stage : Gate h → Stage
  | .side j _ _ _ => j
  | .center j _ _ => j

/-- Invocation of a gate. -/
def Gate.inv : Gate h → Fix h
  | .side _ ι _ _ => ι
  | .center _ ι _ => ι

/-- Time of a gate. -/
def Gate.time : Gate h → Fin 8
  | .side _ _ r _ => r
  | .center _ _ r => r

/-- The gate touching `w` at stage `j`, invocation `ι`, time `r`, if any. -/
def gateAt {κ : Kind} (j : Stage) (ι : Fix h) (r : Fin 8) (w : Role κ h) : Option (Gate h) :=
  (touch w).find? (fun g => g.stage = j ∧ g.inv = ι ∧ g.time = r)

open Classical in
/-- The edge of `w` entering vertex `v`, if any. -/
noncomputable def edgeInto {κ : Kind} (w : Role κ h) (v : Vertex κ h) :
    Option (Vertex κ h × Vertex κ h) :=
  (edges w).find? (fun e => e.2 = v)

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- An edge-operator assignment: the map applied to wire `w` along its edge `e`. -/
abbrev EdgeOps (κ : Kind) (h : ℕ) (A : Type*) := Role κ h → Vertex κ h × Vertex κ h → A → A

/-- Apply the incoming edge operators of the wires touched at `(j, ι, r)`. -/
noncomputable def preEdges {κ : Kind} (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (s : Role κ h → A) : Role κ h → A := fun w =>
  match gateAt j ι r w with
  | some g => match edgeInto w (.gate g) with
    | some e => E w e (s w)
    | none => s w
  | none => s w

/-- One framed invocation: for each time `r`, incoming edge operators, then the scalar row. -/
noncomputable def framedInvocation (κ : Kind) (half : R) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h)
    (s : Role κ h → A) : Role κ h → A :=
  (List.finRange 8).foldl
    (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : R) (preEdges E j ι r s)) s

/-- One framed stage (all invocations; disjoint role sets). -/
noncomputable def framedStage (κ : Kind) (half : R) (E : EdgeOps κ h A) (j : Stage)
    (s : Role κ h → A) : Role κ h → A := fun w =>
  match invOf j w with
  | some ι => framedInvocation κ half E j ι s w
  | none => s w

/-- The framed network: three framed stages, then every wire's edge into its sink. -/
noncomputable def framedNet (κ : Kind) (half : R) (E : EdgeOps κ h A) (s : Role κ h → A) :
    Role κ h → A := fun w =>
  let t := framedStage κ half E .three (framedStage κ half E .two (framedStage κ half E .one s))
  match edgeInto w (.sink w) with
  | some e => E w e (t w)
  | none => t w

/-- CONTRACT. Frame invariant (5) ([OAI26, §3.2, (5)]; Appendix D.2, Proposition D.3 (`oai:networks`)): if every edge `u → v`
applies `D_v ∘ D_u⁻¹` for invertible `R`-linear frames `D`, the framed network equals
`D_out ∘ S_Ω ∘ D_in⁻¹`: the value on wire `w` is `D_{sink w}` of the scalar network applied to the
logical inputs `D_{source}⁻¹(s)`. No physical preprocessing of the input is needed. Holds for every
`h`, both networks. -/
def FrameInvariantStmt (h : ℕ) : Prop :=
  ∀ (κ : Kind) {Rg Ar : Type} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar] (half : Rg)
    (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar)) (s : Role κ h → Ar) (w : Role κ h),
    framedNet κ half (fun _ e => fun x => D e.2 ((D e.1).symm x)) s w =
      D (.sink w) (net κ half (fun w' => (D (.source w')).symm (s w')) w)

/-! ### The bit-network array corollary -/

/-- Reduction mod `Q` of a rational with denominator prime to `Q`. -/
def ratMod (Q : ℕ) (r : ℚ) : ZMod Q := (r.num : ZMod Q) * ((r.den : ZMod Q))⁻¹

/-- Two address chunks `H, D ∈ (ℤ/Q)^m` (coordinates indexed by the cube) and spectators `σ`. -/
abbrev ChunkAddr (h Q : ℕ) (σ : Type*) := (Cube h → ZMod Q) × (Cube h → ZMod Q) × σ

/-- The matrix of the bit frame at a vertex. -/
noncomputable def matB (v : Vertex .bit h) : Matrix (Cube h) (Cube h) ℚ := LinearMap.toMatrix' (frameB v)

/-- The address shear `Φ_M` on arrays: the entry at `(H, D)` moves to `(H + M D, D)`, i.e.
`(Φ_M f)(H, D, σ) = f(H − M D, D, σ)` ([OAI26, §3.4, Prop. 7]). -/
def shearArr {σ M : Type*} (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) (f : ChunkAddr h Q σ → M) :
    ChunkAddr h Q σ → M :=
  fun x => f (x.1 - (Mx.map (ratMod Q)).mulVec x.2.1, x.2.1, x.2.2)

/-- Physical edge operators of the bit network: `Φ_{A_e}`, `A_e = M_head − M_tail`. -/
noncomputable def bitEdgeOps {σ M : Type*} (Q : ℕ) : EdgeOps .bit h (ChunkAddr h Q σ → M) :=
  fun _ e f => shearArr Q (matB e.2 - matB e.1) f

/-- CONTRACT (B3, array corollary). [OAI26, §3.4, Prop. 7]; Proposition A.7 (`prop:transfer11`).
At `h = 100`, for a prime `q` avoiding the denominators of all frame matrices and `Q = q^b`: running
the bit network with the physical edge operators `Φ_{A_e}` and pointwise XOR gates, on arbitrary
arrays (scratch included), output role `ρ(w)` holds input role `w` sheared by `H ← H + D`. -/
def BitArrayCorollaryStmt : Prop :=
  ∀ {σ Md : Type} [AddCommGroup Md] [Module (ZMod 2) Md] (q b : ℕ), q.Prime →
    (∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j)) →
    ∀ (s : Role .bit 100 → (ChunkAddr 100 (q ^ b) σ → Md)) (w : Role .bit 100)
      (x : ChunkAddr 100 (q ^ b) σ),
    framedNet .bit (0 : ZMod 2) (bitEdgeOps (q ^ b)) s w.rho x = s w (x.1 - x.2.1, x.2.1, x.2.2)

end SubNLogN.Math.Networks
