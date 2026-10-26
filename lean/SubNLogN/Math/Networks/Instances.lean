import SubNLogN.Math.Networks.Basic

/-!
# Networks: finiteness instances for gates and vertices

`Fintype` structures on `Gate h` and `Vertex κ h` (via explicit equivalences with sums of finite
types). They are needed to collect the finitely many entries of all frame matrices when choosing
the prime radix (`ExistsOddPrimeAvoidingStmt`); no statement depends on the particular instance.
-/

namespace SubNLogN.Math.Networks

/-- Gates as a sum of finite types. -/
def Gate.equivSum (h : ℕ) :
    Gate h ≃ (Stage × Fix h × Fin 8 × Tri h) ⊕ (Stage × Fix h × Fin 8) where
  toFun
    | .side j ι r t => .inl (j, ι, r, t)
    | .center j ι r => .inr (j, ι, r)
  invFun
    | .inl (j, ι, r, t) => .side j ι r t
    | .inr (j, ι, r) => .center j ι r
  left_inv g := by cases g <;> rfl
  right_inv x := by rcases x with ⟨j, ι, r, t⟩ | ⟨j, ι, r⟩ <;> rfl

instance (h : ℕ) : Fintype (Gate h) := Fintype.ofEquiv _ (Gate.equivSum h).symm

/-- Vertices as a sum of finite types. -/
def Vertex.equivSum (κ : Kind) (h : ℕ) :
    Vertex κ h ≃ Role κ h ⊕ Gate h ⊕ Role κ h where
  toFun
    | .source w => .inl w
    | .gate g => .inr (.inl g)
    | .sink w => .inr (.inr w)
  invFun
    | .inl w => .source w
    | .inr (.inl g) => .gate g
    | .inr (.inr w) => .sink w
  left_inv v := by cases v <;> rfl
  right_inv x := by rcases x with w | g | w <;> rfl

instance (κ : Kind) (h : ℕ) : Fintype (Vertex κ h) := Fintype.ofEquiv _ (Vertex.equivSum κ h).symm

end SubNLogN.Math.Networks
