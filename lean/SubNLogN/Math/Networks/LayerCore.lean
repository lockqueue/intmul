import SubNLogN.Math.Networks.AppCLayer
import SubNLogN.Math.Networks.AppCModel

/-!
# Networks: shared definitions for the complex core (Lemma A.10 (`lem:transfer-phase`)) and the layer procedure (Proposition A.11 (`prop:prop14-param`))

* `groupBits`, `groupSel`, `cCoreVal`: `C^{⊗e}` on the selected bit `ρ` of the chunks `j0, …, j0+e−1`
  of a layer array (matching `SubNLogN/Machine/Contracts/CCore.lean`).
* `layerLayout A K D S`: the stream layout of a layer array: field `0` = prefix `[A]` (the row field),
  then `D` chunks of `K` binary fields (bit `t` from the least significant end of chunk `j` is field
  `1 + jK + (K−1−t)`), then the suffix `[S]` (field `DK + 1`). `encodeAddr`, `decodeAddr` translate
  addresses; arrays are translated by composition.
* `ProcK.AllStates Good d p c A`: every intermediate array of `ProcK.run d p c A` (inside nodes and
  children too) satisfies `Good` (the guard predicate used for finite-width machine realization).
-/

namespace SubNLogN.Math.Networks

open SubNLogN.Math.Walsh

/-- The selected bits `ρ` of the chunks `j0, …, j0+e−1` of an address. -/
def groupBits {A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D) (x : LayerAddr A K D S) :
    Fin e → Bool :=
  fun i => x.2.1 ⟨j0 + i, by have := i.isLt; omega⟩ ρ

/-- Overwrite the selected bits `ρ` of the chunks `j0, …, j0+e−1` by `bs`. -/
def groupSel {A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (x : LayerAddr A K D S) (bs : Fin e → Bool) :
    LayerAddr A K D S :=
  (x.1, fun j => if h : j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + e then
      Function.update (x.2.1 j) ρ (bs ⟨(j : ℕ) - j0, by omega⟩) else x.2.1 j, x.2.2)

/-- `C^{⊗e}` on the selected bits `ρ` of the chunks `j0, …, j0+e−1`, identically on every coefficient. -/
noncomputable def cCoreVal {r A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) : RArr (LayerAddr A K D S) r :=
  fun x k => CD e (fun bs => z (groupSel ρ j0 e x bs) k) (groupBits ρ j0 e h x)

/-- The stream layout of a layer array. -/
def layerLayout (A K D S : ℕ) : Model.Layout where
  n := D * K + 2
  r := fun i => if i.val = 0 then A else if i.val ≤ D * K then 2 else S

/-- Address translation `LayerAddr → layerLayout.Addr`. -/
def encodeAddr {A K D S : ℕ} (x : LayerAddr A K D S) : (layerLayout A K D S).Addr := fun i =>
  if h0 : i.val = 0 then ⟨x.1.val, by simp [layerLayout, h0]⟩
  else if h1 : i.val ≤ D * K then
    ⟨if hK : 0 < K then
        (if x.2.1 ⟨(i.val - 1) / K, by
            have : (i.val - 1) / K < D := Nat.div_lt_of_lt_mul (by
              have := Nat.mul_comm D K; omega)
            exact this⟩ ⟨K - 1 - (i.val - 1) % K, by omega⟩ then 1 else 0)
      else 0, by
        simp only [layerLayout, h0, h1, if_false, if_true]
        split_ifs <;> omega⟩
  else ⟨x.2.2.val, by simp [layerLayout, h0, h1]⟩

/-- Address translation `layerLayout.Addr → LayerAddr`. -/
def decodeAddr {A K D S : ℕ} (y : (layerLayout A K D S).Addr) : LayerAddr A K D S :=
  (⟨(y ⟨0, by simp [layerLayout]⟩).val, by
      have := (y ⟨0, by simp [layerLayout]⟩).isLt; simpa [layerLayout] using this⟩,
   fun j t => (y ⟨1 + j.val * K + (K - 1 - t.val), by
      have hj := j.isLt; have ht := t.isLt
      have : j.val * K + K ≤ D * K := by nlinarith
      simp only [layerLayout]; omega⟩).val = 1,
   ⟨(y ⟨D * K + 1, by simp [layerLayout]⟩).val, by
      have := (y ⟨D * K + 1, by simp [layerLayout]⟩).isLt; simpa [layerLayout] using this⟩)

/-- Arrays: `encode z = z ∘ decodeAddr`, `decode y = y ∘ encodeAddr`. -/
def encodeArr {A K D S r : ℕ} (z : RArr (LayerAddr A K D S) r) : (layerLayout A K D S).Addr → Fin r → ℂ :=
  fun y => z (decodeAddr y)

/-- Arrays back to `LayerAddr`. -/
def decodeArr {A K D S r : ℕ} (y : (layerLayout A K D S).Addr → Fin r → ℂ) : RArr (LayerAddr A K D S) r :=
  fun x => y (encodeAddr x)

/-- CONTRACT (layout round trip). `decodeAddr ∘ encodeAddr = id`, so `decodeArr ∘ encodeArr = id`. -/
def DecodeEncodeAddrStmt : Prop :=
  ∀ (A K D S : ℕ) (x : LayerAddr A K D S), decodeAddr (encodeAddr x) = x

end SubNLogN.Math.Networks

namespace SubNLogN.Math.Networks.Model

/-- Every intermediate array of a role operation's run satisfies `Good`. -/
def RoleOp.allStates {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β))
    (call : Child → RowClass L → (L.Addr → β) → Prop) (Good : (L.Addr → β) → Prop)
    (c : RowClass L) (hW : 0 < W) : RoleOp L β W Child → (L.Addr → β) → Prop
  | .call k ch, A => call ch (c.sub W hW k) A
  | o, A => Good (o.run crun c hW A)

/-- Every intermediate array of an operation's run satisfies `Good`. -/
def Op.allStates {L : Layout} {β : Type} {Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β))
    (call : Child → RowClass L → (L.Addr → β) → Prop) (Good : (L.Addr → β) → Prop)
    (c : RowClass L) : Op L β Child → (L.Addr → β) → Prop
  | .prim s, A => Good (s.runIn c A)
  | .node _ hW ops, A => ∀ i : Fin ops.length,
      (ops.get i).allStates crun call Good c hW
        ((ops.take i.val).foldl (fun A o => o.run crun c hW A) A)

/-- **Guard predicate on runs**: `Good` holds for the input and for every intermediate array of
`ProcK.run d p c A`, inside nodes and children included. -/
def ProcK.AllStates {L : Layout} {β : Type} (Good : (L.Addr → β) → Prop) :
    (d : ℕ) → ProcK L β d → RowClass L → (L.Addr → β) → Prop
  | 0, p, c, A => Good A ∧ ∀ i : Fin (@id (List (Step L β)) p).length,
      Good (((@id (List (Step L β)) p).take (i.val + 1)).foldl (fun A s => Step.runIn c s A) A)
  | d + 1, p, c, A => Good A ∧ ∀ i : Fin (@id (List (Op L β (ProcK L β d))) p).length,
      ((@id (List (Op L β (ProcK L β d))) p).get i).allStates (ProcK.run d) (ProcK.AllStates Good d)
        Good c (((@id (List (Op L β (ProcK L β d))) p).take i.val).foldl
          (fun A o => Op.run (ProcK.run d) c o A) A)

end SubNLogN.Math.Networks.Model
