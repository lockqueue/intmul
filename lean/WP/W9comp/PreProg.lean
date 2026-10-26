import WP.W9comp.Shapes

/-!
# WP.W9comp.PreProg — the PRE node composite, its phase specs and cost arithmetic

The proofs `preNodeProg_spec` / `W9_preNode_of_phases_holds` are in `WP.W9comp.PreNode`.

`preNodeProg` is the composite program, parameterized by its phase sub-programs:

`P1 ; P2 ; push guard on TL ; P3 ; P4 ; P5 ; P7 ; P8 ; rewind TL → TR down to the guard`

* P3, P4 and P7 move the table head across the filter rows and the two twiddle tables. The guard,
  pushed before P3, lets the final rewind restore `TL` and `TR` exactly; it is needed because `TL`'s
  old content is arbitrary.
* `preNodeProg_spec`: if every phase program meets its contract body (`SpecP1` … `SpecP8`), then the
  composite meets `W9_preNode`'s body with constant `C1 + … + C8 + 6`.
* `W9_preNode_of_phases_holds`: the contract-level statement.

Values: the phase chain is `preNodeV` by `preNodeV_eq_phases` (`rfl`). The static-stride spread
equals the snapshot's under `SpreadStrideOK` (`w9UStatic_eq`). The phase hypotheses (shapes,
widths) come from `PreNodeOK`, `PreTablesW` and `Shapes.lean`.
-/

namespace WP.W9comp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## The phase contract bodies (verbatim from `Contracts.W9.Pre`) -/

def SpecP1 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (x : Array (ℤ × ℤ)) (σ : BLoc m → List Sym),
    PreDims h → PreCtx h σ → x.size = h.N → ArrW w x → MatW w (w9XRows h.t1 h.r x) →
    σ (.inl .W0) = blkE x.toList →
    Runs P σ (Function.update σ (.inl .W0) (matSyms (w9XRows h.t1 h.r x))) (fun _ => True)
      (C * preTransposeBound w h)

def SpecP2 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (xRows : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
    PreDims h → PreCtx h σ → xRows.size = h.t1 → (∀ row ∈ xRows.toList, row.size = h.r) →
    MatW w xRows →
    EntryW w (computableNyquistAltSumContiguous h.p_in h.pSub h.r (xRows.getD (h.t1 / 2) #[])) →
    σ (.inl .W0) = matSyms xRows →
    Runs P σ (Function.update σ (.inl .RET)
        ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
          (xRows.getD (h.t1 / 2) #[]))).reverse ++ σ (.inl .RET))) (fun _ => True)
      (C * altSumBound w h)

def SpecP3 (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restT : List Sym),
    PreDims h → PreCtx h σ → xRows.size = h.t1 → (∀ row ∈ xRows.toList, row.size = h.r) →
    MatW w xRows → (∀ j < h.t1, TapsW w (ft.getD j []) ∧ (ft.getD j []).length ≤ h.W) →
    MatW w (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows) →
    σ (.inl .W0) = matSyms xRows → σ (.inl .TR) = filterRowsSyms h.t1 ft ++ restT →
    Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
          (matSyms (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows)))
        (.inl .TR) restT) (.inl .TL) ((filterRowsSyms h.t1 ft).reverse ++ σ (.inl .TL)))
      (fun _ => True) (C * spreadBound Mul w h)

def SpecP4 (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (preTw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restT : List Sym),
    PreDims h → PreCtx h σ → U.size = h.t1 → (∀ row ∈ U.toList, row.size = h.r) → MatW w U →
    TwW w h.r preTw → MatW w (w9P h.pSub h.t1 h.r preTw U) →
    σ (.inl .W0) = matSyms U → σ (.inl .TR) = twSyms h.r preTw ++ restT →
    Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
          (matSyms (w9P h.pSub h.t1 h.r preTw U)))
        (.inl .TR) restT) (.inl .TL) ((twSyms h.r preTw).reverse ++ σ (.inl .TL)))
      (fun _ => True) (C * twistBound Mul w h)

def SpecP5 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (Pm : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
    PreDims h → PreCtx h σ → Pm.size = h.t1 → (∀ row ∈ Pm.toList, row.size = h.r) → MatW w Pm →
    MatW w (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm)) →
    σ (.inl .W0) = matSyms Pm →
    Runs P σ (Function.update σ (.inl .W0) (matSyms (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm))))
      (fun _ => True) (C * synBound w h)

def SpecP7 (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (postTw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restT : List Sym),
    PreDims h → PreCtx h σ → Q.size = h.t1 → (∀ row ∈ Q.toList, row.size = h.r) → MatW w Q →
    TwW w h.r postTw → MatW w (w9QPost h.pSub h.t1 h.r postTw Q) →
    σ (.inl .W0) = matSyms Q → σ (.inl .TR) = twSyms h.r postTw ++ restT →
    Runs P σ (Function.update (Function.update (Function.update σ (.inl .W0)
          (matSyms (w9QPost h.pSub h.t1 h.r postTw Q)))
        (.inl .TR) restT) (.inl .TL) ((twSyms h.r postTw).reverse ++ σ (.inl .TL)))
      (fun _ => True) (C * twistBound Mul w h)

def SpecP8 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PreHdr) (w : ℕ) (M : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
    PreCtx h σ → M.size = h.t1 → (∀ row ∈ M.toList, row.size = h.r) → MatW w M →
    σ (.inl .W0) = matSyms M →
    Runs P σ (Function.update σ (.inl .W0) (M.toList.flatMap nodeSyms)) (fun _ => True)
      (C * emitBound w h)

/-- `W9_preNode`'s body. -/
def SpecPreNode (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (h : PreHdr) (w : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restT : List Sym),
    PreDims h → PreCtx h σ → PreTablesW w h.m1 h.t1 h.r ft preTw postTw → x.size = h.N →
    PreNodeOK w h ft preTw postTw x →
    σ (.inl .W0) = blkE x.toList → σ (.inl .TR) = preBody h.t1 h.r ft preTw postTw ++ restT →
    Runs P σ (Function.update (Function.update σ (.inl .W0)
          ((preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList.flatMap nodeSyms))
        (.inl .RET)
        ((entrySyms (altNodeV h.p_in h.pSub h.t1 h.r x)).reverse ++ σ (.inl .RET)))
      (fun _ => True) (C * preNodeBound Mul w h)

/-! ## The composite program -/

/-- Registers of the PRE composite: one component per phase and the rewind register. -/
abbrev PreRegs (R1 R2 R3 R4 R5 R7 R8 : Type) : Type :=
  R1 × R2 × R3 × R4 × R5 × R7 × R8 × Option Sym

section Lenses

variable (R1 R2 R3 R4 R5 R7 R8 : Type)

def pl1 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R1 := Lens.fst _ _
def pl2 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R2 := lsnd (Lens.fst _ _)
def pl3 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R3 := lsnd (lsnd (Lens.fst _ _))
def pl4 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R4 := lsnd (lsnd (lsnd (Lens.fst _ _)))
def pl5 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R5 := lsnd (lsnd (lsnd (lsnd (Lens.fst _ _))))
def pl7 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R7 := lsnd (lsnd (lsnd (lsnd (lsnd (Lens.fst _ _)))))
def pl8 : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) R8 :=
  lsnd (lsnd (lsnd (lsnd (lsnd (lsnd (Lens.fst _ _))))))
def plg : Lens (PreRegs R1 R2 R3 R4 R5 R7 R8) (Option Sym) :=
  lsnd (lsnd (lsnd (lsnd (lsnd (lsnd (Lens.snd _ _))))))

end Lenses

/-- **The PRE node composite.** -/
def preNodeProg {m m1 m2 m3 m4 m5 m7 m8 : ℕ} {R1 R2 R3 R4 R5 R7 R8 : Type}
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (h7 : m7 ≤ m)
    (h8 : m8 ≤ m) (P1 : Prog (BLoc m1) (fun _ => Sym) R1) (P2 : Prog (BLoc m2) (fun _ => Sym) R2)
    (P3 : Prog (BLoc m3) (fun _ => Sym) R3) (P4 : Prog (BLoc m4) (fun _ => Sym) R4)
    (P5 : Prog (BLoc m5) (fun _ => Sym) R5) (P7 : Prog (BLoc m7) (fun _ => Sym) R7)
    (P8 : Prog (BLoc m8) (fun _ => Sym) R8) :
    Prog (BLoc m) (fun _ => Sym) (PreRegs R1 R2 R3 R4 R5 R7 R8) :=
  .seq (callB h1 (pl1 R1 R2 R3 R4 R5 R7 R8) P1) <|
  .seq (callB h2 (pl2 R1 R2 R3 R4 R5 R7 R8) P2) <|
  .seq (pushConst (.inl .TL) symGuard) <|
  .seq (callB h3 (pl3 R1 R2 R3 R4 R5 R7 R8) P3) <|
  .seq (callB h4 (pl4 R1 R2 R3 R4 R5 R7 R8) P4) <|
  .seq (callB h5 (pl5 R1 R2 R3 R4 R5 R7 R8) P5) <|
  .seq (callB h7 (pl7 R1 R2 R3 R4 R5 R7 R8) P7) <|
  .seq (callB h8 (pl8 R1 R2 R3 R4 R5 R7 R8) P8) <|
  (rewindTo (.inl .TL) (.inl .TR) symGuard).liftRegs (plg R1 R2 R3 R4 R5 R7 R8)

theorem preNodeProg_closed {m m1 m2 m3 m4 m5 m7 m8 : ℕ} {R1 R2 R3 R4 R5 R7 R8 : Type}
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (h7 : m7 ≤ m)
    (h8 : m8 ≤ m) {P1 : Prog (BLoc m1) (fun _ => Sym) R1} {P2 : Prog (BLoc m2) (fun _ => Sym) R2}
    {P3 : Prog (BLoc m3) (fun _ => Sym) R3} {P4 : Prog (BLoc m4) (fun _ => Sym) R4}
    {P5 : Prog (BLoc m5) (fun _ => Sym) R5} {P7 : Prog (BLoc m7) (fun _ => Sym) R7}
    {P8 : Prog (BLoc m8) (fun _ => Sym) R8} (c1 : P1.Closed) (c2 : P2.Closed) (c3 : P3.Closed)
    (c4 : P4.Closed) (c5 : P5.Closed) (c7 : P7.Closed) (c8 : P8.Closed) :
    (preNodeProg h1 h2 h3 h4 h5 h7 h8 P1 P2 P3 P4 P5 P7 P8).Closed :=
  closed_seq (closed_callB _ _ c1) <| closed_seq (closed_callB _ _ c2) <|
  closed_seq (closed_pushConst _ _) <| closed_seq (closed_callB _ _ c3) <|
  closed_seq (closed_callB _ _ c4) <| closed_seq (closed_callB _ _ c5) <|
  closed_seq (closed_callB _ _ c7) <| closed_seq (closed_callB _ _ c8) <| closed_rewind _ _ _ _

/-! ## Arithmetic and context lemmas -/

theorem preCtx_of_eq {m : ℕ} {h : PreHdr} {σ S : BLoc m → List Sym} (hC : PreCtx h σ)
    (e0 : S (.inl .C0) = σ (.inl .C0)) (e1 : S (.inl .C1) = σ (.inl .C1)) : PreCtx h S := by
  obtain ⟨⟨r0, h0⟩, ⟨r1, h1⟩⟩ := hC
  exact ⟨⟨r0, e0.trans h0⟩, ⟨r1, e1.trans h1⟩⟩

/-- The composite's cost is within `(ΣCᵢ + 6)·preNodeBound`. -/
theorem preCost_le (Mul : ℕ → ℕ) (w : ℕ) (h : PreHdr) (C1 C2 C3 C4 C5 C7 C8 L : ℕ)
    (hL : L ≤ preBodyBound w h) :
    C1 * preTransposeBound w h + (C2 * altSumBound w h + (1 + (C3 * spreadBound Mul w h +
      (C4 * twistBound Mul w h + (C5 * synBound w h + (C7 * twistBound Mul w h +
      (C8 * emitBound w h + (3 * L + 2)))))))) ≤
      (C1 + C2 + C3 + C4 + C5 + C7 + C8 + 6) * preNodeBound Mul w h := by
  have he : preNodeBound Mul w h = preTransposeBound w h + altSumBound w h +
      spreadBound Mul w h + 2 * twistBound Mul w h + synBound w h + emitBound w h +
      preBodyBound w h + eb w := rfl
  have hE : 4 ≤ eb w := by unfold eb; omega
  rw [he]
  generalize preTransposeBound w h = b1 at *
  generalize altSumBound w h = b2 at *
  generalize spreadBound Mul w h = b3 at *
  generalize twistBound Mul w h = b4 at *
  generalize synBound w h = b5 at *
  generalize emitBound w h = b8 at *
  generalize preBodyBound w h = bb at *
  generalize eb w = e at *
  generalize hC : C1 + C2 + C3 + C4 + C5 + C7 + C8 + 6 = C
  have k1 : C1 * b1 ≤ C * b1 := Nat.mul_le_mul_right _ (by omega)
  have k2 : C2 * b2 ≤ C * b2 := Nat.mul_le_mul_right _ (by omega)
  have k3 : C3 * b3 ≤ C * b3 := Nat.mul_le_mul_right _ (by omega)
  have k4 : C4 * b4 ≤ C * b4 := Nat.mul_le_mul_right _ (by omega)
  have k5 : C5 * b5 ≤ C * b5 := Nat.mul_le_mul_right _ (by omega)
  have k7 : C7 * b4 ≤ C * b4 := Nat.mul_le_mul_right _ (by omega)
  have k8 : C8 * b8 ≤ C * b8 := Nat.mul_le_mul_right _ (by omega)
  have kb : 6 * (bb + e) ≤ C * (bb + e) := Nat.mul_le_mul_right _ (by omega)
  have expand : C * (b1 + b2 + b3 + 2 * b4 + b5 + b8 + bb + e) =
      C * b1 + C * b2 + C * b3 + C * b4 + C * b4 + C * b5 + C * b8 + C * (bb + e) := by ring
  rw [expand]
  omega

#assert_std_axioms preNodeProg_closed preCtx_of_eq preCost_le

end WP.W9comp
