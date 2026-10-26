import WP.W9comp.Shapes

/-!
# WP.W9comp.PostProg — the POST node composite, its phase specs and cost arithmetic

The proofs `postNodeProg_spec` / `W9_postNode_of_phases_holds` are in `WP.W9comp.PostNode`.

`postNodeProg` is the composite program, parameterized by its phase sub-programs:

`Q2 ; Q3 ; push guard on TL ; Q5 ; Q6 ; rewind TL → TR down to the guard`

* Q5 (`W9_columns`) moves the table head across the POST body and pops `alt` from RQ. The guard,
  pushed before Q5, lets the final rewind restore `TL` and `TR` exactly.
* `SpecQ2` … `SpecQ6` are the phase contract bodies (verbatim from `Contracts.W9.Post`);
  `SpecPostNode` is `W9_postNode`'s body.
* `postCost_le`: the composite's cost is within `(C2 + C3 + 2·C5 + C6 + 6)·postNodeBound`. The
  factor 2 on `C5` absorbs the `eb H` term of `W9_columns`' cost (`eb H ≤ N·eb H`, `N ≥ 1`).
-/

namespace WP.W9comp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## The phase contract bodies (verbatim from `Contracts.W9.Post`) -/

def SpecQ2 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PostHdr) (w : ℕ) (qHat : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
    PostDims h → PostCtx h σ → qHat.size = h.t1 → (∀ row ∈ qHat.toList, row.size = h.r) →
    MatW w qHat → ArrW w (w9QHatT h.t1 h.r qHat) →
    σ (.inl .W0) = matSyms qHat →
    Runs P σ (Function.update σ (.inl .W0) (blkE (w9QHatT h.t1 h.r qHat).toList))
      (fun _ => True) (C * postTransposeBound w h)

def SpecQ3 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PostHdr) (w : ℕ) (qHatT : Array (ℤ × ℤ)) (σ : BLoc m → List Sym),
    PostDims h → PostCtx h σ → qHatT.size = h.N → ArrW w qHatT →
    MatW w (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT)) →
    σ (.inl .W0) = blkE qHatT.toList →
    Runs P σ (Function.update σ (.inl .W0)
        (matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT))))
      (fun _ => True) (C * routesBound w h)

def SpecQ5 (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ) (Y : Array (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restT rq : List Sym),
    PostDims h → PostCtx h σ → PostTablesW h.H h.r c0T c1T → Y.size = h.r →
    (∀ col ∈ Y.toList, col.size = h.t1) →
    (∀ u2 < h.r, ColumnOK h.pSub h.t1 h.r u2 (read1D c0T u2) (read1D c1T u2) (Y.getD u2 #[]) alt) →
    MatW h.H (w9ZBarrett h.pSub h.t1 h.r c0T c1T alt Y) →
    σ (.inl .W0) = matSyms Y → σ (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT →
    σ (.inl .RQ) = entrySyms alt ++ rq →
    Runs P σ (Function.update (Function.update (Function.update (Function.update σ (.inl .W0)
          (matSyms (w9ZBarrett h.pSub h.t1 h.r c0T c1T alt Y)))
        (.inl .TR) restT) (.inl .TL) ((postBody h.pSub h.r c0T c1T).reverse ++ σ (.inl .TL)))
        (.inl .RQ) rq)
      (fun _ => True) (C * (h.r * columnBound Mul h + h.N * eb h.H + eb h.H + 1))

def SpecQ6 (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (h : PostHdr) (w : ℕ) (Zc : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym),
    PostDims h → PostCtx h σ → Zc.size = h.r → (∀ col ∈ Zc.toList, col.size = h.t1) →
    MatW w Zc → ArrW w (w9Out h.p h.pSub h.t1 h.r Zc) →
    σ (.inl .W0) = matSyms Zc →
    Runs P σ (Function.update σ (.inl .W0) (nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc)))
      (fun _ => True) (C * outBound w h)

/-- `W9_postNode`'s body. -/
def SpecPostNode (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (h : PostHdr) (w : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (qHat : Array (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restT rq : List Sym),
    PostDims h → PostCtx h σ → PostTablesW h.H h.r c0T c1T → qHat.size = h.t1 →
    (∀ row ∈ qHat.toList, row.size = h.r) → PostNodeOK w h c0T c1T alt qHat →
    σ (.inl .W0) = matSyms qHat → σ (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT →
    σ (.inl .RQ) = entrySyms alt ++ rq →
    Runs P σ (Function.update (Function.update σ (.inl .W0)
          (nodeSyms (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild alt qHat)))
        (.inl .RQ) rq)
      (fun _ => True) (C * postNodeBound Mul w h)

/-! ## The composite program -/

/-- Registers of the POST composite: one component per phase and the rewind register. -/
abbrev PostRegs (R2 R3 R5 R6 : Type) : Type := R2 × R3 × R5 × R6 × Option Sym

section Lenses

variable (R2 R3 R5 R6 : Type)

def ql2 : Lens (PostRegs R2 R3 R5 R6) R2 := Lens.fst _ _
def ql3 : Lens (PostRegs R2 R3 R5 R6) R3 := lsnd (Lens.fst _ _)
def ql5 : Lens (PostRegs R2 R3 R5 R6) R5 := lsnd (lsnd (Lens.fst _ _))
def ql6 : Lens (PostRegs R2 R3 R5 R6) R6 := lsnd (lsnd (lsnd (Lens.fst _ _)))
def qlg : Lens (PostRegs R2 R3 R5 R6) (Option Sym) := lsnd (lsnd (lsnd (Lens.snd _ _)))

end Lenses

/-- **The POST node composite.** -/
def postNodeProg {m m2 m3 m5 m6 : ℕ} {R2 R3 R5 R6 : Type}
    (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h5 : m5 ≤ m) (h6 : m6 ≤ m)
    (Q2 : Prog (BLoc m2) (fun _ => Sym) R2) (Q3 : Prog (BLoc m3) (fun _ => Sym) R3)
    (Q5 : Prog (BLoc m5) (fun _ => Sym) R5) (Q6 : Prog (BLoc m6) (fun _ => Sym) R6) :
    Prog (BLoc m) (fun _ => Sym) (PostRegs R2 R3 R5 R6) :=
  .seq (callB h2 (ql2 R2 R3 R5 R6) Q2) <|
  .seq (callB h3 (ql3 R2 R3 R5 R6) Q3) <|
  .seq (pushConst (.inl .TL) symGuard) <|
  .seq (callB h5 (ql5 R2 R3 R5 R6) Q5) <|
  .seq (callB h6 (ql6 R2 R3 R5 R6) Q6) <|
  (rewindTo (.inl .TL) (.inl .TR) symGuard).liftRegs (qlg R2 R3 R5 R6)

theorem postNodeProg_closed {m m2 m3 m5 m6 : ℕ} {R2 R3 R5 R6 : Type}
    (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h5 : m5 ≤ m) (h6 : m6 ≤ m)
    {Q2 : Prog (BLoc m2) (fun _ => Sym) R2} {Q3 : Prog (BLoc m3) (fun _ => Sym) R3}
    {Q5 : Prog (BLoc m5) (fun _ => Sym) R5} {Q6 : Prog (BLoc m6) (fun _ => Sym) R6}
    (c2 : Q2.Closed) (c3 : Q3.Closed) (c5 : Q5.Closed) (c6 : Q6.Closed) :
    (postNodeProg h2 h3 h5 h6 Q2 Q3 Q5 Q6).Closed :=
  closed_seq (closed_callB _ _ c2) <| closed_seq (closed_callB _ _ c3) <|
  closed_seq (closed_pushConst _ _) <| closed_seq (closed_callB _ _ c5) <|
  closed_seq (closed_callB _ _ c6) <| closed_rewind _ _ _ _

/-! ## Arithmetic and context lemmas -/

theorem postCtx_of_eq {m : ℕ} {h : PostHdr} {σ S : BLoc m → List Sym} (hC : PostCtx h σ)
    (e0 : S (.inl .C0) = σ (.inl .C0)) : PostCtx h S := by
  obtain ⟨r0, h0⟩ := hC
  exact ⟨r0, e0.trans h0⟩

/-- The composite's cost is within `(C2 + C3 + 2·C5 + C6 + 6)·postNodeBound`. -/
theorem postCost_le (Mul : ℕ → ℕ) (w : ℕ) (h : PostHdr) (C2 C3 C5 C6 L : ℕ)
    (hL : L ≤ postBodyBound h) (hN : 1 ≤ h.N) :
    C2 * postTransposeBound w h + (C3 * routesBound w h + (1 + (C5 * (h.r * columnBound Mul h +
      h.N * eb h.H + eb h.H + 1) + (C6 * outBound w h + (3 * L + 2))))) ≤
      (C2 + C3 + 2 * C5 + C6 + 6) * postNodeBound Mul w h := by
  have he : postNodeBound Mul w h = postTransposeBound w h + routesBound w h +
      (h.r * columnBound Mul h + h.N * eb h.H + 1) + outBound w h + postBodyBound h + eb w := rfl
  have hE : 4 ≤ eb w := by unfold eb; omega
  have hNE : eb h.H ≤ h.N * eb h.H := Nat.le_mul_of_pos_left _ hN
  rw [he]
  generalize postTransposeBound w h = b2 at *
  generalize routesBound w h = b3 at *
  generalize h.r * columnBound Mul h = rc at *
  generalize h.N * eb h.H = ne at *
  generalize eb h.H = eh at *
  generalize outBound w h = b6 at *
  generalize postBodyBound h = bb at *
  generalize eb w = e at *
  generalize hC : C2 + C3 + 2 * C5 + C6 + 6 = C
  have k2 : C2 * b2 ≤ C * b2 := Nat.mul_le_mul_right _ (by omega)
  have k3 : C3 * b3 ≤ C * b3 := Nat.mul_le_mul_right _ (by omega)
  have k5 : C5 * (rc + ne + eh + 1) ≤ C5 * (2 * (rc + ne + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have k5e : C5 * (2 * (rc + ne + 1)) = (2 * C5) * (rc + ne + 1) := by ring
  have k5' : (2 * C5) * (rc + ne + 1) ≤ C * (rc + ne + 1) := Nat.mul_le_mul_right _ (by omega)
  have k6 : C6 * b6 ≤ C * b6 := Nat.mul_le_mul_right _ (by omega)
  have kb : 6 * (bb + e) ≤ C * (bb + e) := Nat.mul_le_mul_right _ (by omega)
  have expand : C * (b2 + b3 + (rc + ne + 1) + b6 + bb + e) =
      C * b2 + C * b3 + C * (rc + ne + 1) + C * b6 + C * (bb + e) := by ring
  rw [expand]
  omega

#assert_std_axioms postNodeProg_closed postCtx_of_eq postCost_le

end WP.W9comp
