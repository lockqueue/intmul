import WP.W9c.RowKitInst
import WP.W9c.RowCostDefs
import WP.W9c.RowValue

/-!
# WP.W9c.RowMain — **`W9_spreadRow` from its parts**

* `ht_rowProg`: phases A–D chained on the row host `Loc 12 40` (cost `costA + costB + costC + costD`).
* `eLB`: the host's named stacks in `LB` order (`S W0 TL TR RET RQ C0 C1 C2 C3 OA OB`), scratch
  `j ↦ j`; a bijection `Loc 12 40 ≃ BLoc 40`, so `Runs.embed` gives the exact contract frame.
* `W9_spreadRow_of_parts`: instances from the contracts (`exists_inst`), one common constant
  (`Spec*.mono`), the kit (`mkRKit`, `mkPKit`/`passInst`), the value (`rowCells_eq_spread1`,
  `spreadRow_toList`) and the cost obligation `RowCostLe`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-! ## Phases A–D -/

theorem ht_rowProg {σ : Type} (K : RKit σ) {Mul : ℕ → ℕ} {C : ℕ} (hK : RKitOK Mul K C)
    (hRC : RowCOK) (hg1 : GluePackW) (hg2 : GlueDigits) (hg3 : GlueEmit) (hg4 : GlueCells)
    (σ0 : RL → List Sym) (h : PreHdr) (w : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ))
    (restT r0 r1 : List Sym) (hdims : PreDims h)
    (hC0 : σ0 rC0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0)
    (hC1 : σ0 rC1 = hdrSyms [h.p_in] ++ r1) (hsize : row.size = h.r) (harr : ArrW w row)
    (htaps : TapsW w taps) (hlen : taps.length ≤ h.W) (hW0 : σ0 rW0 = blkE row.toList)
    (hTR : σ0 rTR = filterRowSyms taps ++ restT) :
    HT [] σ0 (rowProg K) (stF σ0 h.pSub h.m1 h.r h.p_in taps restT row.toList)
      (costA C h.pSub h.m1 h.t1 h.r h.p_in + costB C h.pSub h.m1 h.r w taps row.toList +
        costC C Mul h.pSub h.m1 h.r h.p_in w taps row.toList +
        costD C h.pSub h.m1 h.r h.p_in taps) := by
  have hr : h.r = 2 ^ natLog2Fuel h.r h.r := hdims.2.1
  have hr0 : 0 < h.r := by rw [hr]; exact Nat.two_pow_pos _
  obtain ⟨TA, hA, hTA⟩ := ht_rowA (ρ := []) K hK σ0 h.pSub h.m1 h.t1 h.r h.p_in r0 r1 hC0 hC1 hr
  obtain ⟨TB, hB, hTB⟩ := ht_rowB (ρ := []) K hK σ0 h.pSub h.m1 h.r h.p_in w taps restT
    row.toList hTR hW0 hlen htaps
  obtain ⟨TC, hCC, hTC⟩ := hRC hg1 hg2 hg3 hg4 K Mul C [] hK σ0 h.pSub h.m1 h.r h.p_in w taps
    restT row.toList hr hr0 (by simp [hsize]) (fun z hz => harr z hz) htaps hlen
  have hD := ht_rowD (ρ := []) K hK σ0 h.pSub h.m1 h.r h.p_in taps restT row.toList
  refine (HT.seq hA (HT.seq hB (HT.seq hCC hD))).mono ?_
  simp only [costA, costB]
  omega

/-! ## The host's stacks as layout-B stacks -/

/-- Layout-B name of the row host's `i`-th named stack. -/
def lbOf (i : Fin 12) : LB :=
  match i with
  | ⟨0, _⟩ => .S
  | ⟨1, _⟩ => .W0
  | ⟨2, _⟩ => .TL
  | ⟨3, _⟩ => .TR
  | ⟨4, _⟩ => .RET
  | ⟨5, _⟩ => .RQ
  | ⟨6, _⟩ => .C0
  | ⟨7, _⟩ => .C1
  | ⟨8, _⟩ => .C2
  | ⟨9, _⟩ => .C3
  | ⟨10, _⟩ => .OA
  | _ => .OB

/-- The row host inside `BLoc 40`. -/
def eLB : RL → BLoc 40 := Sum.map lbOf id

/-- **The `W9_spreadRow` witness program**: the row driver over the kit `mkRKit` built from the
kernel instances (pass instance `passInst pk up wn ce mu cp dr iz dc`), embedded by `eLB`.
`W9_spreadRow_of_parts` uses literally `rowMainProg` applied to the `exists_inst` instances. -/
def rowMainProg (hd : Inst 9 24 Unit) (tp : Inst 4 24 Unit) (sp zp : Inst 3 24 Unit)
    (pk : Inst 6 24 Unit) (up wn : Inst 4 24 Unit) (ce : Inst 3 24 Unit) (mu : Inst 3 8 Unit)
    (cp : Inst 2 4 Unit) (dr : Inst 1 4 Unit) (iz : Inst 1 4 Bool) (ic dc : Inst 1 4 Unit)
    (ad sb sa : Inst 3 4 Unit) :
    Prog (BLoc 40) (fun _ => Sym)
      (RSig hd tp sp zp pk (passInst pk up wn ce mu cp dr iz dc) cp dr iz ic dc ad sb sa) :=
  (rowProg (mkRKit hd tp sp zp pk (passInst pk up wn ce mu cp dr iz dc) cp dr iz ic dc ad sb
    sa)).mapStk eLB

theorem lbOf_injective : Function.Injective lbOf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [lbOf] at h)

theorem eLB_injective : Function.Injective eLB := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [eLB, Sum.map_inl, Sum.map_inr,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, id] at h
  · rw [lbOf_injective h]
  · rw [h]

theorem eLB_surjective : Function.Surjective eLB := by
  intro k
  rcases k with k | j
  · cases k
    · exact ⟨.inl 0, rfl⟩
    · exact ⟨.inl 1, rfl⟩
    · exact ⟨.inl 2, rfl⟩
    · exact ⟨.inl 3, rfl⟩
    · exact ⟨.inl 4, rfl⟩
    · exact ⟨.inl 5, rfl⟩
    · exact ⟨.inl 6, rfl⟩
    · exact ⟨.inl 7, rfl⟩
    · exact ⟨.inl 8, rfl⟩
    · exact ⟨.inl 9, rfl⟩
    · exact ⟨.inl 10, rfl⟩
    · exact ⟨.inl 11, rfl⟩
  · exact ⟨.inr j, rfl⟩

#assert_std_axioms ht_rowProg lbOf_injective eLB_injective eLB_surjective

end WP.W9c
