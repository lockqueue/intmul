import WP.W9g.TopA

/-!
# WP.W9g.TopB — data passes and cleanup of the leaf kernel

* `undirshProg`: drop the rescale parameters `SH`, `DIR` (and their marks).
* `drainProg`, `delimProg`: `W0 = ⟦x⟧` (the whole stack) ↦ `⟦x⟧ $D`, through `E`.
* `outCell`, `rescLoop`: F4. Every entry of the FFT output on `R` (reversed, above `$D`) is
  rescaled (`rescK`, here `q → p`) and pushed onto `W0`, so `W0` receives the output in order.
* `cleanupProg`: pop the guard, the counters, the parameters and every mark of the setup.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- Entry rescale by direction and amount. -/
def rescE (left : Bool) (d : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := (rescLD left d z.1, rescLD left d z.2)

/-- The temporaries that carry a `mark` from the setup. -/
def marksL : List Stk := [.Ra, .Rc, .Rd, .Na, .Nc, .Nd, .Ne, .Nf, .X1, .X2, .X5, .X7, .X9, .X11, .X12]

section Prog

variable {τ : Type}

/-- Drop the rescale parameters. -/
def undirshProg : MProg Stk τ :=
  (.seq (lm (WP.W6a.dropBits .SH)) (.seq (lm (popR .SH)) (.seq (lm (popR .DIR)) (lm (popR .DIR)))))

/-- Move every entry of `W0` (the whole stack) onto `E`. -/
def drainProg : MProg Stk τ := whileTop .W0 (fun o => o.isSome) (lm (emove .W0 .E .T1))

/-- `W0 = ⟦x⟧` ↦ `⟦x⟧ $D`. -/
def delimProg : MProg Stk τ :=
  .seq (lm (pushC .E .mark)) (.seq drainProg (.seq (lm (pushC .W0 symD))
    (.seq (moveAll .E .W0 .T1 .mark) (lm (popR .E)))))

/-- Undo the setup. -/
def cleanupProg : MProg Stk τ :=
  (.seq (lm (popR .TL)) (.seq (lm (WP.W6a.dropBits .CS)) (.seq (lm (popR .CS)) (.seq (lm (WP.W6a.dropBits .Q2)) (.seq (lm (popR .Q2)) (.seq (lm (popR .ONE)) (.seq (lm (popR .ONE)) (.seq undirshProg (.seq (lm (popR .Ra)) (.seq (lm (popR .Rc)) (.seq (lm (popR .Rd)) (.seq (lm (popR .Na)) (.seq (lm (popR .Nc)) (.seq (lm (popR .Nd)) (.seq (lm (popR .Ne)) (.seq (lm (popR .Nf)) (.seq (lm (popR .X1)) (.seq (lm (popR .X2)) (.seq (lm (popR .X5)) (.seq (lm (popR .X7)) (.seq (lm (popR .X9)) (.seq (lm (popR .X11)) (.seq (lm (popR .X12)) (.seq (lm (WP.W6a.dropBits .HP)) (.seq (lm (popR .HP)) (.seq (lm (WP.W6a.dropBits .HK)) (.seq (lm (popR .HK)) (.seq (lm (WP.W6a.dropBits .HQ)) (.seq (lm (popR .HQ)) (.seq (lm (WP.W6a.dropBits .HPin)) (lm (popR .HPin))))))))))))))))))))))))))))))))

theorem undirshProg_closed : (undirshProg : MProg Stk τ).Closed :=
  ⟨lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed trivial, lm_closed trivial⟩

theorem drainProg_closed : (drainProg : MProg Stk τ).Closed :=
  whileTop_closed (lm_closed (emove_closed _ _ _))

theorem delimProg_closed : (delimProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, drainProg_closed, lm_closed trivial, moveAll_closed _ _ _ _, lm_closed trivial⟩

theorem cleanupProg_closed : (cleanupProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial,
    lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed trivial, lm_closed trivial,
    undirshProg_closed, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial,
    lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial⟩

end Prog

section Prog2

variable (X : Prims)

/-- F4 cell: rescale the top entry of `R` onto `W0`. -/
def outCell : MProg Stk X.Reg :=
  .seq (lm (emove .R .RI .T1)) (.seq (rescK X) (.seq (lm (emove .RO .W0 .T1)) (lm (dropEntry .RI))))

/-- F4: all entries of `R` above `$D`. -/
def rescLoop : MProg Stk X.Reg := whileTop .R (notSym symD) (outCell X)

theorem outCell_closed : (outCell X).Closed :=
  ⟨lm_closed (emove_closed _ _ _), rescK_closed X, lm_closed (emove_closed _ _ _),
    lm_closed (dropEntry_closed _)⟩

theorem rescLoop_closed : (rescLoop X).Closed := whileTop_closed (outCell_closed X)

end Prog2

section Spec

variable {τ : Type}

theorem undirsh_rs (d : ℕ) (s0 d0 : List Sym) (x : Sym) (σ : Stk → List Sym)
    (hSH : σ .SH = natSyms d ++ Sym.mark :: s0) (hDIR : σ .DIR = x :: Sym.mark :: d0) :
    RS [] (undirshProg : MProg Stk τ) σ (Function.update (Function.update σ .SH s0) .DIR d0)
      (3 * bitLen d + 5) := by
  refine ((dropNat_rs (τ := τ) .SH d (Sym.mark :: s0) σ (termOK_mark' _) hSH).seq
      ((popR_rs .SH _ Sym.mark s0 (by rfl)).seq
      ((popR_rs .DIR _ x (Sym.mark :: d0) (by exact hDIR)).seq
      (popR_rs .DIR _ Sym.mark d0 (by rfl))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · omega

theorem drain_rs (w : ℕ) : ∀ (v : List (ℤ × ℤ)) (W : List Sym) (σ : Stk → List Sym),
    (∀ z ∈ v, EntryW w z) → σ .W0 = blkE v → σ .E = W →
    RS [] (drainProg : MProg Stk τ) σ
      (Function.update (Function.update σ .W0 []) .E (blkE v.reverse ++ W))
      (v.length * (6 * eb w + 5) + 2)
  | [], W, σ, _, hs, hd => by
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hs]
      rfl
    · rw [List.reverse_nil, blkE_nil, List.nil_append, ← hd]
      rw [blkE_nil] at hs
      rw [← hs, Function.update_eq_self, Function.update_eq_self]
  | z :: v, W, σ, hw, hs, hd => by
    have hz : (entrySyms z).length ≤ eb w := length_entrySyms_le (hw z (by simp))
    have ih := drain_rs w v (entrySyms z ++ W)
      (Function.update (Function.update σ .W0 (blkE v)) .E (entrySyms z ++ σ .E))
      (fun y hy => hw y (by simp [hy])) (by rfl) (by rw [Function.update_self, hd])
    refine whileTop_step' ?_ (emove_rs (src := Stk.W0) (dst := Stk.E) (t := Stk.T1) (by decide)
      (by decide) (by decide) z (blkE v) σ (by rw [hs, blkE_cons])) (ih.congr ?_ le_rfl) ?_
    · rw [hs, blkE_cons]
      rfl
    · rw [upd4_absorb, List.reverse_cons, blkE_append, blkE_cons, blkE_nil, List.append_nil,
        List.append_assoc]
    · simp only [List.length_cons]
      have := Nat.mul_le_mul_left 6 hz
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem delim_rs (w : ℕ) (xs : List (ℤ × ℤ)) (σ : Stk → List Sym) (hw : ∀ z ∈ xs, EntryW w z)
    (hW0 : σ .W0 = blkE xs) :
    RS [] (delimProg : MProg Stk τ) σ (Function.update σ .W0 (blkE xs ++ [symD]))
      (xs.length * (12 * eb w + 10) + 7) := by
  refine ((pushC_rs (τ := τ) .E .mark σ).seq
    ((drain_rs w xs (Sym.mark :: σ .E) _ hw (by exact hW0) (by rfl)).seq
    ((pushC_rs .W0 symD _).seq
    ((moveAll_rs (src := Stk.E) (dst := Stk.W0) (t := Stk.T1) (by decide) (by decide) (by decide)
      mark_ok w xs (σ .E) [symD] _ hw (by rfl) (by rfl)).seq
    (popR_rs .E _ Sym.mark (σ .E) (by rfl)))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have key : xs.length * (6 * eb w + 5) + xs.length * (6 * eb w + 5) =
        xs.length * (12 * eb w + 10) := by
      rw [← Nat.mul_add]
      exact congrArg (fun x => xs.length * x) (by omega)
    omega

theorem outCell_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (left : Bool) (w d : ℕ) (a b : ℤ) (rR rs rd : List Sym)
    (σ : Stk → List Sym) (hR : σ .R = entrySyms (a, b) ++ rR)
    (hSH : σ .SH = natSyms d ++ rs) (hrs : TermOK rs) (hDIR : σ .DIR = dirSym left :: rd)
    (hT : ∀ k ∈ rsTemps, TermOK (σ k)) (hw : EntryW w (a, b))
    (hw' : EntryW w (rescLD left d a, rescLD left d b)) :
    RS [] (outCell X) σ
      (Function.update (Function.update σ .R rR) .W0
        (entrySyms (rescLD left d a, rescLD left d b) ++ σ .W0))
      (rescCost CL CA CR w d + 14 * eb w + 6) := by
  refine ((emove_rs (src := Stk.R) (dst := Stk.RI) (t := Stk.T1) (by decide) (by decide) (by decide) (a, b) rR σ (by exact hR)).seq
      ((rescK_rs hok left w d a b (σ .RI) rs rd _ (by rfl) (by exact hSH) hrs (by exact hDIR) (fun k hk => by simp only [rsTemps, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl <;> exact hT _ (by decide)) hw.1 hw.2).seq
      ((emove_rs (src := Stk.RO) (dst := Stk.W0) (t := Stk.T1) (by decide) (by decide) (by decide) (rescLD left d a, rescLD left d b) (σ .RO) _ (by rfl)).seq
      (dropEntry_rs .RI (a, b) (σ .RI) _ (by rfl))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have e1 := length_entrySyms_le hw
    have e2 := length_entrySyms_le hw'
    omega

theorem rescLoop_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (left : Bool) (w d : ℕ) (R0 rs rd : List Sym)
    (hrs : TermOK rs) :
    ∀ (v : List (ℤ × ℤ)) (W : List Sym) (σ : Stk → List Sym),
      (∀ z ∈ v, EntryW w z) → (∀ z ∈ v, EntryW w (rescE left d z)) →
      σ .R = blkE v ++ symD :: R0 → σ .W0 = W → σ .SH = natSyms d ++ rs →
      σ .DIR = dirSym left :: rd → (∀ k ∈ rsTemps, TermOK (σ k)) →
      RS [] (rescLoop X) σ
        (Function.update (Function.update σ .R (symD :: R0)) .W0
          (blkE (v.map (rescE left d)).reverse ++ W))
        (v.length * (rescCost CL CA CR w d + 14 * eb w + 8) + 2)
  | [], W, σ, _, _, hR, hW, _, _, _ => by
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hR]
      exact notSym_self symD R0
    · rw [List.map_nil, List.reverse_nil, blkE_nil, List.nil_append, ← hW]
      rw [blkE_nil, List.nil_append] at hR
      rw [← hR, Function.update_eq_self, Function.update_eq_self]
  | (a, b) :: v, W, σ, hw, hw', hR, hW, hSH, hDIR, hT => by
    have ih := rescLoop_rs hok left w d R0 rs rd hrs v (entrySyms (rescE left d (a, b)) ++ W)
      (Function.update (Function.update σ .R (blkE v ++ symD :: R0)) .W0
        (entrySyms (rescLD left d a, rescLD left d b) ++ σ .W0))
      (fun z hz => hw z (by simp [hz])) (fun z hz => hw' z (by simp [hz])) (by rfl)
      (by rw [← hW]; rfl) (by exact hSH) (by exact hDIR)
      (fun k hk => by
        simp only [rsTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hT _ (by decide))
    refine whileTop_step' ?_ (outCell_rs hok left w d a b (blkE v ++ symD :: R0) rs rd σ
      (by rw [hR, blkE_cons, List.append_assoc]) hSH hrs hDIR hT (hw _ (by simp))
      (hw' (a, b) (by simp))) (ih.congr ?_ le_rfl) ?_
    · rw [hR, blkE_cons, List.append_assoc]
      exact notSym_entry symD_ok (a, b) _
    · rw [upd4_absorb, List.map_cons, List.reverse_cons, blkE_append, blkE_cons, blkE_nil,
        List.append_nil, List.append_assoc]
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem cleanup_rs (K nq d p q pin : ℕ) (x : Sym) (σ0 σ : Stk → List Sym)
    (hTL : σ .TL = symGuard :: σ0 .TL) (hCS : σ .CS = natSyms K ++ Sym.mark :: σ0 .CS)
    (hQ2 : σ .Q2 = natSyms nq ++ Sym.mark :: σ0 .Q2)
    (hONE : σ .ONE = Sym.bit true :: Sym.mark :: σ0 .ONE)
    (hSH : σ .SH = natSyms d ++ Sym.mark :: σ0 .SH) (hDIR : σ .DIR = x :: Sym.mark :: σ0 .DIR)
    (hM : ∀ k ∈ marksL, σ k = Sym.mark :: σ0 k)
    (hHP : σ .HP = natSyms p ++ Sym.mark :: σ0 .HP) (hHK : σ .HK = natSyms K ++ Sym.mark :: σ0 .HK)
    (hHQ : σ .HQ = natSyms q ++ Sym.mark :: σ0 .HQ)
    (hHPin : σ .HPin = natSyms pin ++ Sym.mark :: σ0 .HPin) :
    RS [] (cleanupProg : MProg Stk τ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ .TL (σ0 .TL)) .CS (σ0 .CS)) .Q2 (σ0 .Q2)) .ONE (σ0 .ONE)) .SH (σ0 .SH)) .DIR (σ0 .DIR)) .Ra (σ0 .Ra)) .Rc (σ0 .Rc)) .Rd (σ0 .Rd)) .Na (σ0 .Na)) .Nc (σ0 .Nc)) .Nd (σ0 .Nd)) .Ne (σ0 .Ne)) .Nf (σ0 .Nf)) .X1 (σ0 .X1)) .X2 (σ0 .X2)) .X5 (σ0 .X5)) .X7 (σ0 .X7)) .X9 (σ0 .X9)) .X11 (σ0 .X11)) .X12 (σ0 .X12)) .HP (σ0 .HP)) .HK (σ0 .HK)) .HQ (σ0 .HQ)) .HPin (σ0 .HPin))
      (6 * bitLen K + 3 * bitLen nq + 3 * bitLen d + 3 * bitLen p + 3 * bitLen q + 3 * bitLen pin
        + 50) := by
  refine ((popR_rs (τ := τ) .TL σ symGuard (σ0 .TL) hTL).seq
      ((dropNat_rs .CS K (Sym.mark :: σ0 .CS) _ (termOK_mark' _) (by exact hCS)).seq
      ((popR_rs .CS _ Sym.mark (σ0 .CS) (by rfl)).seq
      ((dropNat_rs .Q2 nq (Sym.mark :: σ0 .Q2) _ (termOK_mark' _) (by exact hQ2)).seq
      ((popR_rs .Q2 _ Sym.mark (σ0 .Q2) (by rfl)).seq
      ((popR_rs .ONE _ (Sym.bit true) (Sym.mark :: σ0 .ONE) (by exact hONE)).seq
      ((popR_rs .ONE _ Sym.mark (σ0 .ONE) (by rfl)).seq
      ((undirsh_rs d (σ0 .SH) (σ0 .DIR) x _ (by exact hSH) (by exact hDIR)).seq
      ((popR_rs .Ra _ Sym.mark (σ0 .Ra) (by exact hM .Ra (by decide))).seq
      ((popR_rs .Rc _ Sym.mark (σ0 .Rc) (by exact hM .Rc (by decide))).seq
      ((popR_rs .Rd _ Sym.mark (σ0 .Rd) (by exact hM .Rd (by decide))).seq
      ((popR_rs .Na _ Sym.mark (σ0 .Na) (by exact hM .Na (by decide))).seq
      ((popR_rs .Nc _ Sym.mark (σ0 .Nc) (by exact hM .Nc (by decide))).seq
      ((popR_rs .Nd _ Sym.mark (σ0 .Nd) (by exact hM .Nd (by decide))).seq
      ((popR_rs .Ne _ Sym.mark (σ0 .Ne) (by exact hM .Ne (by decide))).seq
      ((popR_rs .Nf _ Sym.mark (σ0 .Nf) (by exact hM .Nf (by decide))).seq
      ((popR_rs .X1 _ Sym.mark (σ0 .X1) (by exact hM .X1 (by decide))).seq
      ((popR_rs .X2 _ Sym.mark (σ0 .X2) (by exact hM .X2 (by decide))).seq
      ((popR_rs .X5 _ Sym.mark (σ0 .X5) (by exact hM .X5 (by decide))).seq
      ((popR_rs .X7 _ Sym.mark (σ0 .X7) (by exact hM .X7 (by decide))).seq
      ((popR_rs .X9 _ Sym.mark (σ0 .X9) (by exact hM .X9 (by decide))).seq
      ((popR_rs .X11 _ Sym.mark (σ0 .X11) (by exact hM .X11 (by decide))).seq
      ((popR_rs .X12 _ Sym.mark (σ0 .X12) (by exact hM .X12 (by decide))).seq
      ((dropNat_rs .HP p (Sym.mark :: σ0 .HP) _ (termOK_mark' _) (by exact hHP)).seq
      ((popR_rs .HP _ Sym.mark (σ0 .HP) (by rfl)).seq
      ((dropNat_rs .HK K (Sym.mark :: σ0 .HK) _ (termOK_mark' _) (by exact hHK)).seq
      ((popR_rs .HK _ Sym.mark (σ0 .HK) (by rfl)).seq
      ((dropNat_rs .HQ q (Sym.mark :: σ0 .HQ) _ (termOK_mark' _) (by exact hHQ)).seq
      ((popR_rs .HQ _ Sym.mark (σ0 .HQ) (by rfl)).seq
      ((dropNat_rs .HPin pin (Sym.mark :: σ0 .HPin) _ (termOK_mark' _) (by exact hHPin)).seq
      (popR_rs .HPin _ Sym.mark (σ0 .HPin) (by rfl)))))))))))))))))))))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · omega

end Spec

#assert_std_axioms undirshProg_closed drainProg_closed delimProg_closed cleanupProg_closed
  outCell_closed rescLoop_closed undirsh_rs drain_rs delim_rs outCell_rs rescLoop_rs cleanup_rs

end WP.W9g
