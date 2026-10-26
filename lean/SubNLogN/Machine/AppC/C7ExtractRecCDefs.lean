/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractRecB

/-!
# Lemma A.9 extraction, part 6a: one record, definitions (`Machine/AppC/C7ExtractRecCDefs.lean`)

The body of the main loop of the extraction kernel, for the record with index `n` (counter
`n + 1` on `cM`): decode `n`, test the guards of `y` and `z`; an exceptional record gets a hole
`tag 8` in the skeleton stream and its keyed record (key = the `A`-bit destination
`c7Dest … n`) on the bank, computed by the triple sub-kernel (`TriSpec`, the `C7BadTriStmt`
behaviour) and Horner's rule; a kept record is moved to the skeleton stream (`runs_recBody`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

This file holds the definitions (`NumAt`, `TriSpec`, the programs `recPro`, `badBr`, `goodBr`,
`recEpi`, `recBody`, the cost `recCost`), the value facts `T_inBox`, `dest_lt`, and the closedness
lemmas (`closed_recBody`); the run lemma `runs_recBody` is in `C7ExtractRecC.lean`. Everything here
is proved (no `sorry`).
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.Corr SubNLogN.Machine.AppC.C7RadixAux SubNLogN.Math.Networks
  SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.C7RepairAux.Math

/-- `S k` holds the number `v` above a `TermOK` tail. -/
def NumAt {E' : Type} (S : XK E' → List Sym) (k : XK E') (v : ℕ) : Prop :=
  ∃ r, TermOK r ∧ S k = natSyms v ++ r

/-! ## Value facts -/

/-- The triple map keeps the box. -/
theorem T_inBox (K ρ f : ℕ) (hK : 1 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (t : ℕ × ℕ × ℕ)
    (ht : InBox (f * K) t) :
    InBox (f * K) (packedT0 K ρ f (packedS0inv (f * K) K ρ f t)) := by
  obtain ⟨hx, hy, hz⟩ := packedS0inv_inBox (K := K) (ρ := ρ) (f := f) ht
  refine ⟨hx, ?_, hz⟩
  show Nat.xor _ _ < _
  rw [Nat.xor_eq, ← selMaskM_eq]
  refine Nat.xor_lt_two_pow hy (lt_of_lt_of_le (selMaskM_lt K ρ _ hK (f - 1)) ?_)
  apply Nat.pow_le_pow_right (by norm_num)
  have : (f - 1) * K + K = f * K := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hf]
  omega

/-- The destination of a record index is a record index. -/
theorem dest_lt (K ρ f N0 N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (hK : 1 ≤ K) (hρ : ρ < K)
    (hf : 1 ≤ f) (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3) {n : ℕ}
    (hn : n < c7M K f N0 N1 N2 N3) :
    c7Dest K ρ f N1 N2 N3 σ n < c7M K f N0 N1 N2 N3 :=
  c7Lift_lt hN1 hN2 hN3 σ _ (fun t ht => T_inBox K ρ f hK hρ hf t ht) hn

section Rec

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- **Behaviour of the triple sub-kernel** (`C7BadTriStmt`, on the stacks `nX, nY, nZ` with the
parameters on `K, ρ, f, cL, c2L, c2K, c2r, cF1`). -/
def TriSpec (tri : Prog (XK E') (fun _ => Sym) xk.R) (C K ρ f : ℕ) : Prop :=
  ∀ (x y z : ℕ) (rx ry rz : List Sym) (S : XK E' → List Sym),
    x < 2 ^ (f * K) → y < 2 ^ (f * K) → z < 2 ^ (f * K) → TermOK rx → TermOK ry → TermOK rz →
    S (wk .nX) = natSyms x ++ rx → S (wk .nY) = natSyms y ++ ry → S (wk .nZ) = natSyms z ++ rz →
    NumAt S sK K → NumAt S sRho ρ → NumAt S sF f → NumAt S (wk .cL) (f * K) →
    NumAt S (wk .c2L) (2 ^ (f * K)) → NumAt S (wk .c2K) (2 ^ K) → NumAt S (wk .c2r) (2 ^ ρ) →
    NumAt S (wk .cF1) (f - 1) →
    Runs tri S
      (Function.update (Function.update (Function.update S
        (wk .nX) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).1 ++ rx))
        (wk .nY) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).2.1 ++ ry))
        (wk .nZ) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).2.2 ++ rz))
      (fun _ => True) (C * (f * K + 1) ^ 3)

/-- Prologue of a record: index `n = (n+1) - 1` on `tP`, decoding, names, guard flag. -/
def recPro (σ : Equiv.Perm (Fin 3)) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .tP) .mark) (.seq (cpT xk (wk .cM) (wk .tP)) (.seq (subT xk (wk .tP) (wk .c1))
  (.seq (decode xk) (.seq (names xk σ) (.seq (pushW xk (wk .fG) (.bit false))
  (.seq (guardV xk (wk .nY)) (guardV xk (wk .nZ))))))))

/-- The exceptional branch. -/
def badBr (σ : Equiv.Perm (Fin 3)) (tri : Prog (XK E') (fun _ => Sym) xk.R) :
    Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk sH (.tag 8)) (.seq tri (.seq (horner xk σ) (.seq (keyEmit xk)
  (.seq (dropFW xk (wk .nX)) (.seq (dropFW xk (wk .nY)) (dropFW xk (wk .nZ)))))))

/-- The kept branch. -/
def goodBr : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (goodMove xk) (.seq (dropFW xk (wk .nX)) (.seq (dropFW xk (wk .nY)) (dropFW xk (wk .nZ))))

/-- Epilogue: drop the flag, the decoded coordinates and the index. -/
def recEpi : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .fG)) (.seq (dropFW xk (wk .vC1)) (.seq (dropFW xk (wk .vC2))
  (.seq (dropFW xk (wk .vC3)) (.seq (dropFW xk (wk .vA0)) (.seq (dropFW xk (wk .vA1))
  (.seq (dropFW xk (wk .vA2)) (.seq (dropFW xk (wk .vA3)) (dropFW xk (wk .tP)))))))))

/-- **The record body.** -/
def recBody (σ : Equiv.Perm (Fin 3)) (tri : Prog (XK E') (fun _ => Sym) xk.R) :
    Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (recPro xk σ) (.seq (.seq (peekW xk (wk .fG))
    (.ite (fun v => decide (xk.lw.get v = some (Sym.bit true))) (badBr xk σ tri) (goodBr xk)))
    (recEpi xk))

/-- Cost bound of one record. -/
def recCost (nb f L C R A : ℕ) : ℕ :=
  2 * ((f - 1) * (8 * opCost xk nb + 16)) + 64 * opCost xk nb + C * (L + 1) ^ 3 + 4 * R +
    8 * A + 60

theorem drop_le (nb v : ℕ) (hv : v < 2 ^ nb) : 2 * bitLen v + 2 ≤ opCost xk nb := by
  have := small_le xk nb (bitLen v) 0 (TMFw.W3s.bitLen_le_of_lt hv) (by omega)
  omega


end Rec

section Closed

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

theorem closed_passW (g : Sym) (src dst : XK E') : (passW xk g src dst).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passM g src dst)

theorem closed_setBad : (setBad xk).Closed := ⟨closed_popW xk _, closed_pushW xk _ _⟩

theorem closed_flagIf (x y : XK E') (o : Ordering) : (flagIf xk x y o).Closed :=
  ⟨xk.cmp_closed _ _ _ _, closed_setBad xk, closed_skipW xk⟩

theorem closed_guardBody : (guardBody xk).Closed :=
  ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_modBy xk _ _ _ _ _ _ _, closed_flagIf xk _ _ _,
    closed_addTo xk _ _ _ _ _ _, closed_flagIf xk _ _ _, closed_dropFW xk _,
    closed_divBy xk _ _ _ _ _ _ _⟩

theorem closed_guardLoop : (guardLoop xk).Closed := closed_countdown xk.lw _ _ (closed_guardBody xk)

theorem closed_guardV (v : XK E') : (guardV xk v).Closed :=
  ⟨⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_divBy xk _ _ _ _ _ _ _, closed_pushW xk _ _,
    closed_copyW xk _ _ _⟩, closed_guardLoop xk, closed_popW xk _, closed_dropFW xk _⟩

theorem closed_dmF (x y q r : XK E') : (dmF xk x y q r).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, xk.dm_closed _ _ _ _ _ _ _⟩

theorem closed_decode : (decode xk).Closed :=
  ⟨closed_dmF xk _ _ _ _, closed_dmF xk _ _ _ _, closed_dropFW xk _, closed_dmF xk _ _ _ _,
    closed_dropFW xk _, closed_dmF xk _ _ _ _, closed_dropFW xk _, closed_dmF xk _ _ _ _,
    closed_dropFW xk _, closed_dmF xk _ _ _ _, closed_dropFW xk _⟩

theorem closed_names (σ : Equiv.Perm (Fin 3)) : (names xk σ).Closed :=
  ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_pushW xk _ _, closed_copyW xk _ _ _,
    closed_pushW xk _ _, closed_copyW xk _ _ _⟩

theorem closed_horner (σ : Equiv.Perm (Fin 3)) : (horner xk σ).Closed :=
  ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_mulBy xk _ _ _ _ _ _ _,
    closed_addTo xk _ _ _ _ _ _, closed_mulBy xk _ _ _ _ _ _ _, closed_addTo xk _ _ _ _ _ _,
    closed_mulBy xk _ _ _ _ _ _ _, closed_addTo xk _ _ _ _ _ _, closed_mulBy xk _ _ _ _ _ _ _,
    closed_addTo xk _ _ _ _ _ _, closed_mulBy xk _ _ _ _ _ _ _, closed_addTo xk _ _ _ _ _ _,
    closed_mulBy xk _ _ _ _ _ _ _, closed_addTo xk _ _ _ _ _ _, closed_addTo xk _ _ _ _ _ _⟩

theorem closed_goodMove : (goodMove xk).Closed :=
  ⟨closed_popW xk _, closed_pushW xk _ _, closed_passW xk _ _ _⟩

theorem closed_keyEmit : (keyEmit xk).Closed :=
  ⟨closed_popW xk _, closed_pushW xk _ _, closed_passW xk _ _ _, closed_pushW xk _ _,
    closed_pushW xk _ _, closed_passW xk _ _ _, closed_popW xk _, closed_passW xk _ _ _,
    closed_popW xk _, closed_popW xk _⟩

theorem closed_recPro (σ : Equiv.Perm (Fin 3)) : (recPro xk σ).Closed :=
  ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_subFrom xk _ _ _ _ _ _, closed_decode xk,
    closed_names xk σ, closed_pushW xk _ _, closed_guardV xk _, closed_guardV xk _⟩

theorem closed_badBr (σ : Equiv.Perm (Fin 3)) {tri : Prog (XK E') (fun _ => Sym) xk.R}
    (ht : tri.Closed) : (badBr xk σ tri).Closed :=
  ⟨closed_pushW xk _ _, ht, closed_horner xk σ, closed_keyEmit xk, closed_dropFW xk _,
    closed_dropFW xk _, closed_dropFW xk _⟩

theorem closed_goodBr : (goodBr xk).Closed :=
  ⟨closed_goodMove xk, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _⟩

theorem closed_recEpi : (recEpi xk).Closed :=
  ⟨closed_popW xk _, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _,
    closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _,
    closed_dropFW xk _⟩

/-- The record body is closed when the triple sub-kernel is. -/
theorem closed_recBody (σ : Equiv.Perm (Fin 3)) {tri : Prog (XK E') (fun _ => Sym) xk.R}
    (ht : tri.Closed) : (recBody xk σ tri).Closed :=
  ⟨closed_recPro xk σ, ⟨closed_peekW xk _, closed_badBr xk σ ht, closed_goodBr xk⟩,
    closed_recEpi xk⟩

end Closed

end SubNLogN.Machine.AppC.C7ExtractAux

