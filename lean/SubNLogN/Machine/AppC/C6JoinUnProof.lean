/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinMove

/-!
# Lemma A.8 unjoin: loop body (`Machine/AppC/C6JoinUnProof.lean`)

Part 1 of the proof of `C6UnjoinStmt` (`Machine/AppC/C6QLeaves.lean`): one iteration of the
unjoin loop on the joining layout `KJ E1` (`C6JoinMove.lean`): the in-place right move of one digit
by the K1 kernel (`moveJ`), then `N2 := N2·q` on the binary counter `jp .N2` (`mulConstN`).
Proved: `runs_bodyUJ`. Helpers live in `SubNLogN.Machine.AppC.C6JoinUnAux`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinUnAux

open AppC.C6JoinAux NatArith

/-- The specification of the K1 right-move kernel `P1` (from `K1MoveDigitMixStmt q true`). -/
def KerSpec (q C1 : ℕ) {E1 R1 : Type} [DecidableEq E1]
    (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) : Prop :=
  ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
    (S : KLoc (Fin 4) E1 → List Sym),
    v.length = N0 * q * N1 * N2 → BlkTerm rest → TermOK r2 → TermOK r3 →
    S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
    S (.inl 3) = natSyms N2 ++ r3 →
    Runs P1 S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
      (arrSyms (permByInv (moveRightMixInv q N1 N2) v) ++ S (.inl 1))) (fun _ => True)
      (C1 * (vol v + 1))

section Body

variable {E1 : Type} [DecidableEq E1] {R1 : Type}

/-- One unjoin iteration: the right move of one digit in place, then `N2 := N2·q`. -/
def bodyUJ (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq (moveJ P1)
    ((mulConstN (jp .N2) q (jp .Q) (jp .Td) (jp .A) (jp .Bs) (jp .Acc) (jp .Tm)).liftRegs (lN R1))

omit [DecidableEq E1] in
theorem closed_bodyUJ (q : ℕ) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hP1 : P1.Closed) : (bodyUJ q P1).Closed :=
  ⟨closed_moveJ hP1, WP.W9comp.closed_liftRegs _ (closed_mulConstN _ _ _ _ _ _ _ _)⟩

/-- **One unjoin iteration**: the array `arrSyms v` becomes the right move of its digit
`[N0] × [q] × [N1] × [N2] → [N0] × [N1] × [q] × [N2]`, and the counter on `jp .N2` is multiplied
by `q`; every other stack is unchanged. -/
theorem runs_bodyUJ {q C1 : ℕ} {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hs1 : KerSpec q C1 P1) (S : KJ E1 → List Sym) (v : List (List Bool))
    (rest r2 r3 : List Sym) (N0 N1 N2 : ℕ) (hlen : v.length = N0 * q * N1 * N2)
    (hrest : BlkTerm rest) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hN1 : S (jp .N1) = natSyms N1 ++ r2)
    (hN2 : S (jp .N2) = natSyms N2 ++ r3) :
    Runs (bodyUJ q P1) S
      (Function.update (Function.update S (.inl 0)
        (arrSyms (permByInv (moveRightMixInv q N1 N2) v) ++ rest)) (jp .N2)
        (natSyms (N2 * q) ++ r3))
      (fun _ => True)
      (C1 * (vol v + 1) + 6 * vol (permByInv (moveRightMixInv q N1 N2) v) + 7 +
        mulConstCost N2 q) := by
  have h1 := runs_moveJ S v (permByInv (moveRightMixInv q N1 N2) v) rest r2 r3 N1 N2
    (fun S' h0 h2 h3 => hs1 N0 N1 N2 v rest r2 r3 S' hlen hrest hr2 hr3 h0 h2 h3) hS0 hN1 hN2
  have h2 := runs_mulConstN (K := KJ E1) (k := jp .N2) (Q := jp .Q) (Tdst := jp .Td) (A := jp .A)
    (Bs := jp .Bs) (Acc := jp .Acc) (T := jp .Tm) (by simp [List.nodup_cons]) q N2 r3
    (Function.update S (.inl 0) (arrSyms (permByInv (moveRightMixInv q N1 N2) v) ++ rest)) hr3
    (by rw [Function.update_of_ne (jp_ne_inl _ _)]; exact hN2)
  have h2' := WP.W9comp.runs_mono (WP.W0m.runs_liftRegs (lN R1) h2) (fun _ _ => trivial) le_rfl
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2') (fun _ h => h) ?_
  simp only [List.length_reverse]
  change _ ≤ C1 * (vol v + 1) + 6 * (arrSyms (permByInv (moveRightMixInv q N1 N2) v)).length +
    7 + mulConstCost N2 q
  omega

end Body

end AppC.C6JoinUnAux

end SubNLogN.Machine
