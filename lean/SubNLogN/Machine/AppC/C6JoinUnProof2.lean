/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinUnProof
import SubNLogN.Machine.AppC.C6JoinCommon

/-!
# Lemma A.8 unjoin: loop and program (`Machine/AppC/C6JoinUnProof2.lean`)

Part 2 of the proof of `C6UnjoinStmt`: the loop `loopUJ` over the `t` digits (`K1.Rot.nLoop` on
the counter `tS`), its states `stUJ` (the setup state `stA` of `C6JoinCommon.lean` with the array
after `j` moves and `N2 = q^(ℓ+j)·B`), and the whole program `progUJ = setupJ; loopUJ; cleanJ`.
Proved: `runs_loopUJ`, `closed_progUJ`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinUnAux

open AppC.C6JoinAux NatArith

theorem permByInv_id_uj {α : Type} [Inhabited α] (v : List α) :
    permByInv (fun y => y) v = v := by
  apply List.ext_getElem (by simp [permByInv])
  intro n h1 h2
  simp [permByInv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

section Loop

variable {E1 : Type} [DecidableEq E1] {R1 : Type}

/-- The unjoin loop: `bodyUJ` repeated `t` times (`t` read from `tS`). -/
def loopUJ (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  K1.Rot.nLoop (lWJ R1) (jp .tS) (jp .Kc) (jp .Kt) (bodyUJ q P1)

/-- **The unjoin program.** -/
def progUJ (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq (setupJ q (jp .lS) .N2) (.seq (loopUJ q P1) (cleanJ .N2))

omit [DecidableEq E1] in
theorem closed_progUJ (q : ℕ) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hP1 : P1.Closed) : (progUJ q P1).Closed :=
  ⟨closed_setupJ _ _ _, K1.Rot.closed_nLoop _ _ _ _ (closed_bodyUJ q hP1), closed_cleanJ _⟩

/-- The loop states: after `j` moves, the array is `permByInv (ujComp q ℓ G B j) v` and the
counter on `N2` is `q^(ℓ+j)·B`. -/
def stUJ (S : KJ E1 → List Sym) (q t l G B : ℕ) (v : List (List Bool)) (rest : List Sym)
    (j : ℕ) : KJ E1 → List Sym :=
  Function.update (stA S t l (G * q ^ l) .N2 (q ^ (l + j) * B)) (.inl 0)
    (arrSyms (permByInv (ujComp q l G B j) v) ++ rest)

/-- **The unjoin loop**, with a uniform bound `M` on the cost of one iteration. -/
theorem runs_loopUJ {q C1 : ℕ} {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hs1 : KerSpec q C1 P1) (S : KJ E1 → List Sym) (A t l G B : ℕ) (v : List (List Bool))
    (rest : List Sym) (hv : v.length = A * q ^ t * q ^ t * q ^ l * G * q ^ l * B)
    (hrest : BlkTerm rest) (M : ℕ)
    (hM : ∀ j, j < t → C1 * (vol (permByInv (ujComp q l G B j) v) + 1) +
      6 * vol (permByInv (ujComp q l G B (j + 1)) v) + 7 + mulConstCost (q ^ (l + j) * B) q ≤ M) :
    Runs (loopUJ q P1) (stUJ S q t l G B v rest 0) (stUJ S q t l G B v rest t) (fun _ => True)
      (t * M + 16 * t + 13 * bitLen t + 12) := by
  have h := K1.Rot.runs_nLoop (lWJ R1) (ns := jp .tS) (Kc := jp .Kc) (t := jp .Kt) (by simp)
    (by simp) (by simp) (bodyUJ q P1) (stUJ S q t l G B v rest) t (Sym.mark :: S (jp .tS))
    (termOK_mark _) (by simp [stUJ, stA, Function.update_apply])
    (by simp [stUJ, stA, Function.update_apply]) (fun _ => M) (fun j hj => ?_)
  · refine WP.W9comp.runs_mono h (fun _ h => h) ?_
    simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    omega
  · show Runs _ _ _ _ M
    have hj1 : j + 1 ≤ t := hj
    obtain ⟨k, hk⟩ : ∃ k, t = k + 1 + j := ⟨t - 1 - j, by omega⟩
    have hlenj : (permByInv (ujComp q l G B j) v).length =
        A * q ^ t * q ^ k * q * (G * q ^ l) * (q ^ (l + j) * B) := by
      rw [AppC.C6Aux.length_permByInv, hv, hk]
      ring
    have hb := runs_bodyUJ hs1 (Function.update (stUJ S q t l G B v rest j) (jp .Kc)
        (natSyms (t - (j + 1)) ++ Sym.mark :: stUJ S q t l G B v rest 0 (jp .Kc)))
      (permByInv (ujComp q l G B j) v) rest (Sym.mark :: S (jp .N1)) (Sym.mark :: S (jp .N2))
      (A * q ^ t * q ^ k) (G * q ^ l) (q ^ (l + j) * B) hlenj hrest (termOK_mark _)
      (termOK_mark _) (by simp [stUJ, stA, Function.update_apply])
      (by simp [stUJ, stA, Function.update_apply]) (by simp [stUJ, stA, Function.update_apply])
    have harr : permByInv (moveRightMixInv q (G * q ^ l) (q ^ (l + j) * B))
        (permByInv (ujComp q l G B j) v) = permByInv (ujComp q l G B (j + 1)) v := by
      rw [permByInv_ujComp_succ hj1 v hv, Nat.mul_comm G (q ^ l)]
      rfl
    have hy : q ^ (l + j) * B * q = q ^ (l + (j + 1)) * B := by ring
    rw [harr] at hb
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hb ?_) (fun _ h => h) (hM j hj)
    simp only [stUJ]
    rw [Function.update_comm (show (jp .Kc : KJ E1) ≠ .inl 0 from jp_ne_inl _ _),
      Function.update_idem, Function.update_comm (show (jp .Kc : KJ E1) ≠ jp .N2 by simp),
      stA_upd, hy]

end Loop

end AppC.C6JoinUnAux

end SubNLogN.Machine
