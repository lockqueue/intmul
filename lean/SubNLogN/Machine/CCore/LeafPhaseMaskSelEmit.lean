/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelKit

/-!
# C-core phase leaf, record-wise sign selection: emitting the mask bits (`LeafPhaseMaskSelEmit.lean`)

**Scope (honest summary).** Programs and proved `Runs` lemmas (generic stack type `K`):
* `msEmitP b X Rho C C2 U Tmp`: push one chunk of mask bits onto `Tmp` (forward order:
  `K-1-ρ` zeros, the bit `b`, `ρ` zeros; counters `X = K-1-ρ`, `Rho = ρ`);
* `msMulM Fu Fu2`: multiply a unary block of zeros on `Fu` by `m`.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability

variable {K : Type}

/-- Push one chunk of mask bits onto `Tmp`: `x` zeros (counter `X`), the bit `b`, `r` zeros
(counter `Rho`); `C` is a work counter (empty), `C2`, `U` are temporaries. -/
def msEmitP (b : Bool) (X Rho C C2 U Tmp : K) : PProg K :=
  .seq (msLift (copyBlock X C C2)) (.seq (zbProg C U Tmp)
    (.seq (msLift (pushC Tmp (Sym.bit b)))
      (.seq (msLift (copyBlock Rho C C2)) (zbProg C U Tmp))))

/-- Multiply the unary block of zeros on `Fu` by `m` (via `Fu2`). -/
def msMulM (Fu Fu2 : K) : PProg K :=
  .seq (.seq (peekT Fu) (.loop (fun v => isBitO v.t)
    (.seq (.seq (popO Fu) (msPushAll Fu2 (List.replicate mn (Sym.bit false)))) (peekT Fu))))
    (msLift (moveBlock Fu2 Fu))

theorem closed_copyBlock' (src dst tmp : K) : (copyBlock src dst tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, skip]

theorem closed_msEmitP (b : Bool) (X Rho C C2 U Tmp : K) : (msEmitP b X Rho C C2 U Tmp).Closed :=
  WP.W9comp.closed_seq (closed_msLift (closed_copyBlock' X C C2))
    (WP.W9comp.closed_seq (closed_zbProg C U Tmp)
      (WP.W9comp.closed_seq (closed_msLift (by simp [Prog.Closed, Prog.FreeBelow, pushC]))
        (WP.W9comp.closed_seq (closed_msLift (closed_copyBlock' Rho C C2))
          (closed_zbProg C U Tmp))))

theorem closed_msMulM (Fu Fu2 : K) : (msMulM Fu Fu2).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_peekT Fu)
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_popO Fu) (closed_msPushAll Fu2 _))
      (closed_peekT Fu))) (closed_msLift (closed_moveBlock' Fu2 Fu))

section Runs

variable [DecidableEq K]

theorem runs_msEmitP {X Rho C C2 U Tmp : K} (b : Bool)
    (hXC : X ≠ C) (hXC2 : X ≠ C2) (hCC2 : C ≠ C2) (hRC : Rho ≠ C) (hRC2 : Rho ≠ C2)
    (hCU : C ≠ U) (hCT : C ≠ Tmp) (hRT : Rho ≠ Tmp) (x r : ℕ) (RX RR : List Sym)
    (hRX : TermOK RX) (hRR : TermOK RR) (S : K → List Sym)
    (hX : S X = natSyms x ++ RX) (hRho : S Rho = natSyms r ++ RR) (hC : S C = []) :
    Runs (msEmitP b X Rho C C2 U Tmp) S
      (Function.update S Tmp
        (List.replicate r (Sym.bit false) ++ Sym.bit b :: (List.replicate x (Sym.bit false) ++ S Tmp)))
      (fun _ => True) (30 * (x + r) + 30) := by
  -- 1. copy `x` onto `C`
  have r1 := runs_liftRegs lensPO (runs_copyBlock hXC hXC2 hCC2 (encodeNat x) RX S hRX hX)
  set S1 := Function.update S C ((encodeNat x).map Sym.bit ++ S C) with hS1
  -- 2. `x` zeros onto `Tmp`
  have r2 := runs_zbProg hCU hCT x [] S1 TermOK.nil (by rw [hS1, Function.update_self, hC]; simp [natSyms])
  set S2 := Function.update (Function.update S1 C []) Tmp
    (List.replicate x (Sym.bit false) ++ S1 Tmp) with hS2
  -- 3. the bit `b`
  have r3 := runs_liftRegs lensPO (runs_pushC Tmp (Sym.bit b) S2)
  set S3 := Function.update S2 Tmp (Sym.bit b :: S2 Tmp) with hS3
  -- 4. copy `r` onto `C`
  have hS3R : S3 Rho = (encodeNat r).map Sym.bit ++ RR := by
    rw [hS3, Function.update_of_ne hRT, hS2, Function.update_of_ne hRT, Function.update_of_ne hRC,
      hS1, Function.update_of_ne hRC, hRho]
    rfl
  have r4 := runs_liftRegs lensPO (runs_copyBlock hRC hRC2 hCC2 (encodeNat r) RR S3 hRR hS3R)
  set S4 := Function.update S3 C ((encodeNat r).map Sym.bit ++ S3 C) with hS4
  -- 5. `r` zeros onto `Tmp`
  have hS3C : S3 C = [] := by
    rw [hS3, Function.update_of_ne hCT, hS2, Function.update_of_ne hCT, Function.update_self]
  have r5 := runs_zbProg hCU hCT r [] S4 TermOK.nil (by rw [hS4, Function.update_self, hS3C]; simp [natSyms])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 r5)))) ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have h1 := TMFw.W3s.bitLen_le_of_lt (Nat.lt_two_pow_self (n := x))
    have h2 := TMFw.W3s.bitLen_le_of_lt (Nat.lt_two_pow_self (n := r))
    have e1 : (encodeNat x).length = bitLen x := rfl
    have e2 : (encodeNat r).length = bitLen r := rfl
    omega

theorem runs_msMulM {Fu Fu2 : K} (hne : Fu ≠ Fu2) (a : ℕ) (RF : List Sym) (hRF : TermOK RF)
    (S : K → List Sym) (hFu : S Fu = List.replicate a (Sym.bit false) ++ RF) (hFu2 : S Fu2 = []) :
    Runs (msMulM Fu Fu2) S
      (Function.update S Fu (List.replicate (a * mn) (Sym.bit false) ++ RF))
      (fun _ => True) (4 * (a * mn) + 4 * a + 6) := by
  let st : List Unit → List Unit → K → List Sym := fun done rest =>
    Function.update (Function.update S Fu (List.replicate rest.length (Sym.bit false) ++ RF)) Fu2
      (List.replicate (done.length * mn) (Sym.bit false))
  have hw := runs_while (pk := peekT Fu)
    (body := .seq (popO Fu) (msPushAll Fu2 (List.replicate mn (Sym.bit false))))
    (c := fun v => isBitO v.t) st 1 (fun _ _ _ => 1 + (mn + 1))
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT Fu (st done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st]
      rw [Function.update_of_ne hne, Function.update_self]
      rcases rest with _ | ⟨x, rest⟩
      · simp [isBitO_of_termOK hRF]
      · simp [List.replicate_succ])
    (fun done x rest => by
      have h1 := runs_popO Fu (Sym.bit false) (List.replicate rest.length (Sym.bit false) ++ RF)
        (st done (x :: rest)) (by
          simp only [st]
          rw [Function.update_of_ne hne, Function.update_self]
          simp [List.replicate_succ])
      have h2 := runs_msPushAll Fu2 (List.replicate mn (Sym.bit false))
        (Function.update (st done (x :: rest)) Fu (List.replicate rest.length (Sym.bit false) ++ RF))
      have e : List.replicate mn (Sym.bit false) ++ List.replicate (done.length * mn) (Sym.bit false) =
          List.replicate ((done ++ [x]).length * mn) (Sym.bit false) := by
        rw [← List.replicate_add]
        congr 1
        simp only [List.length_append, List.length_singleton]
        ring
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
        (fun _ _ => trivial) (by simp)
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all)
    (List.replicate a ()) []
  have h0 : st [] (List.replicate a ()) = S := by
    simp only [st, List.length_replicate, List.length_nil, zero_mul, List.replicate_zero]
    rw [← hFu, ← hFu2, Function.update_eq_self, Function.update_eq_self]
  rw [h0] at hw
  have hS1 : st ([] ++ List.replicate a ()) [] Fu2 =
      (List.replicate (a * mn) false).map Sym.bit ++ [] := by
    simp [st, List.map_replicate]
  have h3 := runs_liftRegs lensPO (runs_moveBlock hne.symm (List.replicate (a * mn) false) []
    (st ([] ++ List.replicate a ()) []) TermOK.nil hS1)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hw h3) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    simp only [st, Function.update_apply]
    split_ifs <;> simp_all [List.map_replicate]
  · have hc := whileCost_const 1 (1 + (mn + 1))
      (fun (_ : List Unit) (_ : Unit) (_ : List Unit) => 1 + (mn + 1))
      (fun _ _ _ => le_rfl) (List.replicate a ()) []
    simp only [List.length_replicate] at hc ⊢
    nlinarith

end Runs

end SubNLogN.Machine.CCore.PhaseMaskAux
