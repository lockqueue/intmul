/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostHdr

/-!
# K5-PP: `log₂ D` from the header (`Bridge/PrePostKD.lean`)

`D = ∏_{i ≥ 1} t_i` (Section 4.4 (`sec:bridge-alg`), `R / t_1`). For a power of two `t = 2^a`, `natSyms t` is `a`
bits `0` then one bit `1` (`zcount_two_pow`), so `log₂ D = Σ_{i ≥ 1} zcount t_i`, which the
program `zcFields` counts while walking over the header fields `t_1, …, t_{d-1}`
(`runs_zcFields`; the number of fields is counted down on a counter stack).

**Scope (honest summary).** Proved, no `sorry`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

theorem encodeNat_two_pow : ∀ a : ℕ, encodeNat (2 ^ a) = List.replicate a false ++ [true]
  | 0 => by
    have h := encodeNat_add_add_one 0
    rw [encodeNat_zero] at h
    simpa using h
  | a + 1 => by
    rw [pow_succ, mul_two, encodeNat_add, if_neg, encodeNat_two_pow a]
    · rfl
    · rw [encodeNat_eq_nil_iff]; positivity

theorem zcount_two_pow (a : ℕ) : zcount (2 ^ a) = a := by
  rw [zcount, encodeNat_two_pow]
  simp

/-- Sum of the `0`-bit counts of a list of fields. -/
def zsum (l : List ℕ) : ℕ := (l.map zcount).sum

theorem zsum_append_single (l : List ℕ) (x : ℕ) : zsum (l ++ [x]) = zsum l + zcount x := by
  simp [zsum]

section Fields

variable {K : Type} [DecidableEq K]

/-- **Zero-count over `k` fields**, `k` counted down on `D`. -/
theorem runs_zcFields {src G N U D : K} (h1 : src ≠ G) (h2 : src ≠ N) (h3 : src ≠ U)
    (h4 : G ≠ N) (h5 : G ≠ U) (h6 : N ≠ U) (h7 : D ≠ src) (h8 : D ≠ G) (h9 : D ≠ N) (h10 : D ≠ U)
    (fs : List ℕ) (c H : ℕ) (L RN RD : List Sym) (S : K → List Sym) (hRN : TermOK RN)
    (hRD : TermOK RD) (hsrc : S src = hdrSyms fs ++ L) (hN : S N = natSyms c ++ RN)
    (hD : S D = natSyms fs.length ++ RD) (hH1 : ∀ x ∈ fs, bitLen x ≤ H) (hH2 : c + zsum fs ≤ H)
    (hH3 : fs.length ≤ H) :
    Runs (zcFields src G N U D) S
      (Function.update (Function.update (Function.update (Function.update S src L) G
        ((hdrSyms fs).reverse ++ S G)) N (natSyms (c + zsum fs) ++ RN)) D RD) (fun _ => True)
      (fs.length * (H * (6 * H + 14) + 6 * H + 16) + 2) := by
  let st : List ℕ → List ℕ → K → List Sym := fun done rest =>
    Function.update (Function.update (Function.update (Function.update S src (hdrSyms rest ++ L)) G
      ((hdrSyms done).reverse ++ S G)) N (natSyms (c + zsum done) ++ RN)) D
      (natSyms rest.length ++ RD)
  have h0 : st [] fs = S := by
    funext k
    simp only [st, Function.update_apply]
    split_ifs with hk1 hk2 hk3 hk4
    · rw [hk1, hD]
    · rw [hk2, hN]; simp [zsum]
    · rw [hk3]; simp [hdrSyms]
    · rw [hk4, hsrc]
    · rfl
  have hw := runs_while (pk := peekR D) (body := .seq (zcField src G N U) (dec D U))
    (c := optIsBit) st 1
    (fun done x rest => bitLen x * (6 * (c + zsum done + zcount x) + 14) + 4 +
      (6 * zerosLead (encodeNat (rest.length + 1)) + 8))
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekR D (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_self] at hv
      rw [hv, optIsBit_natSyms _ hRD]
      cases rest <;> simp)
    (fun done x rest => by
      have hz := runs_zcField h1 h2 h3 h4 h5 h6 x (c + zsum done) (hdrSyms rest ++ L) RN
        (st done (x :: rest)) hRN
        (by simp only [st, Function.update_apply, if_neg (Ne.symm h7), if_neg h2, if_neg h1,
              if_true, hdrSyms_cons]
            simp)
        (by simp only [st, Function.update_apply, if_neg (Ne.symm h9), if_true])
      set S1 := Function.update (Function.update (Function.update (st done (x :: rest)) src
        (hdrSyms rest ++ L)) G ((natSyms x ++ [Sym.mark]).reverse ++ st done (x :: rest) G)) N
        (natSyms (c + zsum done + zcount x) ++ RN) with hS1
      have hS1D : S1 D = (encodeNat (rest.length + 1)).map Sym.bit ++ RD := by
        simp only [hS1, st, Function.update_apply, if_neg h9, if_neg h8, if_neg h7, if_true,
          List.length_cons, natSyms]
      have hd : Runs (dec D U) S1 (Function.update S1 D ((encodeNat rest.length).map Sym.bit ++ RD))
          (fun _ => True) (6 * zerosLead (encodeNat (rest.length + 1)) + 8) :=
        Runs.of_eval fun v => ⟨_, _, dec_eval (ρ := []) h10 v rest.length RD S1 hRD hS1D,
          trivial, le_refl _⟩
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hz hd) ?_)
        (fun _ _ => trivial) le_rfl
      funext k
      simp only [hS1, st, Function.update_apply, zsum_append_single, hdrSyms_append,
        List.reverse_append, hdrSyms_cons]
      split_ifs <;> simp_all [natSyms, hdrSyms, Nat.add_assoc])
    fs []
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st, hdrSyms, natSyms, encodeNat_zero]
  · have hb := whileCost_le_traj 1 (H * (6 * H + 14) + 6 * H + 12)
      (fun done x rest => bitLen x * (6 * (c + zsum done + zcount x) + 14) + 4 +
        (6 * zerosLead (encodeNat (rest.length + 1)) + 8)) fs (fun done x rest h => by
        have hx : bitLen x ≤ H := hH1 x (by rw [← h]; simp)
        have hs : c + zsum done + zcount x ≤ H := by
          have : zsum (done ++ x :: rest) = zsum done + zcount x + zsum rest := by
            simp [zsum]; ring
          rw [h] at this
          omega
        have hz : zerosLead (encodeNat (rest.length + 1)) ≤ H := by
          have h1' := zerosLead_le_length (encodeNat (rest.length + 1))
          have h2' := length_encodeNat_le (rest.length + 1)
          have h3' : (done ++ x :: rest).length = fs.length := by rw [h]
          simp at h3'
          omega
        have := Nat.mul_le_mul hx (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hs) 14)
        omega) fs [] rfl
    nlinarith

end Fields

end SubNLogN.Machine.BridgePP
