/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7TopAddr
import SubNLogN.Machine.AppC.C7TopArith
import SubNLogN.Machine.K1.DigitPairPermMix

/-!
# Lemma A.9 phase 3: the omitted top selected bit (`Machine/AppC/C7Top.lean`)

Lemma A.9 (`lem:transfer13`, Appendix A.4 (`sec:transfer-packed`))
finishes with `y_J ⊕= x_J`, `J = ρ + (f-1)K`: one fixed permutation of an address-digit pair
via Lemma A.4(1) (`lem:transfer-streams`), at cost `c_pair (N_sym + 1)`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

**Proved here (0 `sorry`, no pending hypotheses):** `c7Top_holds τ σ : C7TopStmt τ σ` for every
`τ` and every chunk arrangement `σ` (statement in `Machine/AppC/C7Skel.lean`). The premise
`s_b/W_b < m^τ` of `C7TopStmt` is not used.

**Program** (named stacks `Fin 8` = array, `K, ρ, f, N1, N2, N3, R`; private stacks
`E1 ⊕ Fin 7`, where `E1` are the private stacks of the `K1` kernel):
1. Push guard `mark`s on the private stacks `D`, `T`, `G`, `B`.
2. Build the spectator counters of the digit-pair view (`Machine/AppC/C7TopAddr.lean`) above the
   marks: `G' ∈ {N1·2^{L-1}, N1N2·2^{2L-1}, N2·2^{L-1}}` and `B' ∈ {N2N3·2^{L+J}, N3·2^J}` by slot
   pair (`L = fK`), using the counter routines of `Machine/AppC/C7TopArith.lean` (products by
   nested `inc` loops, powers of two by pushing zeros, `LSB` on top).
3. Run the proved `K1` kernel `k1PairPermMix_holds 2 π` (`π` = CNOT controlled by the `x` digit)
   through `callInj`: source = the array, destination = `D`, counters = `G`, `B`.
4. Move the result back in place by two guard rewinds `D → T → array` (the two reversals cancel),
   and pop the counters and marks.

**Cost.** With `M` records, `V = vol v`, `A = lgVol V` and `b = bitLen M ≤ A`: the counter phase
costs `≤ 194·M·b + 334·M` (`prelude_runs`), the `K1` kernel `C₁(V+1)`, the rewinds and drops
`≤ 6V + 2|G'| + 2|B'| + 8` (`postlude_runs`, `|·|` = bit length, `G', B' ≤ M`). The total is
`≤ (C₁ + 2000)(V + M(A+1)^3) ≤ (C₁ + 2000) · c7Cost τ K f M V R` (`V_le_c7Cost`).

**Reused results.** `K1Digit.k1PairPermMix_holds` (`Machine/K1/DigitPairPermMix.lean`, proved);
`c7Addr_holds` (`Machine/AppC/C7Addr.lean`, proved; only its range part is used, to show that the
permuted array consists of records of width `R`).
-/

namespace SubNLogN.Machine.AppC.C7TopAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.AppC.C7Aux Computability

/-! ## Layout -/

/-- Stacks of the kernel: named `Fin 8`, private `E1 ⊕ Fin 7`. -/
abbrev TL (E1 : Type) := KLoc (Fin 8) (E1 ⊕ Fin 7)

section Layout

variable {E1 : Type}

/-- Own private stack `i`. -/
def pv (i : Fin 7) : TL E1 := .inr (.inr i)

def sArr : TL E1 := .inl 0
def sK : TL E1 := .inl 1
def sRho : TL E1 := .inl 2
def sF : TL E1 := .inl 3
def sN1 : TL E1 := .inl 4
def sN2 : TL E1 := .inl 5
def sN3 : TL E1 := .inl 6
def sD : TL E1 := pv 0
def sT : TL E1 := pv 1
def sG : TL E1 := pv 2
def sB : TL E1 := pv 3
def sT1 : TL E1 := pv 4
def sT2 : TL E1 := pv 5
def sU : TL E1 := pv 6

/-- `K1` named stacks: `0` source = array, `1` destination = `D`, `2`/`3` counters = `G`, `B`. -/
def kIdx (i : Fin 4) : TL E1 :=
  if i.val = 0 then sArr else if i.val = 1 then sD else if i.val = 2 then sG else sB

/-- Embedding of the `K1` kernel's stacks. -/
def ιK : KLoc (Fin 4) E1 → TL E1
  | .inl i => kIdx i
  | .inr e => .inr (.inl e)

theorem ιK_inj [DecidableEq E1] : Function.Injective (ιK (E1 := E1)) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (of_decide_eq_false rfl)
  · fin_cases i <;> exact absurd h (of_decide_eq_false rfl)
  · fin_cases j <;> exact absurd h (of_decide_eq_false rfl)
  · simp only [ιK, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

end Layout

/-! ## Routines acting on one stack `X` -/

section On

variable {K : Type} [DecidableEq K]

theorem pushC_on (Sx : K → List Sym) (X : K) (W : List Sym) (x : Sym) :
    Runs (pushC X x) (Function.update Sx X W) (Function.update Sx X (x :: W)) (fun _ => True) 1 := by
  have h := pushC_runs X x (Function.update Sx X W)
  rwa [Function.update_self, Function.update_idem] at h

theorem popR_on (Sx : K → List Sym) (X : K) (W : List Sym) :
    Runs (popR X) (Function.update Sx X W) (Function.update Sx X W.tail) (fun _ => True) 1 := by
  have h := popR_runs X (Function.update Sx X W)
  rwa [Function.update_self, Function.update_idem] at h

theorem copy_on {src X tmp : K} (hsX : src ≠ X) (hst : src ≠ tmp) (hXt : X ≠ tmp)
    (Sx : K → List Sym) (W : List Sym) (n : ℕ) (rs : List Sym) (hrs : TermOK rs)
    (hS : Sx src = natSyms n ++ rs) :
    Runs (copyBlock src X tmp) (Function.update Sx X W) (Function.update Sx X (natSyms n ++ W))
      (fun _ => True) (7 * bitLen n + 7) := by
  refine Runs.of_eval fun v => ?_
  have hS' : Function.update Sx X W src = (encodeNat n).map Sym.bit ++ rs := by
    rw [Function.update_of_ne hsX, hS]; rfl
  have e := copyBlock_eval hsX hst hXt [] v (encodeNat n) rs _ hrs hS'
  rw [Function.update_self, Function.update_idem] at e
  exact ⟨_, _, e, trivial, le_rfl⟩

theorem pushZ_on {NP T U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U) (hXT : X ≠ T)
    (hXN : X ≠ NP) (Sx : K → List Sym) (W : List Sym) (N : ℕ) (rN : List Sym) (hrN : TermOK rN)
    (hNP : Sx NP = natSyms N ++ rN) :
    Runs (pushZ NP T U X) (Function.update Sx X W)
      (Function.update Sx X (List.replicate N (Sym.bit false) ++ W)) (fun _ => True)
      (N * (6 * bitLen N + 11) + 7 * bitLen N + 11) := by
  have h := pushZ_runs hNT hNU hTU hXT hXN (Function.update Sx X W) N rN hrN
    (by rw [Function.update_of_ne hXN.symm]; exact hNP)
  rwa [Function.update_self, Function.update_idem] at h

theorem pushZZ_on {NP NP' T T' U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U)
    (hXT : X ≠ T) (hXN : X ≠ NP) (hN'T' : NP' ≠ T') (hN'U : NP' ≠ U) (hT'U : T' ≠ U)
    (hXT' : X ≠ T') (hXN' : X ≠ NP') (hN'T : NP' ≠ T) (Sx : K → List Sym) (W : List Sym)
    (N N' : ℕ) (rN rN' : List Sym) (hrN : TermOK rN) (hrN' : TermOK rN')
    (hNP : Sx NP = natSyms N ++ rN) (hNP' : Sx NP' = natSyms N' ++ rN') :
    Runs (pushZZ NP NP' T T' U X) (Function.update Sx X W)
      (Function.update Sx X (List.replicate (N * N') (Sym.bit false) ++ W)) (fun _ => True)
      (N * (N' * (6 * bitLen N' + 11) + 7 * bitLen N' + 11 + 6 * bitLen N + 10) +
        7 * bitLen N + 11) := by
  have h := pushZZ_runs hNT hNU hTU hXT hXN hN'T' hN'U hT'U hXT' hXN' hN'T
    (Function.update Sx X W) N N' rN rN' hrN hrN'
    (by rw [Function.update_of_ne hXN.symm]; exact hNP)
    (by rw [Function.update_of_ne hXN'.symm]; exact hNP')
  rwa [Function.update_self, Function.update_idem] at h

theorem mulAdd_on {NP NP' T T' U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U)
    (hXT : X ≠ T) (hXN : X ≠ NP) (hN'T' : NP' ≠ T') (hN'U : NP' ≠ U) (hT'U : T' ≠ U)
    (hXT' : X ≠ T') (hXN' : X ≠ NP') (hN'T : NP' ≠ T) (hXU : X ≠ U) (Sx : K → List Sym)
    (N N' a : ℕ) (rN rN' rX : List Sym) (hrN : TermOK rN) (hrN' : TermOK rN')
    (hrX : TermOK rX) (hNP : Sx NP = natSyms N ++ rN) (hNP' : Sx NP' = natSyms N' ++ rN') :
    Runs (mulAdd NP NP' T T' U X) (Function.update Sx X (natSyms a ++ rX))
      (Function.update Sx X (natSyms (a + N * N') ++ rX)) (fun _ => True)
      (N * (N' * (6 * bitLen (a + N * N') + 9 + 6 * bitLen N' + 10) + 7 * bitLen N' + 11 +
        6 * bitLen N + 10) + 7 * bitLen N + 11) := by
  have h := mulAdd_runs hNT hNU hTU hXT hXN hN'T' hN'U hT'U hXT' hXN' hN'T hXU
    (Function.update Sx X (natSyms a ++ rX)) N N' a rN rN' rX hrN hrN' hrX
    (by rw [Function.update_of_ne hXN.symm]; exact hNP)
    (by rw [Function.update_of_ne hXN'.symm]; exact hNP') (Function.update_self _ _ _)
  rwa [Function.update_idem] at h

theorem popN_on {NP T U X : K} (hNT : NP ≠ T) (hNU : NP ≠ U) (hTU : T ≠ U) (hXT : X ≠ T)
    (hXN : X ≠ NP) (Sx : K → List Sym) (N m : ℕ) (W rN : List Sym) (hrN : TermOK rN)
    (hNP : Sx NP = natSyms N ++ rN) (hNm : N ≤ m) :
    Runs (popN NP T U X) (Function.update Sx X (List.replicate m (Sym.bit false) ++ W))
      (Function.update Sx X (List.replicate (m - N) (Sym.bit false) ++ W)) (fun _ => True)
      (N * (6 * bitLen N + 11) + 7 * bitLen N + 11) := by
  have h := popN_runs hNT hNU hTU hXT hXN (Function.update Sx X
    (List.replicate m (Sym.bit false) ++ W)) N m W rN hrN
    (by rw [Function.update_of_ne hXN.symm]; exact hNP) (Function.update_self _ _ _) hNm
  rwa [Function.update_idem] at h

end On

/-! ## Cost arithmetic -/

theorem cost_lin {n M : ℕ} (c d : ℕ) (hn : n ≤ M) (hM : 1 ≤ M) :
    c * bitLen n + d ≤ c * (M * bitLen M) + d * M := by
  have hb := bitLen_mono hn
  have h1 : c * bitLen n ≤ c * (M * bitLen M) :=
    Nat.mul_le_mul_left c (le_trans hb (Nat.le_mul_of_pos_left _ hM))
  have h2 : d ≤ d * M := Nat.le_mul_of_pos_right _ hM
  omega

theorem cost_pushZ {N M : ℕ} (hN : N ≤ M) (hM : 1 ≤ M) :
    N * (6 * bitLen N + 11) + 7 * bitLen N + 11 ≤ 13 * (M * bitLen M) + 22 * M := by
  have hb := bitLen_mono hN
  have h1 : N * (6 * bitLen N + 11) ≤ M * (6 * bitLen M + 11) := Nat.mul_le_mul hN (by omega)
  have h2 := cost_lin 7 11 hN hM
  have e : M * (6 * bitLen M + 11) = 6 * (M * bitLen M) + 11 * M := by ring
  omega

theorem cost_pushZZ {N N' M : ℕ} (hNN : N * N' ≤ M) (hN : N ≤ M) (hN' : N' ≤ M) (hM : 1 ≤ M) :
    N * (N' * (6 * bitLen N' + 11) + 7 * bitLen N' + 11 + 6 * bitLen N + 10) + 7 * bitLen N + 11 ≤
      26 * (M * bitLen M) + 43 * M := by
  have hb := bitLen_mono hN
  have hb' := bitLen_mono hN'
  have h1 : N * N' * (6 * bitLen N' + 11) ≤ M * (6 * bitLen M + 11) :=
    Nat.mul_le_mul hNN (by omega)
  have h2 : N * (7 * bitLen N' + 6 * bitLen N + 21) ≤ M * (13 * bitLen M + 21) :=
    Nat.mul_le_mul hN (by omega)
  have h3 := cost_lin 7 11 hN hM
  have e1 : N * (N' * (6 * bitLen N' + 11) + 7 * bitLen N' + 11 + 6 * bitLen N + 10) =
      N * N' * (6 * bitLen N' + 11) + N * (7 * bitLen N' + 6 * bitLen N + 21) := by ring
  have e2 : M * (6 * bitLen M + 11) = 6 * (M * bitLen M) + 11 * M := by ring
  have e3 : M * (13 * bitLen M + 21) = 13 * (M * bitLen M) + 21 * M := by ring
  omega

theorem cost_mulAdd {N N' M : ℕ} (hNN : N * N' ≤ M) (hN : N ≤ M) (hN' : N' ≤ M) (hM : 1 ≤ M) :
    N * (N' * (6 * bitLen (N * N') + 9 + 6 * bitLen N' + 10) + 7 * bitLen N' + 11 +
      6 * bitLen N + 10) + 7 * bitLen N + 11 ≤ 32 * (M * bitLen M) + 51 * M := by
  have hb := bitLen_mono hN
  have hb' := bitLen_mono hN'
  have hb'' := bitLen_mono hNN
  have h1 : N * N' * (6 * bitLen (N * N') + 6 * bitLen N' + 19) ≤ M * (12 * bitLen M + 19) :=
    Nat.mul_le_mul hNN (by omega)
  have h2 : N * (7 * bitLen N' + 6 * bitLen N + 21) ≤ M * (13 * bitLen M + 21) :=
    Nat.mul_le_mul hN (by omega)
  have h3 := cost_lin 7 11 hN hM
  have e1 : N * (N' * (6 * bitLen (N * N') + 9 + 6 * bitLen N' + 10) + 7 * bitLen N' + 11 +
      6 * bitLen N + 10) = N * N' * (6 * bitLen (N * N') + 6 * bitLen N' + 19) +
      N * (7 * bitLen N' + 6 * bitLen N + 21) := by ring
  have e2 : M * (12 * bitLen M + 19) = 12 * (M * bitLen M) + 19 * M := by ring
  have e3 : M * (13 * bitLen M + 21) = 13 * (M * bitLen M) + 21 * M := by ring
  omega

/-! ## The program -/

section Prog

variable {E1 : Type}

/-- Counter `G'` on `G` (above its mark), by slot case `s = σ⁻¹0 + σ⁻¹1` (`1`: slots `{0,1}`,
`2`: `{0,2}`, otherwise `{1,2}`). -/
def gProg (s : ℕ) : SProg (TL E1) :=
  if s = 1 then .seq (copyBlock sN1 sG sU) (.seq (pushZZ sF sK sT1 sT2 sU sG) (popR sG))
  else if s = 2 then .seq (mulAdd sN1 sN2 sT1 sT2 sU sG) (.seq (pushZZ sF sK sT1 sT2 sU sG)
    (.seq (pushZZ sF sK sT1 sT2 sU sG) (popR sG)))
  else .seq (copyBlock sN2 sG sU) (.seq (pushZZ sF sK sT1 sT2 sU sG) (popR sG))

/-- Counter `B'` on `B` (above its mark). -/
def bProg (s : ℕ) : SProg (TL E1) :=
  if s = 1 then .seq (mulAdd sN2 sN3 sT1 sT2 sU sB) (.seq (pushZZ sF sK sT1 sT2 sU sB)
    (.seq (pushZ sRho sT1 sU sB) (.seq (pushZZ sF sK sT1 sT2 sU sB) (popN sK sT1 sU sB))))
  else .seq (copyBlock sN3 sB sU) (.seq (pushZ sRho sT1 sU sB)
    (.seq (pushZZ sF sK sT1 sT2 sU sB) (popN sK sT1 sU sB)))

/-- Phase 1-2: guard marks, then the two counters. -/
def prelude (s : ℕ) : SProg (TL E1) :=
  .seq (pushC sD .mark) (.seq (pushC sT .mark) (.seq (pushC sG .mark) (.seq (gProg s)
    (.seq (pushC sB .mark) (bProg s)))))

/-- Phase 4: move the result back in place (`D → T → array`), drop the counters and marks. -/
def postlude : SProg (TL E1) :=
  .seq (WP.W9comp.rewindTo sD sT .mark) (.seq (WP.W9comp.rewindTo sT sArr .mark)
    (.seq (dropTo sG .mark) (dropTo sB .mark)))

/-- **The top-bit kernel** for slot case `s`, around the `K1` kernel `P1`. -/
def topProg {R1 : Type} (s : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (TL E1) (fun _ => Sym) (Option Sym × R1) :=
  .seq ((prelude s).liftRegs (Lens.fst _ _))
    (.seq (callInj ιK (Lens.snd _ _) P1) (postlude.liftRegs (Lens.fst _ _)))

theorem gProg_closed [DecidableEq E1] (s : ℕ) : (gProg (E1 := E1) s).Closed := by
  unfold gProg
  split_ifs
  · exact ⟨copyBlock_closed _ _ _, pushZZ_closed _ _ _ _ _ _, trivial⟩
  · exact ⟨mulAdd_closed _ _ _ _ _ _, pushZZ_closed _ _ _ _ _ _, pushZZ_closed _ _ _ _ _ _,
      trivial⟩
  · exact ⟨copyBlock_closed _ _ _, pushZZ_closed _ _ _ _ _ _, trivial⟩

theorem bProg_closed [DecidableEq E1] (s : ℕ) : (bProg (E1 := E1) s).Closed := by
  unfold bProg
  split_ifs
  · exact ⟨mulAdd_closed _ _ _ _ _ _, pushZZ_closed _ _ _ _ _ _, pushZ_closed _ _ _ _,
      pushZZ_closed _ _ _ _ _ _, popN_closed _ _ _ _⟩
  · exact ⟨copyBlock_closed _ _ _, pushZ_closed _ _ _ _, pushZZ_closed _ _ _ _ _ _,
      popN_closed _ _ _ _⟩

theorem topProg_closed [DecidableEq E1] {R1 : Type} (s : ℕ) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hP1 : P1.Closed) : (topProg s P1).Closed :=
  ⟨WP.W9comp.closed_liftRegs _
      ⟨trivial, trivial, trivial, gProg_closed s, trivial, bProg_closed s⟩,
    closed_callInj _ _ hP1,
    WP.W9comp.closed_liftRegs _ ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      dropTo_closed _ _, dropTo_closed _ _⟩⟩

end Prog

/-! ## Counter values -/

/-- Machine value of `G'` (zeros pushed above the factor). -/
def gVal (s K f N1 N2 : ℕ) : ℕ :=
  if s = 1 then N1 * 2 ^ (f * K - 1) else if s = 2 then N1 * N2 * 2 ^ (f * K + f * K - 1)
  else N2 * 2 ^ (f * K - 1)

/-- Machine value of `B'`. -/
def bVal (s K ρ f N2 N3 : ℕ) : ℕ :=
  if s = 1 then N2 * N3 * 2 ^ (f * K + ρ + f * K - K) else N3 * 2 ^ (f * K + ρ - K)

theorem natSyms_shift_tail (n k : ℕ) (W : List Sym) (hn : 0 < n) (hk : 1 ≤ k) :
    (List.replicate k (Sym.bit false) ++ (natSyms n ++ W)).tail = natSyms (n * 2 ^ (k - 1)) ++ W := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ, List.cons_append, List.tail_cons, Nat.add_sub_cancel,
    natSyms_mul_two_pow n m hn, List.append_assoc]

theorem natSyms_shift (n k : ℕ) (W : List Sym) (hn : 0 < n) :
    List.replicate k (Sym.bit false) ++ (natSyms n ++ W) = natSyms (n * 2 ^ k) ++ W := by
  rw [natSyms_mul_two_pow n k hn, List.append_assoc]

theorem fK_split {K f : ℕ} (hf : 1 ≤ f) : f * K = (f - 1) * K + K := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_mul]

/-- The machine values are the spectator sizes of `Machine/AppC/C7TopAddr.lean`. -/
theorem gVal_eq (σ : Equiv.Perm (Fin 3)) {K ρ f N1 N2 : ℕ} (hρ : ρ < K) (hf : 1 ≤ f) :
    gVal ((σ.symm 0).val + (σ.symm 1).val) K f N1 N2 = topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1) := by
  have h := fK_split (K := K) hf
  unfold gVal topG
  split_ifs
  · rw [show f * K - 1 = ρ + (f - 1) * K + (K - 1 - ρ) by omega, pow_add]; ring
  · rw [show f * K + f * K - 1 = ρ + (f - 1) * K + f * K + (K - 1 - ρ) by omega, pow_add,
      pow_add]; ring
  · rw [show f * K - 1 = ρ + (f - 1) * K + (K - 1 - ρ) by omega, pow_add]; ring

theorem bVal_eq (σ : Equiv.Perm (Fin 3)) {K ρ f N2 N3 : ℕ} (hρ : ρ < K) (hf : 1 ≤ f) :
    bVal ((σ.symm 0).val + (σ.symm 1).val) K ρ f N2 N3 = topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1) := by
  have h := fK_split (K := K) hf
  unfold bVal topB
  split_ifs
  · rw [show f * K + ρ + f * K - K = ρ + (f - 1) * K + f * K by omega, pow_add]; ring
  · rw [show f * K + ρ - K = ρ + (f - 1) * K by omega]; ring

/-! ## Runs of the phases -/

section Runs

variable {E1 : Type} [DecidableEq E1]

theorem nd {a b : TL E1} (h : decide (a = b) = false) : a ≠ b := of_decide_eq_false h

theorem gProg_runs (s : ℕ) (Sx : TL E1 → List Sym) (X : List Sym) {K f N1 N2 M : ℕ}
    (rK rf r4 r5 : List Sym) (hrK : TermOK rK) (hrf : TermOK rf) (hr4 : TermOK r4)
    (hr5 : TermOK r5) (hSK : Sx sK = natSyms K ++ rK) (hSf : Sx sF = natSyms f ++ rf)
    (hS4 : Sx sN1 = natSyms N1 ++ r4) (hS5 : Sx sN2 = natSyms N2 ++ r5)
    (hK : 1 ≤ K) (hf : 1 ≤ f) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hfK : f * K ≤ M) (hfM : f ≤ M) (hKM : K ≤ M) (h1M : N1 ≤ M) (h2M : N2 ≤ M)
    (h12 : N1 * N2 ≤ M) :
    Runs (gProg s) (Function.update Sx sG (Sym.mark :: X))
      (Function.update Sx sG (natSyms (gVal s K f N1 N2) ++ Sym.mark :: X)) (fun _ => True)
      (84 * (M * bitLen M) + 140 * M) := by
  have hM : 1 ≤ M := le_trans hf hfM
  have hfK1 : 1 ≤ f * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have cZZ := cost_pushZZ hfK hfM hKM hM
  have hZZ : ∀ W : List Sym, Runs (pushZZ sF sK sT1 sT2 sU sG) (Function.update Sx sG W)
      (Function.update Sx sG (List.replicate (f * K) (Sym.bit false) ++ W)) (fun _ => True)
      (f * (K * (6 * bitLen K + 11) + 7 * bitLen K + 11 + 6 * bitLen f + 10) +
        7 * bitLen f + 11) :=
    fun W => pushZZ_on (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl)
      (nd rfl) (nd rfl) (nd rfl) Sx W f K rf rK hrf hrK hSf hSK
  unfold gProg gVal
  split_ifs with hs1 hs2
  · have r1 := copy_on (src := sN1) (X := sG) (tmp := sU) (nd rfl) (nd rfl) (nd rfl) Sx
      (Sym.mark :: X) N1 r4 hr4 hS4
    have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (hZZ _) (popR_on Sx sG _))
    rw [natSyms_shift_tail N1 (f * K) _ hN1 hfK1] at r
    have c1 := cost_lin 7 7 h1M hM
    refine WP.W9comp.runs_mono r (fun _ _ => trivial)
      (le_trans (Nat.add_le_add c1 (Nat.add_le_add cZZ le_rfl)) ?_)
    omega
  · have r1 := mulAdd_on (NP := sN1) (NP' := sN2) (T := sT1) (T' := sT2) (U := sU) (X := sG)
      (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl)
      (nd rfl) (nd rfl) Sx N1 N2 0 r4 r5 (Sym.mark :: X) hr4 hr5 (TermOK.cons rfl _) hS4 hS5
    rw [show natSyms 0 ++ Sym.mark :: X = Sym.mark :: X by simp [natSyms_zero],
      Nat.zero_add] at r1
    have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (hZZ _) (WP.W9comp.runs_seq (hZZ _) (popR_on Sx sG _)))
    rw [← List.append_assoc, ← List.replicate_add,
      natSyms_shift_tail (N1 * N2) (f * K + f * K) _ (Nat.mul_pos hN1 hN2) (by omega)] at r
    have c1 := cost_mulAdd h12 h1M h2M hM
    refine WP.W9comp.runs_mono r (fun _ _ => trivial)
      (le_trans (Nat.add_le_add c1 (Nat.add_le_add cZZ (Nat.add_le_add cZZ le_rfl))) ?_)
    omega
  · have r1 := copy_on (src := sN2) (X := sG) (tmp := sU) (nd rfl) (nd rfl) (nd rfl) Sx
      (Sym.mark :: X) N2 r5 hr5 hS5
    have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (hZZ _) (popR_on Sx sG _))
    rw [natSyms_shift_tail N2 (f * K) _ hN2 hfK1] at r
    have c1 := cost_lin 7 7 h2M hM
    refine WP.W9comp.runs_mono r (fun _ _ => trivial)
      (le_trans (Nat.add_le_add c1 (Nat.add_le_add cZZ le_rfl)) ?_)
    omega

theorem bProg_runs (s : ℕ) (Sx : TL E1 → List Sym) (X : List Sym) {K ρ f N2 N3 M : ℕ}
    (rK r2 rf r5 r6 : List Sym) (hrK : TermOK rK) (hr2 : TermOK r2) (hrf : TermOK rf)
    (hr5 : TermOK r5) (hr6 : TermOK r6) (hSK : Sx sK = natSyms K ++ rK)
    (hS2 : Sx sRho = natSyms ρ ++ r2) (hSf : Sx sF = natSyms f ++ rf)
    (hS5 : Sx sN2 = natSyms N2 ++ r5) (hS6 : Sx sN3 = natSyms N3 ++ r6)
    (hK : 1 ≤ K) (hf : 1 ≤ f) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (hfK : f * K ≤ M) (hfM : f ≤ M) (hKM : K ≤ M) (hρM : ρ ≤ M) (h2M : N2 ≤ M)
    (h3M : N3 ≤ M) (h23 : N2 * N3 ≤ M) :
    Runs (bProg s) (Function.update Sx sB (Sym.mark :: X))
      (Function.update Sx sB (natSyms (bVal s K ρ f N2 N3) ++ Sym.mark :: X)) (fun _ => True)
      (110 * (M * bitLen M) + 190 * M) := by
  have hM : 1 ≤ M := le_trans hf hfM
  have hKfK : K ≤ f * K := Nat.le_mul_of_pos_left K (by omega)
  have cZZ := cost_pushZZ hfK hfM hKM hM
  have cZ := cost_pushZ hρM hM
  have cP := cost_pushZ hKM hM
  have hZZ : ∀ W : List Sym, Runs (pushZZ sF sK sT1 sT2 sU sB) (Function.update Sx sB W)
      (Function.update Sx sB (List.replicate (f * K) (Sym.bit false) ++ W)) (fun _ => True)
      (f * (K * (6 * bitLen K + 11) + 7 * bitLen K + 11 + 6 * bitLen f + 10) +
        7 * bitLen f + 11) :=
    fun W => pushZZ_on (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl)
      (nd rfl) (nd rfl) (nd rfl) Sx W f K rf rK hrf hrK hSf hSK
  have hZ : ∀ W : List Sym, Runs (pushZ sRho sT1 sU sB) (Function.update Sx sB W)
      (Function.update Sx sB (List.replicate ρ (Sym.bit false) ++ W)) (fun _ => True)
      (ρ * (6 * bitLen ρ + 11) + 7 * bitLen ρ + 11) :=
    fun W => pushZ_on (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) Sx W ρ r2 hr2 hS2
  have hP : ∀ (m : ℕ) (W : List Sym), K ≤ m → Runs (popN sK sT1 sU sB)
      (Function.update Sx sB (List.replicate m (Sym.bit false) ++ W))
      (Function.update Sx sB (List.replicate (m - K) (Sym.bit false) ++ W)) (fun _ => True)
      (K * (6 * bitLen K + 11) + 7 * bitLen K + 11) :=
    fun m W hm => popN_on (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) Sx K m W rK hrK hSK hm
  unfold bProg bVal
  split_ifs with hs1
  · have r1 := mulAdd_on (NP := sN2) (NP' := sN3) (T := sT1) (T' := sT2) (U := sU) (X := sB)
      (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl) (nd rfl)
      (nd rfl) (nd rfl) Sx N2 N3 0 r5 r6 (Sym.mark :: X) hr5 hr6 (TermOK.cons rfl _) hS5 hS6
    rw [show natSyms 0 ++ Sym.mark :: X = Sym.mark :: X by simp [natSyms_zero],
      Nat.zero_add] at r1
    have hP' := hP (f * K + ρ + f * K) (natSyms (N2 * N3) ++ Sym.mark :: X) (by omega)
    rw [show List.replicate (f * K + ρ + f * K) (Sym.bit false) ++
        (natSyms (N2 * N3) ++ Sym.mark :: X) =
        List.replicate (f * K) (Sym.bit false) ++ (List.replicate ρ (Sym.bit false) ++
          (List.replicate (f * K) (Sym.bit false) ++ (natSyms (N2 * N3) ++ Sym.mark :: X))) by
      simp only [List.replicate_add, List.append_assoc]] at hP'
    have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (hZZ _) (WP.W9comp.runs_seq (hZ _)
      (WP.W9comp.runs_seq (hZZ _) hP')))
    rw [natSyms_shift (N2 * N3) _ _ (Nat.mul_pos hN2 hN3)] at r
    have c1 := cost_mulAdd h23 h2M h3M hM
    refine WP.W9comp.runs_mono r (fun _ _ => trivial)
      (le_trans (Nat.add_le_add c1 (Nat.add_le_add cZZ (Nat.add_le_add cZ
        (Nat.add_le_add cZZ cP)))) ?_)
    omega
  · have r1 := copy_on (src := sN3) (X := sB) (tmp := sU) (nd rfl) (nd rfl) (nd rfl) Sx
      (Sym.mark :: X) N3 r6 hr6 hS6
    have hP' := hP (f * K + ρ) (natSyms N3 ++ Sym.mark :: X) (by omega)
    rw [show List.replicate (f * K + ρ) (Sym.bit false) ++ (natSyms N3 ++ Sym.mark :: X) =
        List.replicate (f * K) (Sym.bit false) ++ (List.replicate ρ (Sym.bit false) ++
          (natSyms N3 ++ Sym.mark :: X)) by
      simp only [List.replicate_add, List.append_assoc]] at hP'
    have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (hZ _) (WP.W9comp.runs_seq (hZZ _) hP'))
    rw [natSyms_shift N3 _ _ hN3] at r
    have c1 := cost_lin 7 7 h3M hM
    refine WP.W9comp.runs_mono r (fun _ _ => trivial)
      (le_trans (Nat.add_le_add c1 (Nat.add_le_add cZ (Nat.add_le_add cZZ cP))) ?_)
    omega

/-- State after the prelude: marks on `D`, `T`; counters `g`, `b` on `G`, `B` above marks. -/
def preState (S : TL E1 → List Sym) (g b : ℕ) : TL E1 → List Sym :=
  Function.update (Function.update (Function.update (Function.update S sD (Sym.mark :: S sD)) sT
    (Sym.mark :: S sT)) sG (natSyms g ++ Sym.mark :: S sG)) sB (natSyms b ++ Sym.mark :: S sB)

theorem prelude_runs (s : ℕ) (S : TL E1 → List Sym) {K ρ f N1 N2 N3 M : ℕ}
    (rK r2 rf r4 r5 r6 : List Sym) (hrK : TermOK rK) (hr2 : TermOK r2) (hrf : TermOK rf)
    (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6) (hSK : S sK = natSyms K ++ rK)
    (hS2 : S sRho = natSyms ρ ++ r2) (hSf : S sF = natSyms f ++ rf)
    (hS4 : S sN1 = natSyms N1 ++ r4) (hS5 : S sN2 = natSyms N2 ++ r5)
    (hS6 : S sN3 = natSyms N3 ++ r6) (hK : 1 ≤ K) (hf : 1 ≤ f) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (hN3 : 0 < N3) (hfK : f * K ≤ M) (hfM : f ≤ M) (hKM : K ≤ M) (hρM : ρ ≤ M) (h1M : N1 ≤ M)
    (h2M : N2 ≤ M) (h3M : N3 ≤ M) (h12 : N1 * N2 ≤ M) (h23 : N2 * N3 ≤ M) :
    Runs (prelude s) S (preState S (gVal s K f N1 N2) (bVal s K ρ f N2 N3)) (fun _ => True)
      (194 * (M * bitLen M) + 334 * M) := by
  have hM : 1 ≤ M := le_trans hf hfM
  have q1 := pushC_runs sD Sym.mark S
  have q2 := pushC_runs sT Sym.mark (Function.update S sD (Sym.mark :: S sD))
  rw [Function.update_of_ne (show (sT : TL E1) ≠ sD from nd rfl)] at q2
  have eb : ∀ k : TL E1, k ≠ sT → k ≠ sD →
      Function.update (Function.update S sD (Sym.mark :: S sD)) sT (Sym.mark :: S sT) k = S k :=
    fun k h1 h2 => by rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have q3 := pushC_runs sG Sym.mark
    (Function.update (Function.update S sD (Sym.mark :: S sD)) sT (Sym.mark :: S sT))
  rw [eb _ (nd rfl) (nd rfl)] at q3
  have q4 := gProg_runs s
    (Function.update (Function.update S sD (Sym.mark :: S sD)) sT (Sym.mark :: S sT)) (S sG)
    rK rf r4 r5 hrK hrf hr4 hr5 (by rw [eb _ (nd rfl) (nd rfl)]; exact hSK)
    (by rw [eb _ (nd rfl) (nd rfl)]; exact hSf) (by rw [eb _ (nd rfl) (nd rfl)]; exact hS4)
    (by rw [eb _ (nd rfl) (nd rfl)]; exact hS5) hK hf hN1 hN2 hfK hfM hKM h1M h2M h12
  have ed : ∀ k : TL E1, k ≠ sG → k ≠ sT → k ≠ sD →
      Function.update (Function.update (Function.update S sD (Sym.mark :: S sD)) sT
        (Sym.mark :: S sT)) sG (natSyms (gVal s K f N1 N2) ++ Sym.mark :: S sG) k = S k :=
    fun k h0 h1 h2 => by rw [Function.update_of_ne h0, eb k h1 h2]
  have q5 := pushC_runs sB Sym.mark
    (Function.update (Function.update (Function.update S sD (Sym.mark :: S sD)) sT
      (Sym.mark :: S sT)) sG (natSyms (gVal s K f N1 N2) ++ Sym.mark :: S sG))
  rw [ed _ (nd rfl) (nd rfl) (nd rfl)] at q5
  have q6 := bProg_runs s
    (Function.update (Function.update (Function.update S sD (Sym.mark :: S sD)) sT
      (Sym.mark :: S sT)) sG (natSyms (gVal s K f N1 N2) ++ Sym.mark :: S sG)) (S sB)
    rK r2 rf r5 r6 hrK hr2 hrf hr5 hr6
    (by rw [ed _ (nd rfl) (nd rfl) (nd rfl)]; exact hSK)
    (by rw [ed _ (nd rfl) (nd rfl) (nd rfl)]; exact hS2)
    (by rw [ed _ (nd rfl) (nd rfl) (nd rfl)]; exact hSf)
    (by rw [ed _ (nd rfl) (nd rfl) (nd rfl)]; exact hS5)
    (by rw [ed _ (nd rfl) (nd rfl) (nd rfl)]; exact hS6)
    hK hf hN2 hN3 hfK hfM hKM hρM h2M h3M h23
  have r := WP.W9comp.runs_seq q1 (WP.W9comp.runs_seq q2 (WP.W9comp.runs_seq q3 (WP.W9comp.runs_seq q4
    (WP.W9comp.runs_seq q5 q6))))
  refine WP.W9comp.runs_mono r (fun _ _ => trivial) ?_
  omega

theorem mark_not_mem_arrSyms (w : List (List Bool)) : Sym.mark ∉ arrSyms w := by
  simp [arrSyms, blk, recSyms, List.mem_flatten, List.mem_map]

theorem mark_not_mem_natSyms (n : ℕ) : Sym.mark ∉ natSyms n := by
  simp [natSyms]

theorem rewind_runs {K : Type} [DecidableEq K] {src dst : K} (hne : src ≠ dst) (g : Sym)
    (L rest : List Sym) (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Runs (WP.W9comp.rewindTo src dst g) S
      (Function.update (Function.update S src rest) dst (L.reverse ++ S dst)) (fun _ => True)
      (3 * L.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, WP.W9comp.rewindTo_eval hne g v L rest S hg hS, trivial, le_rfl⟩

theorem postlude_runs (S2 : TL E1 → List Sym) (w : List (List Bool)) (rest XD XT XG XB : List Sym)
    (g b : ℕ) (hD : S2 sD = arrSyms w ++ Sym.mark :: XD) (hT : S2 sT = Sym.mark :: XT)
    (hA : S2 sArr = rest) (hG : S2 sG = natSyms g ++ Sym.mark :: XG)
    (hB : S2 sB = natSyms b ++ Sym.mark :: XB) :
    Runs postlude S2 (Function.update (Function.update (Function.update (Function.update
      (Function.update S2 sD XD) sT XT) sArr (arrSyms w ++ rest)) sG XG) sB XB) (fun _ => True)
      (6 * (arrSyms w).length + 2 * bitLen g + 2 * bitLen b + 8) := by
  have r1 := rewind_runs (src := sD) (dst := sT) (nd rfl) Sym.mark (arrSyms w) XD S2
    (mark_not_mem_arrSyms w) hD
  rw [hT] at r1
  have r2 := rewind_runs (src := sT) (dst := sArr) (nd rfl) Sym.mark (arrSyms w).reverse XT
    (Function.update (Function.update S2 sD XD) sT ((arrSyms w).reverse ++ Sym.mark :: XT))
    (by simpa using mark_not_mem_arrSyms w) (Function.update_self _ _ _)
  rw [Function.update_idem, List.reverse_reverse,
    Function.update_of_ne (show (sArr : TL E1) ≠ sT from nd rfl),
    Function.update_of_ne (show (sArr : TL E1) ≠ sD from nd rfl), hA] at r2
  have r3 := dropTo_runs sG Sym.mark (natSyms g) XG
    (Function.update (Function.update (Function.update S2 sD XD) sT XT) sArr (arrSyms w ++ rest))
    (mark_not_mem_natSyms g)
    (by rw [Function.update_of_ne (show (sG : TL E1) ≠ sArr from nd rfl),
      Function.update_of_ne (show (sG : TL E1) ≠ sT from nd rfl),
      Function.update_of_ne (show (sG : TL E1) ≠ sD from nd rfl), hG])
  have r4 := dropTo_runs sB Sym.mark (natSyms b) XB
    (Function.update (Function.update (Function.update (Function.update S2 sD XD) sT XT) sArr
      (arrSyms w ++ rest)) sG XG)
    (mark_not_mem_natSyms b)
    (by rw [Function.update_of_ne (show (sB : TL E1) ≠ sG from nd rfl),
      Function.update_of_ne (show (sB : TL E1) ≠ sArr from nd rfl),
      Function.update_of_ne (show (sB : TL E1) ≠ sT from nd rfl),
      Function.update_of_ne (show (sB : TL E1) ≠ sD from nd rfl), hB])
  have r := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))
  refine WP.W9comp.runs_mono r (fun _ _ => trivial) ?_
  simp only [List.length_reverse, length_natSyms]
  omega

end Runs

/-! ## Cost facts -/

theorem V_le_c7Cost (τ : ℝ) (K f M V R : ℕ) : V + M * (lgVol V + 1) ^ 3 ≤ c7Cost τ K f M V R := by
  unfold c7Cost
  have h0 : (0 : ℝ) ≤ ((f * K : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) τ
  have h1 : (V : ℝ) ≤ (V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg V) (by linarith)
  have h2 : V ≤ ⌈(V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ := by
    have h3 := Nat.le_ceil ((V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1))
    exact_mod_cast le_trans h1 h3
  omega

theorem bitLen_le_lgVol {M V : ℕ} (hMV : M ≤ V) (hM : 1 ≤ M) : bitLen M ≤ lgVol V := by
  apply bitLen_le_of_lt
  unfold lgVol
  have := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * V)
  omega

theorem topA_pos {K ρ f N0 N1 : ℕ} (a b : Fin 3) (hN0 : 0 < N0) (hN1 : 0 < N1) :
    0 < topA K ρ f N0 N1 a b := by
  unfold topA
  split_ifs
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 (by positivity)) hN1) (by positivity)
  · exact Nat.mul_pos hN0 (by positivity)

theorem topG_pos {K ρ f N1 N2 : ℕ} (a b : Fin 3) (hN1 : 0 < N1) (hN2 : 0 < N2) :
    0 < topG K ρ f N1 N2 a b := by
  unfold topG
  split_ifs
  · exact Nat.mul_pos (Nat.mul_pos (by positivity) hN1) (by positivity)
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) hN1)
      (by positivity)) hN2) (by positivity)
  · exact Nat.mul_pos (Nat.mul_pos (by positivity) hN2) (by positivity)

theorem topB_pos {K ρ f N2 N3 : ℕ} (a b : Fin 3) (hN2 : 0 < N2) (hN3 : 0 < N3) :
    0 < topB K ρ f N2 N3 a b := by
  unfold topB
  split_ifs
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) hN2) (by positivity)) hN3
  · exact Nat.mul_pos (by positivity) hN3

end SubNLogN.Machine.AppC.C7TopAux

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts AppC.C7Aux AppC.C7TopAux

/-- **[PROVED] Lemma A.9 phase 3, the omitted top selected bit** (`c7Top_holds`, 0 `sorry`;
Lemma A.9 (`lem:transfer13`),
top selected-bit step). For every `τ` and every chunk arrangement `σ`, `C7TopStmt τ σ` holds: a closed kernel on
the Lemma A.9 named stacks applies `permByInv (c7TopInv K ρ f N1 N2 N3 σ)` to the array in place,
restores all counters and private stacks, and costs at most `(C₁ + 2000) · c7Cost τ K f M V R`,
where `C₁` is the constant of the proved `K1PairPermMixStmt 2 π` kernel. The premise
`s_b/W_b < m^τ` is not used. -/
theorem c7Top_holds (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : C7TopStmt τ σ := by
  intro _
  obtain ⟨C1, hK1⟩ := K1Digit.k1PairPermMix_holds 2 (topπ (σ.symm 0) (σ.symm 1))
  obtain ⟨E1, i1, i2, R1, P1, hfin, hne, hcl, hspec⟩ := hK1 ()
  refine ⟨C1 + 2000, fun _ => ⟨E1 ⊕ Fin 7, inferInstance, inferInstance, Option Sym × R1,
    topProg ((σ.symm 0).val + (σ.symm 1).val) P1, inferInstance, ⟨(none, hne.some)⟩,
    topProg_closed _ hcl, ?_⟩⟩
  intro K ρ f N0 N1 N2 N3 R v rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hlen hw
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  -- size facts
  have hK1' : 1 ≤ K := by omega
  have hQpos : 0 < 2 ^ (f * K) := by positivity
  have hfKlt : f * K < 2 ^ (f * K) := Nat.lt_two_pow_self
  have hX1 : 0 < N0 * 2 ^ (f * K) * 2 ^ (f * K) * 2 ^ (f * K) * N3 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 hQpos) hQpos) hQpos) hN3
  have h12 : N1 * N2 ≤ v.length := by
    rw [hlen, show N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 =
      N1 * N2 * (N0 * 2 ^ (f * K) * 2 ^ (f * K) * 2 ^ (f * K) * N3) by ring]
    exact Nat.le_mul_of_pos_right _ hX1
  have hX2 : 0 < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * 2 ^ (f * K) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 hQpos) hN1) hQpos) hQpos
  have h23 : N2 * N3 ≤ v.length := by
    rw [hlen, show N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 =
      N2 * N3 * (N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * 2 ^ (f * K)) by ring]
    exact Nat.le_mul_of_pos_right _ hX2
  have hX3 : 0 < N0 * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN0 hN1) hQpos) hN2)
      hQpos) hN3
  have hQM : 2 ^ (f * K) ≤ v.length := by
    rw [hlen, show N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 =
      2 ^ (f * K) * (N0 * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3) by ring]
    exact Nat.le_mul_of_pos_right _ hX3
  have hfK : f * K ≤ v.length := by omega
  have hKfK : K ≤ f * K := Nat.le_mul_of_pos_left K (by omega)
  have hffK : f ≤ f * K := Nat.le_mul_of_pos_right f (by omega)
  have hN12 : N1 ≤ N1 * N2 := Nat.le_mul_of_pos_right N1 hN2
  have hN21 : N2 ≤ N1 * N2 := Nat.le_mul_of_pos_left N2 hN1
  have hN32 : N3 ≤ N2 * N3 := Nat.le_mul_of_pos_left N3 hN2
  have hM1 : 1 ≤ v.length := by omega
  -- counter values
  have hgv := gVal_eq σ (N1 := N1) (N2 := N2) hρ hf
  have hbv := bVal_eq σ (N2 := N2) (N3 := N3) hρ hf
  -- phase 1-2: prelude
  have rpre := prelude_runs ((σ.symm 0).val + (σ.symm 1).val) S r1 r2 r3 r4 r5 r6 hr1 hr2 hr3
    hr4 hr5 hr6 hS1 hS2 hS3 hS4 hS5 hS6 hK1' hf hN1 hN2 hN3 hfK (le_trans hffK hfK)
    (le_trans hKfK hfK) (by omega) (le_trans hN12 h12) (le_trans hN21 h12) (le_trans hN32 h23)
    h12 h23
  obtain ⟨S1, hS1def⟩ : ∃ S1, S1 = preState S (gVal ((σ.symm 0).val + (σ.symm 1).val) K f N1 N2)
      (bVal ((σ.symm 0).val + (σ.symm 1).val) K ρ f N2 N3) := ⟨_, rfl⟩
  rw [← hS1def] at rpre
  -- phase 3: the K1 kernel
  obtain ⟨w, hwdef⟩ : ∃ w, w = permByInv (pairPermMixAddr 2 (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1))
      (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1)) (topπ (σ.symm 0) (σ.symm 1)).symm) v := ⟨_, rfl⟩
  have e0 : (S1 ∘ ιK) (.inl 0) = arrSyms v ++ rest := by
    show S1 sArr = _
    rw [hS1def]
    unfold preState
    rw [Function.update_of_ne (show (sArr : TL E1) ≠ sB from nd rfl),
      Function.update_of_ne (show (sArr : TL E1) ≠ sG from nd rfl),
      Function.update_of_ne (show (sArr : TL E1) ≠ sT from nd rfl),
      Function.update_of_ne (show (sArr : TL E1) ≠ sD from nd rfl)]
    exact hS0
  have e2 : (S1 ∘ ιK) (.inl 2) =
      natSyms (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1)) ++ Sym.mark :: S sG := by
    show S1 sG = _
    rw [hS1def]
    unfold preState
    rw [Function.update_of_ne (show (sG : TL E1) ≠ sB from nd rfl), Function.update_self, hgv]
  have e3 : (S1 ∘ ιK) (.inl 3) =
      natSyms (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1)) ++ Sym.mark :: S sB := by
    show S1 sB = _
    rw [hS1def]
    unfold preState
    rw [Function.update_self, hbv]
  have hP := hspec (topA K ρ f N0 N1 (σ.symm 0) (σ.symm 1))
    (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1)) (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1)) v rest
    (Sym.mark :: S sG) (Sym.mark :: S sB) (S1 ∘ ιK) (hlen.trans (topM_eq σ hρ hf)) hrest
    (TermOK.cons rfl _) (TermOK.cons rfl _) e0 e2 e3
  rw [← hwdef] at hP
  have hι0 : ιK (E1 := E1) (.inl 0) = sArr := rfl
  have hι1 : ιK (E1 := E1) (.inl 1) = sD := rfl
  have hS2c : (Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD)) ∘ ιK =
      Function.update (Function.update (S1 ∘ ιK) (.inl 0) rest) (.inl 1)
        (arrSyms w ++ (S1 ∘ ιK) (.inl 1)) := by
    rw [← hι0, ← hι1, Function.update_comp_eq_of_injective _ ιK_inj,
      Function.update_comp_eq_of_injective _ ιK_inj]
    rfl
  have hout : ∀ k, (∀ x, ιK x ≠ k) →
      Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) k = S1 k := by
    intro k hk
    rw [Function.update_of_ne (fun h => hk (.inl 1) (hι1.trans h.symm)),
      Function.update_of_ne (fun h => hk (.inl 0) (hι0.trans h.symm))]
  have rcall := runs_callInj (B := S1)
    (B' := Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD)) ιK_inj
    (Lens.snd (Option Sym) R1) (by rw [hS2c]; exact hP) hout
  -- phase 4: postlude
  have hS1D : S1 sD = Sym.mark :: S sD := by
    rw [hS1def]; unfold preState
    rw [Function.update_of_ne (show (sD : TL E1) ≠ sB from nd rfl),
      Function.update_of_ne (show (sD : TL E1) ≠ sG from nd rfl),
      Function.update_of_ne (show (sD : TL E1) ≠ sT from nd rfl), Function.update_self]
  have hD : Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) sD =
      arrSyms w ++ Sym.mark :: S sD := by
    rw [Function.update_self, hS1D]
  have hT : Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) sT =
      Sym.mark :: S sT := by
    rw [Function.update_of_ne (show (sT : TL E1) ≠ sD from nd rfl),
      Function.update_of_ne (show (sT : TL E1) ≠ sArr from nd rfl), hS1def]
    unfold preState
    rw [Function.update_of_ne (show (sT : TL E1) ≠ sB from nd rfl),
      Function.update_of_ne (show (sT : TL E1) ≠ sG from nd rfl), Function.update_self]
  have hA : Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) sArr = rest := by
    rw [Function.update_of_ne (show (sArr : TL E1) ≠ sD from nd rfl), Function.update_self]
  have hG : Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) sG =
      natSyms (gVal ((σ.symm 0).val + (σ.symm 1).val) K f N1 N2) ++ Sym.mark :: S sG := by
    rw [Function.update_of_ne (show (sG : TL E1) ≠ sD from nd rfl),
      Function.update_of_ne (show (sG : TL E1) ≠ sArr from nd rfl), hS1def]
    unfold preState
    rw [Function.update_of_ne (show (sG : TL E1) ≠ sB from nd rfl), Function.update_self]
  have hB : Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD) sB =
      natSyms (bVal ((σ.symm 0).val + (σ.symm 1).val) K ρ f N2 N3) ++ Sym.mark :: S sB := by
    rw [Function.update_of_ne (show (sB : TL E1) ≠ sD from nd rfl),
      Function.update_of_ne (show (sB : TL E1) ≠ sArr from nd rfl), hS1def]
    unfold preState
    rw [Function.update_self]
  have rpost := postlude_runs _ w rest (S sD) (S sT) (S sG) (S sB) _ _ hD hT hA hG hB
  have r := WP.W9comp.runs_seq (runs_lift (Lens.fst (Option Sym) R1) rpre)
    (WP.W9comp.runs_seq rcall (runs_lift (Lens.fst (Option Sym) R1) rpost))
  -- final state
  have hwc : w = permByInv (c7TopInv K ρ f N1 N2 N3 σ) v := by
    rw [hwdef]
    exact permByInv_congr (fun y hy => topAddr σ hρ hf hN1 hN2 hN3 (by rw [← hlen]; exact hy))
  have hfin : Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update S1 sArr rest) sD (arrSyms w ++ S1 sD))
        sD (S sD)) sT (S sT)) sArr (arrSyms w ++ rest)) sG (S sG)) sB (S sB) =
      Function.update S (.inl 0) (arrSyms (permByInv (c7TopInv K ρ f N1 N2 N3 σ) v) ++ rest) := by
    rw [← hwc]
    funext k
    by_cases hkB : k = sB
    · subst hkB
      simp only [Function.update_self, Function.update_of_ne (show (sB : TL E1) ≠ .inl 0 from nd rfl)]
    by_cases hkG : k = sG
    · subst hkG
      simp only [Function.update_self, Function.update_of_ne (show (sG : TL E1) ≠ sB from nd rfl),
        Function.update_of_ne (show (sG : TL E1) ≠ .inl 0 from nd rfl)]
    by_cases hkA : k = sArr
    · subst hkA
      simp only [Function.update_self, Function.update_of_ne (show (sArr : TL E1) ≠ sB from nd rfl),
        Function.update_of_ne (show (sArr : TL E1) ≠ sG from nd rfl)]
      rfl
    by_cases hkT : k = sT
    · subst hkT
      simp only [Function.update_self, Function.update_of_ne (show (sT : TL E1) ≠ sB from nd rfl),
        Function.update_of_ne (show (sT : TL E1) ≠ sG from nd rfl),
        Function.update_of_ne (show (sT : TL E1) ≠ sArr from nd rfl),
        Function.update_of_ne (show (sT : TL E1) ≠ .inl 0 from nd rfl)]
    by_cases hkD : k = sD
    · subst hkD
      simp only [Function.update_self, Function.update_of_ne (show (sD : TL E1) ≠ sB from nd rfl),
        Function.update_of_ne (show (sD : TL E1) ≠ sG from nd rfl),
        Function.update_of_ne (show (sD : TL E1) ≠ sArr from nd rfl),
        Function.update_of_ne (show (sD : TL E1) ≠ sT from nd rfl),
        Function.update_of_ne (show (sD : TL E1) ≠ .inl 0 from nd rfl)]
    · have hk0 : k ≠ .inl 0 := hkA
      simp only [Function.update_of_ne hkB, Function.update_of_ne hkG, Function.update_of_ne hkA,
        Function.update_of_ne hkT, Function.update_of_ne hkD, Function.update_of_ne hk0, hS1def,
        preState]
  refine WP.W9comp.runs_congr (WP.W9comp.runs_mono r (fun _ _ => trivial) ?_) hfin
  -- cost
  have hV : vol v = v.length * (R + 1) := vol_of_len hw
  have hrange : ∀ y < v.length, pairPermMixAddr 2 (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1))
      (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1)) (topπ (σ.symm 0) (σ.symm 1)).symm y < v.length := by
    intro y hy
    have hy' : y < N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by
      rw [← hlen]; exact hy
    rw [topAddr σ hρ hf hN1 hN2 hN3 hy', hlen]
    exact (c7Addr_holds σ K ρ f N0 N1 N2 N3 hK hρ hf hN0 hN1 hN2 hN3 y hy').2.2.1
  have hww : ∀ p ∈ w, p.length = R := fun p hp => hw p (permByInv_mem hrange (hwdef ▸ hp))
  have hVw : (arrSyms w).length = vol v := by
    show vol w = vol v
    rw [vol_of_len hww, hV, hwdef, permByInv_length]
  have hMV : v.length ≤ vol v := by rw [hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hbA := bitLen_le_lgVol hMV hM1
  have hM' := topM_eq σ (N0 := N0) (N1 := N1) (N2 := N2) (N3 := N3) hρ hf
  have hA0 := topA_pos (K := K) (ρ := ρ) (f := f) (σ.symm 0) (σ.symm 1) hN0 hN1
  have hG0 := topG_pos (K := K) (ρ := ρ) (f := f) (σ.symm 0) (σ.symm 1) hN1 hN2
  have hB0 := topB_pos (K := K) (ρ := ρ) (f := f) (σ.symm 0) (σ.symm 1) hN2 hN3
  have hgM : gVal ((σ.symm 0).val + (σ.symm 1).val) K f N1 N2 ≤ v.length := by
    rw [hgv, hlen, hM']
    have := Nat.le_mul_of_pos_right (topG K ρ f N1 N2 (σ.symm 0) (σ.symm 1))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA0 (by norm_num : 0 < 2)) (by norm_num : 0 < 2)) hB0)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hbM : bVal ((σ.symm 0).val + (σ.symm 1).val) K ρ f N2 N3 ≤ v.length := by
    rw [hbv, hlen, hM']
    have := Nat.le_mul_of_pos_right (topB K ρ f N2 N3 (σ.symm 0) (σ.symm 1))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA0 (by norm_num : 0 < 2)) (by norm_num : 0 < 2)) hG0)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hgb := bitLen_mono hgM
  have hbb := bitLen_mono hbM
  have hc7 := V_le_c7Cost τ K f v.length (vol v) R
  have hA3 : lgVol (vol v) ≤ (lgVol (vol v) + 1) ^ 3 :=
    le_trans (Nat.le_succ _) (Nat.le_self_pow (by norm_num) _)
  have hZ1 : v.length * bitLen v.length ≤ v.length * (lgVol (vol v) + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (le_trans hbA hA3)
  have hZ2 : v.length ≤ v.length * (lgVol (vol v) + 1) ^ 3 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hZ3 : bitLen v.length ≤ v.length * bitLen v.length := Nat.le_mul_of_pos_left _ hM1
  have hZ4 : C1 ≤ C1 * (v.length * (lgVol (vol v) + 1) ^ 3) := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : C1 * (vol v + 1) = C1 * vol v + C1 := by ring
  have e2 : (C1 + 2000) * (vol v + v.length * (lgVol (vol v) + 1) ^ 3) = C1 * vol v +
      C1 * (v.length * (lgVol (vol v) + 1) ^ 3) + 2000 * vol v +
      2000 * (v.length * (lgVol (vol v) + 1) ^ 3) := by ring
  have hmono : (C1 + 2000) * (vol v + v.length * (lgVol (vol v) + 1) ^ 3) ≤
      (C1 + 2000) * c7Cost τ K f v.length (vol v) R := Nat.mul_le_mul_left _ hc7
  rw [hVw]
  omega

end SubNLogN.Machine
