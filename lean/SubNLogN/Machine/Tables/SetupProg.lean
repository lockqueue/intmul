/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SetupStmt
import SubNLogN.Machine.Tables.Header
import SubNLogN.Machine.Tables.Frag
import SubNLogN.Machine.Tables.Div

/-!
# K6 (`Machine/Tables/SetupProg.lean`): parameter setup and cleanup of the table generator

**Scope (honest summary).** Proves the contract fragment `SetupStmt`
(`Machine/Tables/SetupStmt.lean`) as `SubNLogN.Machine.Tables.setup_holds`.

* `setupP` (`setupA`, `setupB1`, `setupB2`, `setupC`, `setupD`): fetch `P`, `ω`, `wT`, `t_0` from
  the header (`fetchProg`); `rSH := hdrSyms [t_0]`, `rA := t_0`; `rq := P+2`, `rPC := P+6`;
  `rB := (P+2) + bitLen (2P+1) + 18 = tapPrec P`; `W := 30·rB + 42 = W7.tapPrec (tapPrec P)`,
  `rPi`, `rLn` (W7 kernels at `W`); `rPW = 2^wT`, `rPW1 = 2^(wT+1)`, `rZero = 0`,
  `rNmu = 2^(2P+10)`, `rPq = 2^(P+2)`; temporaries `x40 … x47` are empty again at the end.
* `cleanP`: pop all parameter roles again.
* Costs: every step is bounded by `C·U`, `C·KM·U` or `U` with `U = tabOnce + setup + wT + 1`
  (`W7.tapPrec (tapPrec P) + 1 ≤ 40P + 1000`; the `π`, `ln 2` sizes from IntMul's bounds).

Helpers live in `SubNLogN.Machine.Tables.SetupAux`.
-/

namespace SubNLogN.Machine.Tables.SetupAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables
  SubNLogN.Math.Bridge SubNLogN.Math.Common

/-! ## Header, shape and precision facts -/

theorem hdr_length (b : BrPar) : b.hdr.length = 9 + b.d := by
  simp only [BrPar.hdr, List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn]

theorem hdr_get_P (b : BrPar) (h : 1 < b.hdr.length) : b.hdr[1] = b.P := rfl

theorem hdr_get_W (b : BrPar) (h : 2 < b.hdr.length) : b.hdr[2] = b.ω := rfl

theorem hdr_get_wT (b : BrPar) (h : 4 < b.hdr.length) : b.hdr[4] = b.wT := rfl

theorem prefixProd_one {d : ℕ} (t : Fin d → ℕ) (hd : 0 < d) : prefixProd t 1 = t ⟨0, hd⟩ := by
  unfold prefixProd
  have h : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 1) = {⟨0, hd⟩} := by
    ext i
    simp [Fin.ext_iff]
  rw [h, Finset.prod_singleton]

theorem hdr_get_t0 (b : BrPar) (hd : 0 < b.d) (h : 9 < b.hdr.length) :
    b.hdr[9] = prefixProd b.t 1 := by
  rw [prefixProd_one b.t hd]
  simp [BrPar.hdr, List.getElem_ofFn]

theorem lowerShape_one {d : ℕ} (t : Fin d → ℕ) (hd : 0 < d) : lowerShape t 1 = [t ⟨0, hd⟩] := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp [lowerShape, List.ofFn_succ]

theorem hdrSyms_single (x : ℕ) : hdrSyms [x] = natSyms x ++ [Sym.mark] := by
  simp [hdrSyms]

theorem hdrSyms_lowerShape_one (b : BrPar) (hd : 0 < b.d) :
    hdrSyms (lowerShape b.t 1) = natSyms (prefixProd b.t 1) ++ [Sym.mark] := by
  rw [lowerShape_one b.t hd, prefixProd_one b.t hd, hdrSyms_single]

theorem intSyms_zero' : intSyms 0 = [Sym.pos] := rfl

theorem bitLen_le_pow {x k : ℕ} (h : x ≤ 2 ^ k) : bitLen x ≤ k + 1 :=
  (bitLen_mono h).trans (bitLen_two_pow k).le

theorem bitLen_twoP (P : ℕ) : bitLen (2 * P + 1) ≤ P / 3 + 11 := by
  apply bitLen_le_pow
  have h1 : P / 3 < 2 ^ (P / 3) := Nat.lt_two_pow_self
  have h2 : 2 ^ (P / 3 + 10) = 2 ^ (P / 3) * 1024 := by rw [pow_add]; norm_num
  omega

/-- `tapPrec P` as computed by the machine: `(P+2) + bitLen (P + (P+2) - 1) + 18`. -/
theorem tapPrec_eq (P : ℕ) : tapPrec P = P + 2 + bitLen (P + (P + 2) - 1) + 18 := by
  unfold tapPrec tapGuard
  rw [lg_eq_bitLen (by omega : 2 ≤ 2 * P + 2),
    show 2 * P + 2 - 1 = P + (P + 2) - 1 by omega]
  omega

theorem tapPrec_le (P : ℕ) : tapPrec P ≤ P + P / 3 + 31 := by
  have h := bitLen_twoP P
  rw [tapPrec_eq, show P + (P + 2) - 1 = 2 * P + 1 by omega]
  omega

theorem w7tap_eq (x : ℕ) : W7.tapPrec x = x * 30 + 42 := by
  unfold W7.tapPrec
  ring

theorem w7tap_le (P : ℕ) : tapPrec P * 30 + 42 + 1 ≤ 40 * P + 1000 := by
  have h := tapPrec_le P
  omega

/-! ## The cost unit -/

/-- The cost unit `U = tabOnce + setup + wT + 1`. -/
def sU (b : BrPar) : ℕ := tabOnce b + b.setup + b.wT + 1

theorem one_le_sU (b : BrPar) : 1 ≤ sU b := by unfold sU; omega

theorem tabOnce_ge (b : BrPar) : (40 * b.P + 1000) * (40 * b.P + 1000) ≤ tabOnce b := by
  unfold tabOnce
  have h : 1 ≤ 40 * b.P + 1000 := by omega
  calc (40 * b.P + 1000) * (40 * b.P + 1000)
      = (40 * b.P + 1000) ^ 2 * 1 := by ring
    _ ≤ (40 * b.P + 1000) ^ 2 * (40 * b.P + 1000) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
    _ = (40 * b.P + 1000) ^ 4 := by ring

theorem sq_le_sU (b : BrPar) : (40 * b.P + 1000) * (40 * b.P + 1000) ≤ sU b := by
  have h := tabOnce_ge b
  unfold sU
  omega

theorem lin_le_sU (b : BrPar) : 40 * b.P + 1000 ≤ sU b :=
  le_trans (Nat.le_mul_of_pos_left _ (by omega)) (sq_le_sU b)

theorem pow4_le_sU (b : BrPar) {v : ℕ} (hv : v + 1 ≤ 40 * b.P + 1000) : (v + 1) ^ 4 ≤ sU b := by
  have h : (v + 1) ^ 4 ≤ tabOnce b := Nat.pow_le_pow_left hv 4
  unfold sU
  omega

theorem setup_le_sU (b : BrPar) : b.setup ≤ sU b := by unfold sU; omega

theorem wT_le_sU (b : BrPar) : b.wT + 1 ≤ sU b := by unfold sU; omega

/-- The header length `H` satisfies `(H+2)^2 ≤ 4·setup`. -/
theorem hdrSq_le (b : BrPar) :
    ((hdrSyms b.hdr).length + 2) ^ 2 ≤ 4 * b.setup := by
  unfold BrPar.setup
  set H := (hdrSyms b.hdr).length
  have h1 : (H + 1) ^ 2 ≤ (H + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (H + 2) ^ 2 ≤ 4 * (H + 1) ^ 2 := by ring_nf; omega
  omega

theorem fetchCost_le (C : ℕ) (b : BrPar) :
    fetchCost C (hdrSyms b.hdr).length ≤ 4 * (C * sU b) + 12 * sU b := by
  unfold fetchCost
  have h := hdrSq_le b
  have h2 := setup_le_sU b
  have h3 : ((hdrSyms b.hdr).length + 2) ^ 2 ≤ 4 * sU b := by omega
  have h4 : C * ((hdrSyms b.hdr).length + 2) ^ 2 ≤ C * (4 * sU b) := Nat.mul_le_mul_left C h3
  have e : (C + 3) * ((hdrSyms b.hdr).length + 2) ^ 2 =
      C * ((hdrSyms b.hdr).length + 2) ^ 2 + 3 * ((hdrSyms b.hdr).length + 2) ^ 2 := by ring
  have e2 : C * (4 * sU b) = 4 * (C * sU b) := by ring
  omega

/-- `C·X ≤ C·U` from `X ≤ U`. -/
theorem cmulU {C X : ℕ} {b : BrPar} (h : X ≤ sU b) : C * X ≤ C * sU b := Nat.mul_le_mul_left C h

/-! ## Programs -/

section Progs

variable (I : TB)

/-- Fetch header field `k` onto `dst` (counter `x40`, temporary `x41`). -/
def fetchK (k : ℕ) (dst : TL) : TP I := (tnat I x40 k).seq (fetchProg I x40 x41 dst)

/-- Phase A: `rP := P`, `rW := ω`, `x42 := wT`, `rA := t_0`, `rSH := t_0 ++ [mark]`. -/
def setupA : TP I :=
  (fetchK I 1 rP).seq ((fetchK I 2 rW).seq ((fetchK I 4 x42).seq ((fetchK I 9 rA).seq
    ((tpush I rSH .mark).seq (tcp I rA rSH)))))

/-- Phase B1: `rq := P + 2`, `rPC := (P + 2) + 4 = coeffPrec P`. -/
def setupB1 : TP I :=
  (tnat I x43 2).seq ((tad I rP x43 rq).seq ((tdr I x43).seq ((tnat I x43 4).seq
    ((tad I rq x43 rPC).seq (tdr I x43)))))

/-- Phase B2: `rB := (P+2) + bitLen (P + (P+2) - 1) + 18 = tapPrec P`. -/
def setupB2 : TP I :=
  (tad I rP rq x43).seq ((clogProg I x43 x44 x45).seq ((tad I rq x45 x46).seq
    ((tnat I x47 18).seq ((tad I x46 x47 rB).seq ((tdr I x43).seq ((tdr I x45).seq
    ((tdr I x46).seq (tdr I x47))))))))

/-- Phase C: `W := 30·rB + 42`, `rPi := π_W`, `rLn := (ln 2)_W`. -/
def setupC : TP I :=
  (tnat I x43 30).seq ((natMul I rB x43 x44).seq ((tnat I x45 42).seq ((tad I x44 x45 x46).seq
    ((tpi I x46 rPi).seq ((tln I x46 rLn).seq ((tdr I x43).seq ((tdr I x44).seq
    ((tdr I x45).seq (tdr I x46)))))))))

/-- Phase D1: `rPW := 2^wT`, `rPW1 := 2^(wT+1)` (`x42` emptied), `rZero := 0`. -/
def setupD1 : TP I :=
  (pow2Int I rPW x42).seq ((tic I x42).seq ((pow2Int I rPW1 x42).seq ((tdr I x42).seq
    (tpush I rZero .pos))))

/-- Phase D2: `rNmu := 2^(pC + 2 + q)`, `rPq := 2^q`. -/
def setupD2 : TP I :=
  (tnat I x43 2).seq ((tad I rPC x43 x44).seq ((tad I x44 rq x45).seq ((pow2Int I rNmu x45).seq
    ((tdr I x43).seq ((tdr I x44).seq ((tdr I x45).seq (pow2Int I rPq rq)))))))

/-- **Setup** of all parameter roles. -/
def setupP : TP I :=
  (setupA I).seq ((setupB1 I).seq ((setupB2 I).seq ((setupC I).seq
    ((setupD1 I).seq (setupD2 I)))))

/-- **Cleanup**: pop all parameter roles. -/
def cleanP : TP I :=
  (tdr I rP).seq ((tdr I rW).seq ((tdr I rB).seq ((tdr I rPC).seq ((intDrop I rPi).seq
    ((intDrop I rLn).seq ((intDrop I rPW).seq ((intDrop I rPW1).seq ((intDrop I rZero).seq
    ((intDrop I rNmu).seq ((intDrop I rPq).seq ((tdr I rq).seq ((dropBlock I rSH).seq
    (tdr I rA)))))))))))))

theorem fetchK_closed (k : ℕ) (dst : TL) : (fetchK I k dst).Closed :=
  ⟨pushBits_closed _ _, fetchProg_closed I _ _ _⟩

theorem setupP_closed : (setupP I).Closed :=
  ⟨⟨fetchK_closed I _ _, fetchK_closed I _ _, fetchK_closed I _ _, fetchK_closed I _ _, trivial,
      callI_closed _ _ _ _⟩,
    ⟨pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pushBits_closed _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    ⟨callI_closed _ _ _ _, clogProg_closed I _ _ _, callI_closed _ _ _ _, pushBits_closed _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _⟩,
    ⟨pushBits_closed _ _, natMul_closed I _ _ _, pushBits_closed _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _⟩,
    ⟨pow2Int_closed I _ _, callI_closed _ _ _ _, pow2Int_closed I _ _, callI_closed _ _ _ _,
      trivial⟩,
    pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pow2Int_closed I _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, pow2Int_closed I _ _⟩

theorem cleanP_closed : (cleanP I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    intDrop_closed I _, intDrop_closed I _, intDrop_closed I _, intDrop_closed I _,
    intDrop_closed I _, intDrop_closed I _, intDrop_closed I _, callI_closed _ _ _ _,
    dropBlock_closed I _, callI_closed _ _ _ _⟩

end Progs

/-! ## Phase specifications -/

section Specs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.fetchK_spec (hI : I.Spec Mul C) (k : ℕ) (dst : TL) (h40 : dst ≠ x40) (h41 : dst ≠ x41)
    (hdP : dst ≠ sPar) (B : TL → List Sym) (hs : List ℕ) (hk : k < hs.length) (rpar : List Sym)
    (v : ℕ) (hv : hs[k] = v) (hP : B sPar = hdrSyms hs ++ rpar) (hB40 : B x40 = [])
    (hB41 : B x41 = []) (ρ : List (TP I)) :
    HT ρ B (fetchK I k dst) (Function.update B dst (natSyms v ++ B dst))
      (bitLen k + 1 + fetchCost C (hdrSyms hs).length) := by
  refine (HT.seq (HT.tnat_spec x40 k B ρ)
    (HT.fetch_spec hI x40 x41 dst (by decide) (by decide) (by decide) h40 h41 hdP _ hs k hk []
      rpar TermOK.nil (by rw [Function.update_self, hB40])
      (by simp (disch := decide) only [Function.update_of_ne, hP])
      (by simp (disch := decide) only [Function.update_of_ne, hB41]) ρ)).of_eq ?_ le_rfl
  funext g
  by_cases g1 : g = dst
  · rw [g1]
    simp only [Function.update_self, Function.update_of_ne h40, hv]
  · by_cases g2 : g = x40
    · rw [g2]
      simp only [Function.update_of_ne (Ne.symm h40), Function.update_self, hB40]
    · simp only [Function.update_of_ne g1, Function.update_of_ne g2]

theorem H_le_setup (b : BrPar) : (hdrSyms b.hdr).length ≤ b.setup := by
  unfold BrPar.setup
  have h : (hdrSyms b.hdr).length + 1 ≤ ((hdrSyms b.hdr).length + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  omega

/-- The state after phase A. -/
def stA (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B
    rP (natSyms b.P)) rW (natSyms b.ω)) x42 (natSyms b.wT)) rA (natSyms (prefixProd b.t 1)))
    rSH (natSyms (prefixProd b.t 1) ++ [Sym.mark])

theorem HT.setupA_spec (hI : I.Spec Mul C) (b : BrPar) (rpar : List Sym) (B : TL → List Sym)
    (hd : 2 ≤ b.d) (hP : B sPar = hdrSyms b.hdr ++ rpar) (hB0 : ∀ j : Fin 61, B (.inr j) = [])
    (ρ : List (TP I)) :
    HT ρ B (setupA I) (stA B b) (17 * (C * sU b) + 89 * sU b) := by
  have hlen := hdr_length b
  have hd0 : 0 < b.d := by omega
  have h40 : B x40 = [] := hB0 40
  have h41 : B x41 = [] := hB0 41
  have hrP : B rP = [] := hB0 0
  have hrW : B rW = [] := hB0 1
  have h42 : B x42 = [] := hB0 42
  have hrA : B rA = [] := hB0 16
  have hrSH : B rSH = [] := hB0 22
  have hF := fetchCost_le C b
  have hU := one_le_sU b
  have ht0 : bitLen (prefixProd b.t 1) + 1 ≤ sU b := by
    have h1 := bitLen_le_length_hdrSyms (hs := b.hdr) (k := 9) (by omega)
    rw [hdr_get_t0 b hd0] at h1
    have h2 := H_le_setup b
    have h3 := setup_le_sU b
    omega
  have hfk : ∀ k, k ≤ 9 → bitLen k + 1 + fetchCost C (hdrSyms b.hdr).length ≤
      4 * (C * sU b) + 22 * sU b := fun k hk => by
    have := bitLen_le_self k
    omega
  refine (HT.seq ((HT.fetchK_spec hI 1 rP (by decide) (by decide) (by decide) B b.hdr
      (by omega) rpar b.P (hdr_get_P b _) hP h40 h41 ρ).mono (hfk 1 (by omega)))
    (HT.seq ((HT.fetchK_spec hI 2 rW (by decide) (by decide) (by decide) _ b.hdr
      (by omega) rpar b.ω (hdr_get_W b _)
      (by simp (disch := decide) only [Function.update_of_ne, hP])
      (by simp (disch := decide) only [Function.update_of_ne, h40])
      (by simp (disch := decide) only [Function.update_of_ne, h41]) ρ).mono (hfk 2 (by omega)))
    (HT.seq ((HT.fetchK_spec hI 4 x42 (by decide) (by decide) (by decide) _ b.hdr
      (by omega) rpar b.wT (hdr_get_wT b _)
      (by simp (disch := decide) only [Function.update_of_ne, hP])
      (by simp (disch := decide) only [Function.update_of_ne, h40])
      (by simp (disch := decide) only [Function.update_of_ne, h41]) ρ).mono (hfk 4 (by omega)))
    (HT.seq ((HT.fetchK_spec hI 9 rA (by decide) (by decide) (by decide) _ b.hdr
      (by omega) rpar (prefixProd b.t 1) (hdr_get_t0 b hd0 _)
      (by simp (disch := decide) only [Function.update_of_ne, hP])
      (by simp (disch := decide) only [Function.update_of_ne, h40])
      (by simp (disch := decide) only [Function.update_of_ne, h41]) ρ).mono (hfk 9 le_rfl))
    (HT.seq ((HT.tpush_spec rSH .mark _ ρ).mono hU)
      ((HT.tcp_spec hI rA rSH (by decide) _ (prefixProd b.t 1) [] TermOK.nil
        (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrA,
          List.append_nil]) ρ).mono (cmulU ht0))))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rSH
  · subst g1
    simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, hrSH]
  by_cases g2 : g = rA
  · subst g2
    simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, hrA,
      List.append_nil]
  by_cases g3 : g = x42
  · subst g3
    simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, h42,
      List.append_nil]
  by_cases g4 : g = rW
  · subst g4
    simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, hrW,
      List.append_nil]
  by_cases g5 : g = rP
  · subst g5
    simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, hrP,
      List.append_nil]
  simp only [stA, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5]

/-- Uniform per-step bounds. -/
theorem stepU {C X : ℕ} {b : BrPar} (h : X ≤ sU b) : C * X ≤ C * sU b + sU b := by
  have := cmulU (C := C) h
  omega

theorem natU {c : ℕ} {C : ℕ} {b : BrPar} (h : c ≤ 900) : bitLen c + 1 ≤ C * sU b + sU b := by
  have := bitLen_le_self c
  have := lin_le_sU b
  omega

theorem binU {C u v : ℕ} {b : BrPar} (h : u + v + 1 ≤ sU b) :
    C * (bitLen u + bitLen v + 1) ≤ C * sU b + sU b := by
  have := bitLen_le_self u
  have := bitLen_le_self v
  exact stepU (by omega)

theorem unU {C v : ℕ} {b : BrPar} (h : v + 1 ≤ sU b) : C * (bitLen v + 1) ≤ C * sU b + sU b := by
  have := bitLen_le_self v
  exact stepU (by omega)

/-- The state after phase B1. -/
def stB1 (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (stA B b) rq (natSyms (b.P + 2))) rPC (natSyms (coeffPrec b.P))

theorem HT.setupB1_spec (hI : I.Spec Mul C) (b : BrPar) (B : TL → List Sym)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (stA B b) (setupB1 I) (stB1 B b) (6 * (C * sU b + sU b)) := by
  have hrq : B rq = [] := hB0 13
  have hrPC : B rPC = [] := hB0 3
  have h43 : B x43 = [] := hB0 43
  have hL := lin_le_sU b
  refine (HT.seq ((HT.tnat_spec x43 2 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.tad_spec hI rP x43 rq (by decide) _ b.P 2 [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, h43])
      ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x43 _ 2 [] TermOK.nil
      (by simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, h43])
      ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tnat_spec x43 4 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.tad_spec hI rq x43 rPC (by decide) _ (b.P + 2) 4 [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stA, Function.update_of_ne, Function.update_self, hrq,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ).mono
      (binU (b := b) (by omega)))
      ((HT.tdr_spec hI x43 _ 4 [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ).mono
      (unU (b := b) (by omega)))))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rPC
  · subst g1
    simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self, hrPC,
      coeffPrec, List.append_nil]
  by_cases g2 : g = rq
  · subst g2
    simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self, hrq,
      List.append_nil]
  by_cases g3 : g = x43
  · subst g3
    simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self, h43]
  simp only [stB1, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3]

/-- The state after phase B2. -/
def stB2 (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (stB1 B b) rB (natSyms (tapPrec b.P))

theorem clogCost_le (C : ℕ) (b : BrPar) :
    C * (bitLen (b.P + (b.P + 2)) + 1) + (C * (bitLen (b.P + (b.P + 2)) + 1) +
      (bitLen (b.P + (b.P + 2) - 1) * (C * (bitLen (b.P + (b.P + 2) - 1) + 1) + 3) + 2)) ≤
    C * sU b + sU b := by
  have hc : bitLen (b.P + (b.P + 2)) ≤ 2 * b.P + 2 := (bitLen_le_self _).trans (by omega)
  have ha : bitLen (b.P + (b.P + 2) - 1) ≤ 2 * b.P + 1 := (bitLen_le_self _).trans (by omega)
  generalize bitLen (b.P + (b.P + 2)) = c at hc ⊢
  generalize bitLen (b.P + (b.P + 2) - 1) = a at ha ⊢
  have hsq := sq_le_sU b
  have haa : a * (a + 1) ≤ (2 * b.P + 1) * (2 * b.P + 2) := Nat.mul_le_mul ha (by omega)
  have hX : (c + 1) + (c + 1) + a * (a + 1) ≤ sU b := by nlinarith
  have hC := cmulU (C := C) hX
  have e : C * (c + 1) + (C * (c + 1) + (a * (C * (a + 1) + 3) + 2)) =
      C * ((c + 1) + (c + 1) + a * (a + 1)) + (3 * a + 2) := by ring
  rw [e]
  have h3 : 3 * a + 2 ≤ sU b := by have := lin_le_sU b; omega
  omega

theorem HT.setupB2_spec (hI : I.Spec Mul C) (b : BrPar) (B : TL → List Sym)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (stB1 B b) (setupB2 I) (stB2 B b) (9 * (C * sU b + sU b)) := by
  have hrB : B rB = [] := hB0 2
  have h43 : B x43 = [] := hB0 43
  have h44 : B x44 = [] := hB0 44
  have h45 : B x45 = [] := hB0 45
  have h46 : B x46 = [] := hB0 46
  have h47 : B x47 = [] := hB0 47
  have hL := lin_le_sU b
  have hn1 : bitLen (b.P + (b.P + 2) - 1) ≤ 2 * b.P + 1 := (bitLen_le_self _).trans (by omega)
  refine (HT.seq ((HT.tad_spec hI rP rq x43 (by decide) _ b.P (b.P + 2) [] [] TermOK.nil
      TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.clogProg_spec hI x43 x44 x45 (by decide) (by decide) (by decide) _
      (b.P + (b.P + 2)) [] TermOK.nil (by omega)
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h43])
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, h44])
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, h45]) ρ).mono
      (clogCost_le C b))
    (HT.seq ((HT.tad_spec hI rq x45 x46 (by decide) _ (b.P + 2) (bitLen (b.P + (b.P + 2) - 1))
      [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_self,
        List.append_nil]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.tnat_spec x47 18 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.tad_spec hI x46 x47 rB (by decide) _ (b.P + 2 + bitLen (b.P + (b.P + 2) - 1))
      18 [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h46, List.append_nil])
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h47]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x43 _ (b.P + (b.P + 2)) [] TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h43]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x45 _ (bitLen (b.P + (b.P + 2) - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x46 _ (b.P + 2 + bitLen (b.P + (b.P + 2) - 1)) [] TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h46]) ρ).mono (unU (b := b) (by omega)))
      ((HT.tdr_spec hI x47 _ 18 [] TermOK.nil
      (by simp (disch := decide) only [stB1, stA, Function.update_of_ne, Function.update_self,
        h47]) ρ).mono (unU (b := b) (by omega))))))))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rB
  · subst g1
    simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne, Function.update_self,
      hrB, List.append_nil, tapPrec_eq]
  by_cases g2 : g = x43
  · subst g2
    simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne, Function.update_self, h43]
  by_cases g3 : g = x45
  · subst g3
    simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne, Function.update_self, h45]
  by_cases g4 : g = x46
  · subst g4
    simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne, Function.update_self, h46]
  by_cases g5 : g = x47
  · subst g5
    simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne, Function.update_self, h47]
  simp only [stB2, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5]

/-- The state after phase C. -/
def stC (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (stB2 B b)
    rPi (intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1))
    rLn (intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1)

theorem HT.setupC_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (b : BrPar) (B : TL → List Sym) (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (stB2 B b) (setupC I) (stC B b) (C * (KM * sU b) + 10 * (C * sU b + sU b)) := by
  have hrPi : B rPi = [] := hB0 4
  have hrLn : B rLn = [] := hB0 5
  have h43 : B x43 = [] := hB0 43
  have h44 : B x44 = [] := hB0 44
  have h45 : B x45 = [] := hB0 45
  have h46 : B x46 = [] := hB0 46
  have hL := lin_le_sU b
  have hU := one_le_sU b
  have hW := w7tap_le b.P
  have htp := tapPrec_le b.P
  have hmul : C * Mul (tapPrec b.P + 30) + C + 5 ≤ C * (KM * sU b) + (C * sU b + sU b) := by
    have h1 : (tapPrec b.P + 30 + 1) ^ 2 ≤ sU b := by
      have h2 : (tapPrec b.P + 30 + 1) ^ 2 ≤ (40 * b.P + 1000) * (40 * b.P + 1000) := by
        rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      have := sq_le_sU b
      omega
    have h3 : Mul (tapPrec b.P + 30) ≤ KM * sU b :=
      (hMul _).trans (Nat.mul_le_mul_left KM h1)
    have h4 : C * Mul (tapPrec b.P + 30) ≤ C * (KM * sU b) := Nat.mul_le_mul_left C h3
    have h5 : C ≤ C * sU b := Nat.le_mul_of_pos_right C hU
    omega
  have hpow : C * (tapPrec b.P * 30 + 42 + 1) ^ 4 ≤ C * sU b + sU b :=
    stepU (pow4_le_sU b hW)
  refine (HT.seq ((HT.tnat_spec x43 30 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.natMul_spec hI rB x43 x44 (by decide) (by decide) (by decide) _
      (tapPrec b.P + 30) (tapPrec b.P) 30 [] [] (by have := bitLen_le_self (tapPrec b.P); omega)
      (by have := bitLen_le_self 30; omega) TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stB2, Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h43]) ρ).mono hmul)
    (HT.seq ((HT.tnat_spec x45 42 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.tad_spec hI x44 x45 x46 (by decide) _ (tapPrec b.P * 30) 42 [] [] TermOK.nil
      TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h44])
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h45]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.tpi_spec hI x46 rPi (by decide) _ (tapPrec b.P * 30 + 42) [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h46]) ρ).mono hpow)
    (HT.seq ((HT.tln_spec hI x46 rLn (by decide) _ (tapPrec b.P * 30 + 42) [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h46]) ρ).mono hpow)
    (HT.seq ((HT.tdr_spec hI x43 _ 30 [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h43]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x44 _ (tapPrec b.P * 30) [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h44]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x45 _ 42 [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h45]) ρ).mono (unU (b := b) (by omega)))
      ((HT.tdr_spec hI x46 _ (tapPrec b.P * 30 + 42) [] TermOK.nil
      (by simp (disch := decide) only [stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h46]) ρ).mono (unU (b := b) (by omega)))))))))))).of_eq ?_
      (by omega)
  funext g
  by_cases g1 : g = rPi
  · subst g1
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, hrPi, List.append_nil, w7tap_eq]
  by_cases g2 : g = rLn
  · subst g2
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, hrLn, List.append_nil, w7tap_eq]
  by_cases g3 : g = x43
  · subst g3
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h43]
  by_cases g4 : g = x44
  · subst g4
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h44]
  by_cases g5 : g = x45
  · subst g5
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h45]
  by_cases g6 : g = x46
  · subst g6
    simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h46]
  simp only [stC, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6]

/-- `C·X ≤ k·(C·U)` from `X ≤ k·U`. -/
theorem cmulk {C X k : ℕ} {b : BrPar} (h : X ≤ k * sU b) : C * X ≤ k * (C * sU b) := by
  have := Nat.mul_le_mul_left C h
  have e : C * (k * sU b) = k * (C * sU b) := by ring
  omega

/-- The state after phase D1. -/
def stD1 (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (stC B b) x42 [])
    rPW (intSyms ((2 ^ b.wT : ℕ) : ℤ))) rPW1 (intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ)))
    rZero (intSyms 0)

theorem HT.setupD1_spec (hI : I.Spec Mul C) (b : BrPar) (B : TL → List Sym)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (stC B b) (setupD1 I) (stD1 B b) (8 * (C * sU b) + 4 * sU b) := by
  have hrPW : B rPW = [] := hB0 6
  have hrPW1 : B rPW1 = [] := hB0 7
  have hrZ : B rZero = [] := hB0 8
  have hw := wT_le_sU b
  have hU := one_le_sU b
  have hL := lin_le_sU b
  have bw := bitLen_le_self b.wT
  have bw1 := bitLen_le_self (b.wT + 1)
  refine (HT.seq ((HT.pow2Int_spec hI rPW x42 (by decide) _ b.wT [] TermOK.nil
      (by simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne, hrPW])
      (by simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, List.append_nil]) ρ).mono
      (show C * (b.wT + bitLen b.wT + 1) + 3 ≤ 2 * (C * sU b) + sU b from by
        have := cmulk (C := C) (k := 2) (b := b) (X := b.wT + bitLen b.wT + 1) (by omega)
        omega))
    (HT.seq ((HT.tic_spec hI x42 _ b.wT [] TermOK.nil
      (by simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, List.append_nil]) ρ).mono
      (cmulU (b := b) (show bitLen b.wT + 1 ≤ sU b by omega)))
    (HT.seq ((HT.pow2Int_spec hI rPW1 x42 (by decide) _ (b.wT + 1) [] TermOK.nil
      (by simp (disch := decide) only [stC, stB2, stB1, stA, Function.update_of_ne, hrPW1])
      (by simp only [Function.update_self]) ρ).mono
      (show C * (b.wT + 1 + bitLen (b.wT + 1) + 1) + 3 ≤ 3 * (C * sU b) + sU b from by
        have := cmulk (C := C) (k := 3) (b := b) (X := b.wT + 1 + bitLen (b.wT + 1) + 1)
          (by omega)
        omega))
    (HT.seq ((HT.tdr_spec hI x42 _ (b.wT + 1) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ).mono
      (cmulk (C := C) (k := 2) (b := b) (X := bitLen (b.wT + 1) + 1) (by omega)))
      ((HT.tpush_spec rZero .pos _ ρ).mono hU))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rZero
  · subst g1
    simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, hrZ, intSyms_zero']
  by_cases g2 : g = rPW1
  · subst g2
    simp (disch := decide) only [stD1, Function.update_of_ne, Function.update_self]
  by_cases g3 : g = x42
  · subst g3
    simp (disch := decide) only [stD1, Function.update_of_ne, Function.update_self]
  by_cases g4 : g = rPW
  · subst g4
    simp (disch := decide) only [stD1, Function.update_of_ne, Function.update_self]
  simp only [stD1, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4]

/-- The state after phase D2. -/
def stD2 (B : TL → List Sym) (b : BrPar) : TL → List Sym :=
  Function.update (Function.update (stD1 B b)
    rNmu (intSyms ((2 ^ (coeffPrec b.P + 2 + (b.P + 2)) : ℕ) : ℤ)))
    rPq (intSyms ((2 ^ (b.P + 2) : ℕ) : ℤ))

theorem HT.setupD2_spec (hI : I.Spec Mul C) (b : BrPar) (B : TL → List Sym)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (stD1 B b) (setupD2 I) (stD2 B b) (8 * (C * sU b + sU b)) := by
  have hrN : B rNmu = [] := hB0 9
  have hrPq : B rPq = [] := hB0 10
  have h43 : B x43 = [] := hB0 43
  have h44 : B x44 = [] := hB0 44
  have h45 : B x45 = [] := hB0 45
  have hL := lin_le_sU b
  have hcp : coeffPrec b.P = b.P + 6 := by unfold coeffPrec; omega
  have he := bitLen_le_self (coeffPrec b.P + 2 + (b.P + 2))
  have he2 := bitLen_le_self (b.P + 2)
  refine (HT.seq ((HT.tnat_spec x43 2 _ ρ).mono (natU (b := b) (C := C) (by omega)))
    (HT.seq ((HT.tad_spec hI rPC x43 x44 (by decide) _ (coeffPrec b.P) 2 [] [] TermOK.nil
      TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, Function.update_of_ne,
        Function.update_self, List.append_nil])
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h43]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.tad_spec hI x44 rq x45 (by decide) _ (coeffPrec b.P + 2) (b.P + 2) [] []
      TermOK.nil TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h44])
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, Function.update_of_ne,
        Function.update_self, List.append_nil]) ρ).mono (binU (b := b) (by omega)))
    (HT.seq ((HT.pow2Int_spec hI rNmu x45 (by decide) _ (coeffPrec b.P + 2 + (b.P + 2)) []
      TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne, hrN])
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h45]) ρ).mono
      (show C * (coeffPrec b.P + 2 + (b.P + 2) + bitLen (coeffPrec b.P + 2 + (b.P + 2)) + 1) + 3
          ≤ C * sU b + sU b from by
        have := cmulU (C := C) (b := b)
          (X := coeffPrec b.P + 2 + (b.P + 2) + bitLen (coeffPrec b.P + 2 + (b.P + 2)) + 1)
          (by omega)
        omega))
    (HT.seq ((HT.tdr_spec hI x43 _ 2 [] TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h43]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x44 _ (coeffPrec b.P + 2) [] TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h44]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI x45 _ (coeffPrec b.P + 2 + (b.P + 2)) [] TermOK.nil
      (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
        Function.update_self, h45]) ρ).mono (unU (b := b) (by omega)))
      ((HT.pow2Int_spec hI rPq rq (by decide) _ (b.P + 2) [] TermOK.nil
        (by simp (disch := decide) only [stD1, stC, stB2, stB1, stA, Function.update_of_ne,
          hrPq])
        (by simp (disch := decide) only [stD1, stC, stB2, stB1, Function.update_of_ne,
          Function.update_self, List.append_nil]) ρ).mono
        (show C * (b.P + 2 + bitLen (b.P + 2) + 1) + 3 ≤ C * sU b + sU b from by
          have := cmulU (C := C) (b := b) (X := b.P + 2 + bitLen (b.P + 2) + 1) (by omega)
          omega))))))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rPq
  · subst g1
    simp (disch := decide) only [stD2, Function.update_of_ne, Function.update_self]
  by_cases g2 : g = rNmu
  · subst g2
    simp (disch := decide) only [stD2, Function.update_of_ne, Function.update_self]
  by_cases g3 : g = x43
  · subst g3
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h43]
  by_cases g4 : g = x44
  · subst g4
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h44]
  by_cases g5 : g = x45
  · subst g5
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, Function.update_of_ne,
      Function.update_self, h45]
  simp only [stD2, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5]

/-- The end state of the setup is the parameter state `parSt`. -/
theorem stD2_eq (b : BrPar) (B : TL → List Sym) (hd : 2 ≤ b.d)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) : stD2 B b = parSt B b := by
  have hd0 : 0 < b.d := by omega
  have h42 : B x42 = [] := hB0 42
  funext g
  by_cases g1 : g = rSH
  · subst g1
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self, hdrSyms_lowerShape_one b hd0]
  by_cases g2 : g = x42
  · subst g2
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self, h42]
  by_cases g3 : g = rP
  · subst g3
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g4 : g = rW
  · subst g4
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g5 : g = rB
  · subst g5
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g6 : g = rPC
  · subst g6
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g7 : g = rPi
  · subst g7
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g8 : g = rLn
  · subst g8
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g9 : g = rPW
  · subst g9
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g10 : g = rPW1
  · subst g10
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g11 : g = rZero
  · subst g11
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g12 : g = rNmu
  · subst g12
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g13 : g = rPq
  · subst g13
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g14 : g = rq
  · subst g14
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  by_cases g15 : g = rA
  · subst g15
    simp (disch := decide) only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne,
      Function.update_self]
  simp only [stD2, stD1, stC, stB2, stB1, stA, parSt, Function.update_of_ne g1,
    Function.update_of_ne g2, Function.update_of_ne g3, Function.update_of_ne g4,
    Function.update_of_ne g5, Function.update_of_ne g6, Function.update_of_ne g7,
    Function.update_of_ne g8, Function.update_of_ne g9, Function.update_of_ne g10,
    Function.update_of_ne g11, Function.update_of_ne g12, Function.update_of_ne g13,
    Function.update_of_ne g14, Function.update_of_ne g15]

/-! ## Cleanup -/

theorem W_le (b : BrPar) : W7.tapPrec (tapPrec b.P) + 4 ≤ sU b := by
  rw [w7tap_eq]
  have h1 := w7tap_le b.P
  have h2 := sq_le_sU b
  have h3 : 40 * b.P + 2000 ≤ (40 * b.P + 1000) * (40 * b.P + 1000) := by nlinarith
  omega

theorem pi_bitLen {W : ℕ} {b : BrPar} (hW : W + 4 ≤ sU b) :
    bitLen (IntMul.computablePiScaledWithCost W).1.natAbs + 1 ≤ sU b := by
  have h0 := (IntMul.computablePiScaledWithCost_error_le W).2
  have h1 := IntMul.computablePiScaledWithCost_toNat_le W
  have e1 : ((IntMul.computablePiScaledWithCost W).1.natAbs : ℤ) =
      (IntMul.computablePiScaledWithCost W).1 := Int.natAbs_of_nonneg h0
  have e2 : ((IntMul.computablePiScaledWithCost W).1.toNat : ℤ) =
      (IntMul.computablePiScaledWithCost W).1 := Int.toNat_of_nonneg h0
  have h2 : (IntMul.computablePiScaledWithCost W).1.natAbs ≤ 2 ^ (W + 2) := by omega
  have h3 := bitLen_le_pow h2
  omega

theorem ln_bitLen {W : ℕ} {b : BrPar} (h3 : 3 ≤ W) (hW : W + 4 ≤ sU b) :
    bitLen (IntMul.computableLog2ScaledWithCost W).1.natAbs + 1 ≤ sU b := by
  have h0 := (IntMul.computableLog2ScaledWithCost_ge_half W h3).2
  have h1 := IntMul.computableLog2ScaledWithCost_toNat_le W
  have e1 : ((IntMul.computableLog2ScaledWithCost W).1.natAbs : ℤ) =
      (IntMul.computableLog2ScaledWithCost W).1 := Int.natAbs_of_nonneg h0
  have e2 : ((IntMul.computableLog2ScaledWithCost W).1.toNat : ℤ) =
      (IntMul.computableLog2ScaledWithCost W).1 := Int.toNat_of_nonneg h0
  have h2 : (IntMul.computableLog2ScaledWithCost W).1.natAbs ≤ 2 ^ (W + 1) := by omega
  have h4 := bitLen_le_pow h2
  omega

theorem dropU {C n k : ℕ} {b : BrPar} (h : n + 1 ≤ k * sU b) :
    1 + C * (n + 1) ≤ k * (C * sU b) + sU b := by
  have := cmulk (C := C) h
  have := one_le_sU b
  omega

theorem HT.cleanP_spec (hI : I.Spec Mul C) (b : BrPar) (B : TL → List Sym) (hd : 2 ≤ b.d)
    (hB0 : ∀ j : Fin 61, B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (parSt B b) (cleanP I) B (20 * (C * sU b) + 20 * sU b) := by
  have hd0 : 0 < b.d := by omega
  have hlen := hdr_length b
  have hrP : B rP = [] := hB0 0
  have hrW : B rW = [] := hB0 1
  have hrB : B rB = [] := hB0 2
  have hrPC : B rPC = [] := hB0 3
  have hrPi : B rPi = [] := hB0 4
  have hrLn : B rLn = [] := hB0 5
  have hrPW : B rPW = [] := hB0 6
  have hrPW1 : B rPW1 = [] := hB0 7
  have hrZ : B rZero = [] := hB0 8
  have hrN : B rNmu = [] := hB0 9
  have hrPq : B rPq = [] := hB0 10
  have hrq : B rq = [] := hB0 13
  have hrA : B rA = [] := hB0 16
  have hrSH : B rSH = [] := hB0 22
  have hL := lin_le_sU b
  have hU := one_le_sU b
  have hW := W_le b
  have hw := wT_le_sU b
  have htp := tapPrec_le b.P
  have hcp : coeffPrec b.P = b.P + 6 := by unfold coeffPrec; omega
  have hω : bitLen b.ω + 1 ≤ sU b := by
    have h1 := bitLen_le_length_hdrSyms (hs := b.hdr) (k := 2) (by omega)
    rw [hdr_get_W b] at h1
    have := H_le_setup b
    have := setup_le_sU b
    omega
  have ht0 : bitLen (prefixProd b.t 1) + 1 ≤ sU b := by
    have h1 := bitLen_le_length_hdrSyms (hs := b.hdr) (k := 9) (by omega)
    rw [hdr_get_t0 b hd0] at h1
    have := H_le_setup b
    have := setup_le_sU b
    omega
  have hW3 : 3 ≤ W7.tapPrec (tapPrec b.P) := by rw [w7tap_eq]; omega
  refine (HT.seq ((HT.tdr_spec hI rP _ b.P [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI rW _ b.ω [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (stepU (b := b) hω))
    (HT.seq ((HT.tdr_spec hI rB _ (tapPrec b.P) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.tdr_spec hI rPC _ (coeffPrec b.P) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.intDrop_spec hI rPi _
      (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1 [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 1) (by have := pi_bitLen hW; omega)))
    (HT.seq ((HT.intDrop_spec hI rLn _
      (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1 [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 1) (by have := ln_bitLen hW3 hW; omega)))
    (HT.seq ((HT.intDrop_spec hI rPW _ ((2 ^ b.wT : ℕ) : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 2) (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)))
    (HT.seq ((HT.intDrop_spec hI rPW1 _ ((2 ^ (b.wT + 1) : ℕ) : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 3) (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)))
    (HT.seq ((HT.intDrop_spec hI rZero _ 0 [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 1)
        (by rw [Int.natAbs_zero]; have := bitLen_le_self 0; omega)))
    (HT.seq ((HT.intDrop_spec hI rNmu _ ((2 ^ (coeffPrec b.P + 2 + (b.P + 2)) : ℕ) : ℤ) []
      TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 1) (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)))
    (HT.seq ((HT.intDrop_spec hI rPq _ ((2 ^ (b.P + 2) : ℕ) : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (dropU (b := b) (C := C) (k := 1) (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)))
    (HT.seq ((HT.tdr_spec hI rq _ (b.P + 2) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (unU (b := b) (by omega)))
    (HT.seq ((HT.dropBlock_spec rSH ρ (natSyms (prefixProd b.t 1)) []
      (mark_not_mem_natSyms _) _
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        hdrSyms_lowerShape_one b hd0])).mono
      (show 2 * (natSyms (prefixProd b.t 1)).length + 2 ≤ 2 * sU b from by
        rw [length_natSyms]; omega))
      ((HT.tdr_spec hI rA _ (prefixProd b.t 1) [] TermOK.nil
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (stepU (b := b) ht0))))))))))))))).of_eq ?_ (by omega)
  funext g
  by_cases g1 : g = rA
  · subst g1; simp (disch := decide) only [Function.update_self, hrA]
  by_cases g2 : g = rSH
  · subst g2; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrSH]
  by_cases g3 : g = rq
  · subst g3; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrq]
  by_cases g4 : g = rPq
  · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrPq]
  by_cases g5 : g = rNmu
  · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrN]
  by_cases g6 : g = rZero
  · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrZ]
  by_cases g7 : g = rPW1
  · subst g7; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrPW1]
  by_cases g8 : g = rPW
  · subst g8; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrPW]
  by_cases g9 : g = rLn
  · subst g9; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrLn]
  by_cases g10 : g = rPi
  · subst g10; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrPi]
  by_cases g11 : g = rPC
  · subst g11; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrPC]
  by_cases g12 : g = rB
  · subst g12; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrB]
  by_cases g13 : g = rW
  · subst g13; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrW]
  by_cases g14 : g = rP
  · subst g14; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hrP]
  simp only [parSt, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6,
    Function.update_of_ne g7, Function.update_of_ne g8, Function.update_of_ne g9,
    Function.update_of_ne g10, Function.update_of_ne g11, Function.update_of_ne g12,
    Function.update_of_ne g13, Function.update_of_ne g14]

end Specs

end SubNLogN.Machine.Tables.SetupAux

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables.SetupAux

theorem setupCost_facts (C KM : ℕ) (b : BrPar) :
    C * sU b ≤ (C + 1) * (KM + 1) * sU b ∧ C * (KM * sU b) ≤ (C + 1) * (KM + 1) * sU b ∧
      sU b ≤ (C + 1) * (KM + 1) * sU b ∧
      500 * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1) =
        500 * ((C + 1) * (KM + 1) * sU b) := by
  refine ⟨Nat.mul_le_mul_right _ (le_trans (Nat.le_succ C)
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos KM))), ?_,
    Nat.le_mul_of_pos_left _ (by positivity), by unfold sU; ring⟩
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_succ C) (Nat.le_succ KM))

/-- **Parameter setup and cleanup** (`SetupStmt`): `setupP` / `cleanP` with `K = 500`. -/
theorem setup_holds : SetupStmt := by
  refine ⟨500, fun I Mul C KM hI hMul =>
    ⟨setupP I, cleanP I, setupP_closed I, cleanP_closed I, ?_, ?_⟩⟩
  · intro b rpar B hd _ hP hB0
    obtain ⟨hX1, hX2, hX3, e⟩ := setupCost_facts C KM b
    rw [e]
    exact (HT.seq (HT.setupA_spec hI b rpar B hd hP hB0 [])
      (HT.seq (HT.setupB1_spec hI b B hB0 [])
      (HT.seq (HT.setupB2_spec hI b B hB0 [])
      (HT.seq (HT.setupC_spec hI hMul b B hB0 [])
      (HT.seq (HT.setupD1_spec hI b B hB0 [])
        (HT.setupD2_spec hI b B hB0 [])))))).of_eq (stD2_eq b B hd hB0) (by omega)
  · intro b B hd _ hB0
    obtain ⟨hX1, hX2, hX3, e⟩ := setupCost_facts C KM b
    rw [e]
    exact (HT.cleanP_spec hI b B hd hB0 []).mono (by omega)

end SubNLogN.Machine.Tables
