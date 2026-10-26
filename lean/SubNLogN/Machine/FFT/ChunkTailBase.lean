/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutHdr
import SubNLogN.Machine.FFT.PhaseBase
import SubNLogN.Math.Walsh.Proofs.LayoutPerm
import WP.Inst.W6a

/-!
# K4.5a (`Machine/FFT/ChunkTailBase.lean`): tools for the tail of a chunk round's slice header

A chunk round `v` (`b₀ ≤ v ≤ ℓ - 2`) calls the layer on the slice header
`sliceHdr q (D+1) 2^ℓ w K m₀ j₀ D nS ρ = permHdr q (D+1) 2^ℓ w K m₀ ++ hdrSyms [j₀, D, nS, ρ]`.
The first six fields are the descriptor header of `PermHdrGenStmt` (proved in
`Machine/FFT/LayoutHdr.lean`). This file and `Machine/FFT/ChunkTail.lean` build the last four.

**Scope (honest summary).** Proved here (no `sorry`), in the namespace
`SubNLogN.Machine.FFT.ChunkAux`:
* the host of the tail builder (`CL = Loc 4 13`, the W3/W6a instances `CI`, the wrapper programs,
  the state function `stC` and its update lemmas, the host rules of the wrappers);
* the closed forms of the tail (`chunk_identity`): with `u = v - b₀`,
  `roundJ0 ℓ K a v + D·K + D·(u - u mod K) = m₀`, so `nS = D·(u - u mod K)`,
  `j₀ = m₀ - D·K - nS` and `ρ = u mod K` (Lemma 6.3, `lem:walsh-layout`; using `a_i ∈ {ℓ-1, ℓ}`).
-/

namespace SubNLogN.Machine.FFT.ChunkAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.Phase (SpecSubNat)

/-! ## 1. Arithmetic of the tail fields -/

/-- The chunk index: `⌊(ℓ-2-v)/K⌋ + 1 + ⌊(v-b₀)/K⌋ = J_blk` for `b₀ ≤ v ≤ ℓ - 2`. -/
theorem jblk_eq (ℓ K v : ℕ) (hK : 0 < K) (hb : (ℓ - 1) % K ≤ v) (hv : v + 2 ≤ ℓ) :
    (ℓ - 2 - v) / K + 1 + (v - (ℓ - 1) % K) / K = (ℓ - 1) / K := by
  have h1 : K * ((ℓ - 1) / K) + (ℓ - 1) % K = ℓ - 1 := Nat.div_add_mod _ _
  have h2 : K * ((v - (ℓ - 1) % K) / K) + (v - (ℓ - 1) % K) % K = v - (ℓ - 1) % K :=
    Nat.div_add_mod _ _
  have h3 : K * ((ℓ - 2 - v) / K) + (ℓ - 2 - v) % K = ℓ - 2 - v := Nat.div_add_mod _ _
  have hρ : (v - (ℓ - 1) % K) % K < K := Nat.mod_lt _ hK
  have hρ' : (ℓ - 2 - v) % K < K := Nat.mod_lt _ hK
  generalize (v - (ℓ - 1) % K) % K = ρ at h2 hρ
  generalize (ℓ - 2 - v) % K = ρ' at h3 hρ'
  generalize (ℓ - 1) / K = J at h1 ⊢
  generalize (v - (ℓ - 1) % K) / K = g at h2 ⊢
  generalize (ℓ - 2 - v) / K = c at h3 ⊢
  generalize (ℓ - 1) % K = b at h1 h2 hb
  have key : K * (c + g) + (ρ' + ρ + 1) = K * J := by rw [Nat.mul_add]; omega
  have hlt1 : K * (c + g) < K * J := by omega
  have hlt2 : K * J < K * (c + g + 2) := by
    rw [show K * (c + g + 2) = K * (c + g) + 2 * K by ring]; omega
  have e1 := Nat.lt_of_mul_lt_mul_left hlt1
  have e2 := Nat.lt_of_mul_lt_mul_left hlt2
  omega

/-- **Closed form of the tail** (`u = v - b₀`): `j₀ + D·K + D·(u - u mod K) = m₀`. -/
theorem chunk_identity {D q ℓ K w v : ℕ} {a : Fin D → ℕ} (hsh : MidShapeOK q ℓ K w a)
    (hc : IsChunkRound ℓ K v) :
    roundJ0 ℓ K a v + D * K + D * ((v - (ℓ - 1) % K) - (v - (ℓ - 1) % K) % K) = addrBits a := by
  obtain ⟨-, -, hℓ2, -, -, -, ha, -⟩ := hsh
  obtain ⟨hK0, hb, hv⟩ := hc
  have hA := LayoutPermAux.addrBits_eq ℓ a (by omega) ha
  have hP := LayoutPermAux.prefixLen_eq ℓ K a
  have hJ := jblk_eq ℓ K v hK0 hb hv
  have h1 : K * ((ℓ - 1) / K) + (ℓ - 1) % K = ℓ - 1 := Nat.div_add_mod _ _
  have h2 : K * ((v - (ℓ - 1) % K) / K) + (v - (ℓ - 1) % K) % K = v - (ℓ - 1) % K :=
    Nat.div_add_mod _ _
  have hu : (v - (ℓ - 1) % K) - (v - (ℓ - 1) % K) % K = K * ((v - (ℓ - 1) % K) / K) := by
    clear h1 hJ hA hP
    generalize (v - (ℓ - 1) % K) % K = ρ at h2 ⊢
    generalize (v - (ℓ - 1) % K) / K = g at h2 ⊢
    generalize v - (ℓ - 1) % K = u at h2 ⊢
    omega
  have hB0 : layoutB0 ℓ K = (ℓ - 1) % K := rfl
  unfold roundJ0
  rw [hA, hP, hu, hB0]
  have e1 : D * (ℓ - 1) = D * (K * ((ℓ - 1) / K) + (ℓ - 1) % K) := by rw [h1]
  rw [e1, ← hJ]
  ring

theorem le_addrBits_D {D q ℓ K w : ℕ} {a : Fin D → ℕ} (hsh : MidShapeOK q ℓ K w a) :
    D ≤ addrBits a := by
  obtain ⟨-, -, hℓ2, -, -, -, ha, -⟩ := hsh
  have hA := LayoutPermAux.addrBits_eq ℓ a (by omega) ha
  have : D * 1 ≤ D * (ℓ - 1) := Nat.mul_le_mul_left _ (by omega)
  omega


/-! ## 2. The host -/

/-- The builder's stacks: named `.inl 0` (the header `midHdr`, restored), `.inl 1` (the round
index, restored), `.inl 2` (the descriptor header `permHdr`, consumed), `.inl 3` (the
destination); thirteen scratch stacks `.inr 0 … 12`. -/
abbrev CL := Loc 4 13

/-- Shift a lens one product component to the right. -/
def lsc {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- The contract instances used by the builder. -/
structure CI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sb : Inst 3 4 Unit
  dm : Inst 4 6 Unit

namespace CI

variable (I : CI)

/-- Host registers: one register file per instance. -/
abbrev R : Type := I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ad.R × I.sb.R × I.dm.R

def lcp : Lens I.R I.cp.R := Lens.fst _ _
def ldr : Lens I.R I.dr.R := lsc (Lens.fst _ _)
def liz : Lens I.R I.iz.R := lsc (lsc (Lens.fst _ _))
def ldc : Lens I.R I.dc.R := lsc (lsc (lsc (Lens.fst _ _)))
def lad : Lens I.R I.ad.R := lsc (lsc (lsc (lsc (Lens.fst _ _))))
def lsb : Lens I.R I.sb.R := lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))
def ldm : Lens I.R I.dm.R := lsc (lsc (lsc (lsc (lsc (Lens.snd _ _)))))

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ad.fin
  have := I.sb.fin; have := I.dm.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ad.ne
  have := I.sb.ne; have := I.dm.ne
  infer_instance

/-- All contract bodies with one shared constant. -/
structure Spec (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ad : SpecAddNat I.ad C
  sb : SpecSubNat I.sb C
  dm : SpecDivMod I.dm C

end CI

/-- Builder programs. -/
abbrev HP (I : CI) : Type := Prog CL (fun _ => Sym) I.R

/-! ### Stack names -/

abbrev sH : CL := .inl 0
abbrev sV : CL := .inl 1
abbrev sT : CL := .inl 2
abbrev sP : CL := .inl 3
abbrev vD : CL := .inr 0
abbrev vl : CL := .inr 1
abbrev vK : CL := .inr 2
abbrev vm : CL := .inr 3
abbrev b0 : CL := .inr 4
abbrev vu : CL := .inr 5
abbrev rr : CL := .inr 6
abbrev vt : CL := .inr 7
abbrev cnt : CL := .inr 8
abbrev a1 : CL := .inr 9
abbrev a2 : CL := .inr 10
abbrev tm : CL := .inr 11
abbrev j0 : CL := .inr 12
/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev d0 : CL := .inl 0

section Wrappers

variable (I : CI)

def hcp (x y : CL) : HP I := callI I.cp [x, y] d0 I.lcp
def hdr (x : CL) : HP I := callI I.dr [x] d0 I.ldr
def hdc (x : CL) : HP I := callI I.dc [x] d0 I.ldc
def had (x y z : CL) : HP I := callI I.ad [x, y, z] d0 I.lad
def hsb (x y z : CL) : HP I := callI I.sb [x, y, z] d0 I.lsb
def hdm (x y z u : CL) : HP I := callI I.dm [x, y, z, u] d0 I.ldm
/-- Count-down loop on `c` (`while c ≠ 0 do (dec c; body)`). -/
def hcd (c : CL) (body : HP I) : HP I := cdLoop I.iz I.dc I.liz I.ldc c d0 body

/-- Loop body: `a1 += t`, `a2 += K` (each through the temporary `tm`). -/
def body : HP I :=
  (had I a1 vt tm).seq
    ((hdr I a1).seq
    ((hcp I tm a1).seq
    ((hdr I tm).seq
    ((had I a2 vK tm).seq
    ((hdr I a2).seq
    ((hcp I tm a2).seq (hdr I tm)))))))

/-- Block A: read `q, D, ℓ` from the middle header (copy, drop, pop the `mark`), restore the
three fields, drop `q`: afterwards `vD = D`, `vl = ℓ`. -/
def blkA : HP I :=
  (hcp I sH tm).seq
    ((hdr I sH).seq
    ((popS sH).seq
    ((hcp I sH vD).seq
    ((hdr I sH).seq
    ((popS sH).seq
    ((hcp I sH vl).seq
    ((hdr I sH).seq
    ((popS sH).seq
    ((pushS sH Sym.mark).seq
    ((hcp I vl sH).seq
    ((pushS sH Sym.mark).seq
    ((hcp I vD sH).seq
    ((pushS sH Sym.mark).seq
    ((hcp I tm sH).seq (hdr I tm)))))))))))))))

/-- Block T: drop the fields `q, D+1, 2^ℓ, w` of the descriptor header, read `K`, `m₀` (consumed). -/
def blkT : HP I :=
  (hdr I sT).seq
    ((popS sT).seq
    ((hdr I sT).seq
    ((popS sT).seq
    ((hdr I sT).seq
    ((popS sT).seq
    ((hdr I sT).seq
    ((popS sT).seq
    ((hcp I sT vK).seq
    ((hdr I sT).seq
    ((popS sT).seq
    ((hcp I sT vm).seq
    ((hdr I sT).seq (popS sT)))))))))))))

/-- Block B: `b₀ = (ℓ - 1) mod K`. -/
def blkB : HP I := (hdc I vl).seq ((hdm I vl vK tm b0).seq (hdr I tm))

/-- Block C: `u = v - b₀`, `ρ = u mod K`, `t = u - ρ`. -/
def blkC : HP I :=
  (hsb I sV b0 vu).seq ((hdm I vu vK tm rr).seq ((hdr I tm).seq (hsb I vu rr vt)))

/-- Block F: `a1 = D·t`, `a2 = D·K` by a loop of `D` iterations. -/
def blkF : HP I := (hcp I vD cnt).seq (hcd I cnt (body I))

/-- Block G: `j₀ = m₀ - D·K - D·t`. -/
def blkG : HP I := (hsb I vm a2 tm).seq ((hsb I tm a1 j0).seq (hdr I tm))

/-- Block H: push the fields `ρ`, `nS = D·t`, `D`, `j₀` onto the destination. -/
def blkH : HP I :=
  (pushS sP Sym.mark).seq
    ((hcp I rr sP).seq
    ((pushS sP Sym.mark).seq
    ((hcp I a1 sP).seq
    ((pushS sP Sym.mark).seq
    ((hcp I vD sP).seq
    ((pushS sP Sym.mark).seq (hcp I j0 sP)))))))

/-- Block I: drop the scratch numbers. -/
def blkI : HP I :=
  (hdr I vD).seq ((hdr I vl).seq ((hdr I vK).seq ((hdr I vm).seq ((hdr I b0).seq ((hdr I vu).seq
    ((hdr I rr).seq ((hdr I vt).seq ((hdr I a1).seq ((hdr I a2).seq (hdr I j0))))))))))

/-- **The tail builder.** -/
def tailProg : HP I :=
  (blkA I).seq ((blkT I).seq ((blkB I).seq ((blkC I).seq ((blkF I).seq ((blkG I).seq
    ((blkH I).seq (blkI I)))))))

theorem tailProg_closed : (tailProg I).Closed := by
  unfold tailProg blkA blkT blkB blkC blkF blkG blkH blkI hcd body hcp hdr hdc had hsb hdm
  repeat' (first
    | exact callI_closed _ _ _ _
    | exact trivial
    | refine cdLoop_closed _ _ _ _ _ _ _ ?_
    | refine WP.W9comp.closed_seq ?_ ?_)

end Wrappers


/-! ## 3. States -/

/-- The builder's state, one argument per stack. -/
def stC (h v t p d l k m b u r x c e1 e2 f j : List Sym) : CL → List Sym
  | .inl i => if (i : ℕ) = 0 then h else if (i : ℕ) = 1 then v else if (i : ℕ) = 2 then t else p
  | .inr i => if (i : ℕ) = 0 then d else if (i : ℕ) = 1 then l else if (i : ℕ) = 2 then k
      else if (i : ℕ) = 3 then m else if (i : ℕ) = 4 then b else if (i : ℕ) = 5 then u
      else if (i : ℕ) = 6 then r else if (i : ℕ) = 7 then x else if (i : ℕ) = 8 then c
      else if (i : ℕ) = 9 then e1 else if (i : ℕ) = 10 then e2 else if (i : ℕ) = 11 then f
      else j

section StC

variable (h v t p d l k m b u r x c e1 e2 f j y : List Sym)

theorem stC_upd_h :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) sH y =
      stC y v t p d l k m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_t :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) sT y =
      stC h v y p d l k m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_p :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) sP y =
      stC h v t y d l k m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_d :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vD y =
      stC h v t p y l k m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_l :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vl y =
      stC h v t p d y k m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_k :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vK y =
      stC h v t p d l y m b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_m :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vm y =
      stC h v t p d l k y b u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_b :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) b0 y =
      stC h v t p d l k m y u r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_u :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vu y =
      stC h v t p d l k m b y r x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_r :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) rr y =
      stC h v t p d l k m b u y x c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_x :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) vt y =
      stC h v t p d l k m b u r y c e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_c :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) cnt y =
      stC h v t p d l k m b u r x y e1 e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_a1 :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) a1 y =
      stC h v t p d l k m b u r x c y e2 f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_a2 :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) a2 y =
      stC h v t p d l k m b u r x c e1 y f j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_tm :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) tm y =
      stC h v t p d l k m b u r x c e1 e2 y j := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

theorem stC_upd_j :
    Function.update (stC h v t p d l k m b u r x c e1 e2 f j) j0 y =
      stC h v t p d l k m b u r x c e1 e2 f y := by
  funext z; rcases z with i | i
  · fin_cases i <;> simp [stC]
  · fin_cases i <;> simp [stC]

end StC


/-! ## 4. Host rules of the wrappers -/

section Rules

variable {I : CI} {C : ℕ}

theorem ht_cp (hI : I.Spec C) (x y : CL) (hxy : [x, y].Nodup) (B : CL → List Sym) (n : ℕ)
    (r P0 : List Sym) (hr : TermOK r) (hB : B x = natSyms n ++ r) (hy : B y = P0) :
    HT [] B (hcp I x y) (Function.update B y (natSyms n ++ P0)) (C * (bitLen n + 1)) := by
  have h := HT.copyNat hI.cp d0 I.lcp x y hxy (by decide) B n r hr hB []
  rw [hy] at h
  exact h

theorem ht_cp0 (hI : I.Spec C) (x y : CL) (hxy : [x, y].Nodup) (B : CL → List Sym) (n : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms n ++ r) (hy : B y = []) :
    HT [] B (hcp I x y) (Function.update B y (natSyms n)) (C * (bitLen n + 1)) := by
  have h := ht_cp hI x y hxy B n r [] hr hB hy
  rw [List.append_nil] at h
  exact h

theorem ht_dr (hI : I.Spec C) (x : CL) (B : CL → List Sym) (n : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms n ++ r) :
    HT [] B (hdr I x) (Function.update B x r) (C * (bitLen n + 1)) :=
  HT.dropNat hI.dr d0 I.ldr x (by decide) B n r hr hB []

theorem ht_dc (hI : I.Spec C) (x : CL) (B : CL → List Sym) (n : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms (n + 1) ++ r) :
    HT [] B (hdc I x) (Function.update B x (natSyms n ++ r))
      (C * (zerosLead (Computability.encodeNat (n + 1)) + 1)) :=
  HT.callI_upd I.dc [x] d0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
    (hI.dc n r _ hr hB) []

theorem ht_ad0 (hI : I.Spec C) (x y z : CL) (hxyz : [x, y, z].Nodup) (B : CL → List Sym)
    (n n' : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B x = natSyms n ++ rx) (hy : B y = natSyms n' ++ ry) (hz : B z = []) :
    HT [] B (had I x y z) (Function.update B z (natSyms (n + n')))
      (C * (bitLen n + bitLen n' + 1)) := by
  have h := HT.addNat hI.ad d0 I.lad x y z hxyz (by decide) B n n' rx ry hrx hry hx hy []
  rw [hz, List.append_nil] at h
  exact h

theorem ht_sb0 (hI : I.Spec C) (x y z : CL) (hxyz : [x, y, z].Nodup) (B : CL → List Sym)
    (n n' : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hle : n' ≤ n)
    (hx : B x = natSyms n ++ rx) (hy : B y = natSyms n' ++ ry) (hz : B z = []) :
    HT [] B (hsb I x y z) (Function.update B z (natSyms (n - n')))
      (C * (bitLen n + bitLen n' + 1)) := by
  have h := SubNLogN.Machine.FFT.Phase.HT.subNat hI.sb d0 I.lsb x y z hxyz (by decide) B n n' rx
    ry hrx hry hle hx hy []
  rw [hz, List.append_nil] at h
  exact h

theorem ht_dm0 (hI : I.Spec C) (x y z u : CL) (hnd : [x, y, z, u].Nodup) (B : CL → List Sym)
    (n n' : ℕ) (rx ry : List Sym) (hn' : 0 < n') (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B x = natSyms n ++ rx) (hy : B y = natSyms n' ++ ry) (hz : B z = []) (hu : B u = []) :
    HT [] B (hdm I x y z u)
      (Function.update (Function.update B z (natSyms (n / n'))) u (natSyms (n % n')))
      (C * (bitLen n * bitLen n' + bitLen n + bitLen n' + 1)) := by
  have h := HT.divModNat hI.dm d0 I.ldm x y z u hnd (by decide) B n n' rx ry hn' hrx hry hx hy []
  rw [hz, List.append_nil] at h
  rw [hu] at h
  rw [List.append_nil] at h
  exact h

theorem ht_push (k : CL) (s : Sym) (B : CL → List Sym) (P0 : List Sym) (hk : B k = P0) :
    HT (σ := I.R) [] B (pushS k s) (Function.update B k (s :: P0)) 1 := by
  have h := HT.pushS (σ := I.R) k s B []
  rw [hk] at h
  exact h

theorem ht_pop (k : CL) (B : CL → List Sym) (s : Sym) (rest : List Sym) (hk : B k = s :: rest) :
    HT (σ := I.R) [] B (popS k) (Function.update B k rest) 1 :=
  HT.popS (σ := I.R) k B s rest hk []

end Rules

/-! ## 5. Costs -/

/-- Uniform cost bound of one primitive call on numbers of bit length at most `B`. -/
def opQ (C B : ℕ) : ℕ := C * (B + 1) ^ 2 + 2 * B + 2

theorem one_le_opQ (C B : ℕ) : 1 ≤ opQ C B := by unfold opQ; omega

theorem C_le_opQ (C B : ℕ) : C ≤ opQ C B := by
  unfold opQ
  have : C * 1 ≤ C * (B + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  omega

theorem cq1 {C B n : ℕ} (hn : bitLen n ≤ B) : C * (bitLen n + 1) ≤ opQ C B := by
  unfold opQ
  have h1 : bitLen n + 1 ≤ (B + 1) ^ 2 := by nlinarith
  have : C * (bitLen n + 1) ≤ C * (B + 1) ^ 2 := Nat.mul_le_mul_left _ h1
  omega

theorem cq2 {C B n n' : ℕ} (hn : bitLen n ≤ B) (hn' : bitLen n' ≤ B) :
    C * (bitLen n + bitLen n' + 1) ≤ opQ C B := by
  unfold opQ
  have h1 : bitLen n + bitLen n' + 1 ≤ (B + 1) ^ 2 := by nlinarith
  have : C * (bitLen n + bitLen n' + 1) ≤ C * (B + 1) ^ 2 := Nat.mul_le_mul_left _ h1
  omega

theorem cqm {C B n n' : ℕ} (hn : bitLen n ≤ B) (hn' : bitLen n' ≤ B) :
    C * (bitLen n * bitLen n' + bitLen n + bitLen n' + 1) ≤ opQ C B := by
  unfold opQ
  have h1 : bitLen n * bitLen n' + bitLen n + bitLen n' + 1 ≤ (B + 1) ^ 2 := by
    have : bitLen n * bitLen n' ≤ B * B := Nat.mul_le_mul hn hn'
    nlinarith
  have : C * (bitLen n * bitLen n' + bitLen n + bitLen n' + 1) ≤ C * (B + 1) ^ 2 :=
    Nat.mul_le_mul_left _ h1
  omega

theorem cqd {C B n : ℕ} (hn : bitLen (n + 1) ≤ B) :
    C * (zerosLead (Computability.encodeNat (n + 1)) + 1) ≤ opQ C B := by
  have h : zerosLead (Computability.encodeNat (n + 1)) ≤ bitLen (n + 1) := zerosLead_le_length _
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) (cq1 hn)

theorem bitLen_le' {B n : ℕ} (h : n ≤ B) : bitLen n ≤ B :=
  (FFT.LayoutAux.bitLen_le_self n).trans h


end SubNLogN.Machine.FFT.ChunkAux
