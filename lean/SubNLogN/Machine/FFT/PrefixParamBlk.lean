/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixParamHdr
import SubNLogN.Machine.FFT.PrefixParamSpec

/-!
# K4-PREFIX parameter phase: the blocks of the kernel (`Machine/FFT/PrefixParamBlk.lean`)

**Scope (honest summary).** The concrete stack layout of the parameter phase
(`PrefixParamStmt`, `Machine/FFT/PrefixParamSpec.lean`: named stacks `Fin 6`, private scratch
`Fin 23`, registers `Option Sym × Unit`) and the blocks of its program with exact `Runs` lemmas:
`uBlk` (`v` copied, `D, ℓ, K, v` to unary), `zBlk` (`ℓ - (v + 1)`), `brBlk` (`PrefixAux.pfY ℓ K v` and the
pass counter, by cases on `v + 1 = ℓ`), `mulBlk` (`2^{D·PrefixAux.pfY}` marks onto stack `2`), `wBlk`
(`natSyms (w + D)` onto stack `4`), `clBlk` (cleanup). Proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixParamAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF
  SubNLogN.Machine.FFT.TwiddleAux SubNLogN.Math.Walsh

/-- Stacks of the parameter phase. -/
abbrev PL : Type := KLoc (Fin 6) (Fin 23)

/-- Registers. -/
abbrev PR : Type := Option Sym × Unit

/-- Register lens. -/
abbrev lP : Lens PR (Option Sym) := Lens.fst _ _

abbrev nH : PL := .inl 0
abbrev nV : PL := .inl 1
abbrev nO2 : PL := .inl 2
abbrev nO3 : PL := .inl 3
abbrev nO4 : PL := .inl 4
abbrev nO5 : PL := .inl 5
abbrev sPK : PL := .inr 0
abbrev sTC : PL := .inr 1
abbrev sBD : PL := .inr 2
abbrev sBL : PL := .inr 3
abbrev sBK : PL := .inr 4
abbrev sBW : PL := .inr 5
abbrev sBV : PL := .inr 6
abbrev sUD : PL := .inr 7
abbrev sUL : PL := .inr 8
abbrev sUK : PL := .inr 9
abbrev sUV : PL := .inr 10
abbrev sZ : PL := .inr 11
abbrev sT : PL := .inr 12
abbrev sT2 : PL := .inr 13
abbrev sX : PL := .inr 14
abbrev sC : PL := .inr 15
abbrev sR : PL := .inr 16
abbrev sY : PL := .inr 17
abbrev sDc : PL := .inr 18
abbrev sF : PL := .inr 19
abbrev sAX : PL := .inr 20
abbrev sP : PL := .inr 21
abbrev sE : PL := .inr 22

/-- `v` copied, `D, ℓ, K, v` to unary. -/
def uBlk : Prog PL (fun _ => Sym) PR :=
  .seq (copyBits lP nV sBV sTC) (.seq (toUnary lP sBD sUD sTC) (.seq (toUnary lP sBL sUL sTC)
    (.seq (toUnary lP sBK sUK sTC) (toUnary lP sBV sUV sTC))))

/-- `Z := ℓ - (v + 1)`. -/
def zBlk : Prog PL (fun _ => Sym) PR :=
  .seq (uCopy lP sUL sZ sT) (.seq (uCopy lP sUV sT2 sT) (.seq (pushK sT2 .mark)
    (monus lP sT2 sZ)))

/-- Case `v + 1 < ℓ` (so `v < b₀`): `Y := ℓ - 1 - b₀ + v`, counter `2^D - 1` onto stack `3`. -/
def neBlk : Prog PL (fun _ => Sym) PR :=
  .seq (drain lP sZ) (.seq (uCopy lP sUL sX sT) (.seq (popO lP sX) (.seq (uCopy lP sUK sC sT)
  (.seq (cycMod lP sX sC sR) (.seq (uCopy lP sUL sY sT) (.seq (popO lP sY)
  (.seq (monus lP sR sY) (.seq (uCopy lP sUV sY sT) (.seq (drain lP sC)
  (.seq (uCopy lP sUD sDc sT) (.seq (pow2m1 lP sDc sF sAX)
    (movePrefix lP sF nO3 Option.isSome))))))))))))

/-- Case `v + 1 = ℓ`: `Y := ℓ - 1`. -/
def eBlk : Prog PL (fun _ => Sym) PR := .seq (uCopy lP sUL sY sT) (popO lP sY)

/-- The case split on `Z = ℓ - (v + 1)`. -/
def brBlk : Prog PL (fun _ => Sym) PR :=
  .seq (peekO lP sZ) (.ite (fun v => (lP.get v).isSome) neBlk eBlk)

/-- `2^{D·Y}` marks onto stack `2`. -/
def mulBlk : Prog PL (fun _ => Sym) PR :=
  .seq (uCopy lP sUD sDc sT) (.seq (mulU lP sDc sY sP sT) (.seq (pow2m1 lP sP sE sAX)
    (.seq (pushK sE .mark) (movePrefix lP sE nO2 Option.isSome))))

/-- `natSyms (w + D)` onto stack `4`. -/
def wBlk : Prog PL (fun _ => Sym) PR :=
  .seq (uCopy lP sUD sDc sT) (.seq (incLoop lP sDc sBW sTC) (.seq (copyBits lP sBW nO4 sTC)
    (drain lP sBW)))

/-- Cleanup. -/
def clBlk : Prog PL (fun _ => Sym) PR :=
  .seq (drain lP sUD) (.seq (drain lP sUL) (.seq (drain lP sUK) (.seq (drain lP sUV)
    (drain lP sY))))

/-- **The parameter-phase program.** -/
def prmProg : Prog PL (fun _ => Sym) PR :=
  .seq (prmHdr lP nH sPK sTC sBD sBL sBK sBW nO5) (.seq uBlk (.seq zBlk (.seq brBlk
    (.seq mulBlk (.seq wBlk clBlk)))))

theorem closed_prmProg : prmProg.Closed := by
  refine ⟨closed_prmHdr lP _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨closed_copyBits lP _ _ _, closed_toUnary lP _ _ _, closed_toUnary lP _ _ _,
      closed_toUnary lP _ _ _, closed_toUnary lP _ _ _⟩
  · exact ⟨closed_uCopy lP _ _ _, closed_uCopy lP _ _ _, closed_pushK _ _, closed_monus lP _ _⟩
  · refine ⟨closed_peekO lP _, ?_, ?_⟩
    · exact ⟨closed_drain lP _, closed_uCopy lP _ _ _, closed_popO lP _, closed_uCopy lP _ _ _,
        closed_cycMod lP _ _ _, closed_uCopy lP _ _ _, closed_popO lP _, closed_monus lP _ _,
        closed_uCopy lP _ _ _, closed_drain lP _, closed_uCopy lP _ _ _, closed_pow2m1 lP _ _ _,
        closed_movePrefix lP _ _ _⟩
    · exact ⟨closed_uCopy lP _ _ _, closed_popO lP _⟩
  · exact ⟨closed_uCopy lP _ _ _, closed_mulU lP _ _ _ _, closed_pow2m1 lP _ _ _,
      closed_pushK _ _, closed_movePrefix lP _ _ _⟩
  · exact ⟨closed_uCopy lP _ _ _, closed_incLoop lP _ _ _, closed_copyBits lP _ _ _,
      closed_drain lP _⟩
  · exact ⟨closed_drain lP _, closed_drain lP _, closed_drain lP _, closed_drain lP _,
      closed_drain lP _⟩

/-! ## Small wrappers with closed-form costs -/

section Wrap

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

theorem runs_drainU (k : K) (S : K → List Sym) (n : ℕ) (h : S k = List.replicate n .mark) :
    Runs (drain lO k) S (Function.update S k []) (fun _ => True) (3 * n + 2) := by
  have e := runs_drain lO k S
  rw [h, List.length_replicate] at e
  exact e

theorem runs_drainN (k : K) (S : K → List Sym) (n : ℕ) (h : S k = natSyms n) :
    Runs (drain lO k) S (Function.update S k []) (fun _ => True) (3 * bitLen n + 2) := by
  have e := runs_drain lO k S
  rw [h, length_natSyms] at e
  exact e

theorem runs_popU (k : K) (S : K → List Sym) (n : ℕ) (h : S k = List.replicate n .mark) :
    Runs (popO lO k) S (Function.update S k (List.replicate (n - 1) .mark)) (fun _ => True) 1 := by
  have e := runs_popO lO k S
  rw [h, List.tail_replicate] at e
  exact runs_mono e (fun _ _ => trivial) le_rfl

end Wrap

/-! ## The blocks -/

theorem runs_uBlk (S : PL → List Sym) (v D ℓ Kp : ℕ) (crest : List Sym) (hcrest : TermOK crest)
    (hV : S nV = natSyms v ++ crest) (hTC : S sTC = []) (hBD : S sBD = natSyms D)
    (hBL : S sBL = natSyms ℓ) (hBK : S sBK = natSyms Kp) (hBV : S sBV = []) (hUD : S sUD = [])
    (hUL : S sUL = []) (hUK : S sUK = []) (hUV : S sUV = []) :
    Runs uBlk S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S sBD []) sBL []) sBK []) sUD (List.replicate D .mark))
        sUL (List.replicate ℓ .mark)) sUK (List.replicate Kp .mark)) sUV
        (List.replicate v .mark))
      (fun _ => True)
      (9 * bitLen v + 4 + (D * (6 * bitLen D + 11) + 2 + (ℓ * (6 * bitLen ℓ + 11) + 2 +
        (Kp * (6 * bitLen Kp + 11) + 2 + (v * (6 * bitLen v + 11) + 2))))) := by
  refine runs_congr (runs_seq' (runs_copyNat lP (by decide) (by decide) (by decide) S v crest hV
      hcrest (hTC ▸ termOK_nil'))
    (runs_seq' (runs_toUnary lP (by decide) (by decide) _ D [] termOK_nil'
      (by simp [hBD]))
    (runs_seq' (runs_toUnary lP (by decide) (by decide) _ ℓ [] termOK_nil'
      (by simp [hBL]))
    (runs_seq' (runs_toUnary lP (by decide) (by decide) _ Kp [] termOK_nil'
      (by simp [hBK]))
      (runs_toUnary lP (by decide) (by decide) _ v [] termOK_nil'
        (by simp [hBV])))))) ?_
  funext x
  simp +decide only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_zBlk (S : PL → List Sym) (v ℓ : ℕ) (hUL : S sUL = List.replicate ℓ .mark)
    (hUV : S sUV = List.replicate v .mark) (hZ : S sZ = []) (hT : S sT = []) (hT2 : S sT2 = []) :
    Runs zBlk S (Function.update S sZ (List.replicate (ℓ - (v + 1)) .mark)) (fun _ => True)
      (9 * ℓ + 4 + (9 * v + 4 + (1 + ((v + 1) * 4 + 2)))) := by
  refine runs_congr (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) S ℓ hUL hT)
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ v
      (by simp [hUV]) (by simp [hT]))
    (runs_seq' (runs_pushK (σ := PR) sT2 .mark _)
      (runs_monus lP (by decide) _ (v + 1) ℓ
        (by simp [hT2, List.replicate_succ])
        (by simp [hZ]))))) ?_
  funext x
  simp +decide only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_eBlk (S : PL → List Sym) (ℓ : ℕ) (hUL : S sUL = List.replicate ℓ .mark)
    (hY : S sY = []) (hT : S sT = []) :
    Runs eBlk S (Function.update S sY (List.replicate (ℓ - 1) .mark)) (fun _ => True)
      (9 * ℓ + 4 + 1) := by
  refine runs_congr (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) S ℓ hUL hT)
    (runs_popU lP sY _ ℓ (by simp [hY]))) (Function.update_idem _ _ _)

/-- Cost bound of `neBlk`. -/
def neCost (ℓ Kp v D : ℕ) : ℕ :=
  ℓ * (4 * Kp + 11) + D * (13 * 2 ^ D + 12) + 4 * 2 ^ D + 25 * ℓ + 12 * Kp + 9 * v + 9 * D + 40

theorem runs_neBlk (S : PL → List Sym) (v ℓ Kp D : ℕ) (hKp : 0 < Kp)
    (hZ : S sZ = List.replicate (ℓ - (v + 1)) .mark) (hUL : S sUL = List.replicate ℓ .mark)
    (hUK : S sUK = List.replicate Kp .mark) (hUV : S sUV = List.replicate v .mark)
    (hUD : S sUD = List.replicate D .mark) (hX : S sX = []) (hC : S sC = []) (hR : S sR = [])
    (hY : S sY = []) (hDc : S sDc = []) (hF : S sF = []) (hAX : S sAX = []) (hT : S sT = []) :
    Runs neBlk S
      (Function.update (Function.update (Function.update S sZ []) sY
        (List.replicate (v + (ℓ - 1 - (ℓ - 1) % Kp)) .mark)) nO3
        (List.replicate (2 ^ D - 1) .mark ++ S nO3))
      (fun _ => True) (neCost ℓ Kp v D) := by
  refine runs_congr (runs_mono (runs_seq' (runs_drainU lP sZ S _ hZ)
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ ℓ
      (by simp [hUL]) (by simp [hT]))
    (runs_seq' (runs_popU lP sX _ ℓ (by simp [hX]))
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ Kp
      (by simp [hUK]) (by simp [hT]))
    (runs_seq' (runs_cycMod lP (by decide) _ (ℓ - 1) Kp hKp (by simp)
      (by simp [hC]) (by simp [hR]))
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ ℓ
      (by simp [hUL]) (by simp [hT]))
    (runs_seq' (runs_popU lP sY _ ℓ (by simp [hY]))
    (runs_seq' (runs_monus lP (by decide) _ ((ℓ - 1) % Kp) (ℓ - 1)
      (by simp) (by simp))
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ v
      (by simp [hUV]) (by simp [hT]))
    (runs_seq' (runs_drainU lP sC _ (Kp - (ℓ - 1) % Kp) (by simp))
    (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) _ D
      (by simp [hUD]) (by simp [hT]))
    (runs_seq' (runs_pow2m1 lP (by decide) _ D (by simp [hDc])
      (by simp [hF]) (by simp [hAX]))
      (runs_uMove lP (by decide) _ (2 ^ D - 1) (by simp))))))))))))))
    (fun _ _ => trivial) ?_) ?_
  · have h1 : (ℓ - 1) * (4 * Kp + 11) ≤ ℓ * (4 * Kp + 11) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (ℓ - 1) % Kp ≤ ℓ - 1 := Nat.mod_le _ _
    have h3 : 2 ^ D - 1 ≤ 2 ^ D := Nat.sub_le _ _
    unfold neCost
    omega
  · funext x
    simp +decide only [Function.update_apply]
    split_ifs <;> simp_all

theorem runs_brBlk (S : PL → List Sym) (v ℓ Kp D : ℕ) (hKp : 0 < Kp) (hv : v < ℓ)
    (hZ : S sZ = List.replicate (ℓ - (v + 1)) .mark) (hUL : S sUL = List.replicate ℓ .mark)
    (hUK : S sUK = List.replicate Kp .mark) (hUV : S sUV = List.replicate v .mark)
    (hUD : S sUD = List.replicate D .mark) (hX : S sX = []) (hC : S sC = []) (hR : S sR = [])
    (hY : S sY = []) (hDc : S sDc = []) (hF : S sF = []) (hAX : S sAX = []) (hT : S sT = []) :
    Runs brBlk S
      (Function.update (Function.update (Function.update S sZ []) sY
        (List.replicate (PrefixAux.pfY ℓ Kp v) .mark)) nO3
        (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark ++ S nO3))
      (fun _ => True) (1 + (neCost ℓ Kp v D + (9 * ℓ + 4 + 1) + 1)) := by
  by_cases hcase : v + 1 = ℓ
  · have hZ0 : S sZ = [] := by simp [hZ, show ℓ - (v + 1) = 0 by omega]
    have e := runs_seq_ite_f (p := neBlk) (q := eBlk) (runs_peekO lP sZ S)
      (fun r hr => by
        have hr' : lP.get r = (S sZ).head? := hr
        show (lP.get r).isSome = false
        rw [hr', hZ0]
        try rfl)
      (runs_eBlk S ℓ hUL hY hT)
    refine runs_congr (runs_mono e (fun _ _ => trivial) (by omega)) ?_
    have hpf : PrefixAux.pfY ℓ Kp v = ℓ - 1 := by simp [PrefixAux.pfY, hcase]
    rw [hpf, if_pos hcase]
    funext x
    simp +decide only [Function.update_apply]
    split_ifs <;> simp_all
  · have hlt : v + 1 < ℓ := by omega
    have e := runs_seq_ite_t (p := neBlk) (q := eBlk) (runs_peekO lP sZ S)
      (fun r hr => by
        have hr' : lP.get r = (S sZ).head? := hr
        show (lP.get r).isSome = true
        rw [hr', hZ]
        obtain ⟨c, hc⟩ : ∃ c, ℓ - (v + 1) = c + 1 := ⟨ℓ - (v + 1) - 1, by omega⟩
        rw [hc, List.replicate_succ]
        try rfl)
      (runs_neBlk S v ℓ Kp D hKp hZ hUL hUK hUV hUD hX hC hR hY hDc hF hAX hT)
    refine runs_congr (runs_mono e (fun _ _ => trivial) (by omega)) ?_
    have hpf : PrefixAux.pfY ℓ Kp v = v + (ℓ - 1 - (ℓ - 1) % Kp) := by
      simp only [PrefixAux.pfY, hcase, if_false, layoutB0]
      omega
    rw [hpf, if_neg hcase]

theorem runs_mulBlk (S : PL → List Sym) (D y : ℕ) (hUD : S sUD = List.replicate D .mark)
    (hY : S sY = List.replicate y .mark) (hDc : S sDc = []) (hP : S sP = []) (hE : S sE = [])
    (hAX : S sAX = []) (hT : S sT = []) :
    Runs mulBlk S (Function.update S nO2 (List.replicate (2 ^ (D * y)) .mark ++ S nO2))
      (fun _ => True)
      (9 * D + 4 + (D * (9 * y + 7) + 2 + (D * y * (13 * 2 ^ (D * y) + 12) + 2 +
        (1 + (4 * 2 ^ (D * y) + 2))))) := by
  have hrep : Sym.mark :: List.replicate (2 ^ (D * y) - 1) .mark =
      List.replicate (2 ^ (D * y)) .mark := by
    have h1 : 1 ≤ 2 ^ (D * y) := Nat.one_le_two_pow
    rw [← List.replicate_succ]
    congr 1
    omega
  refine runs_congr (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) S D hUD hT)
    (runs_seq' (runs_mulU lP (by decide) _ D y (by simp [hDc])
      (by simp [hY]) (by simp [hP])
      (by simp [hT]))
    (runs_seq' (runs_pow2m1 lP (by decide) _ (D * y) (by simp)
      (by simp [hE]) (by simp [hAX]))
    (runs_seq' (runs_pushK (σ := PR) sE .mark _)
      (runs_uMove lP (by decide) _ (2 ^ (D * y)) (by simp [hrep])))))) ?_
  funext x
  simp +decide only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_wBlk (S : PL → List Sym) (D w : ℕ) (hUD : S sUD = List.replicate D .mark)
    (hBW : S sBW = natSyms w) (hDc : S sDc = []) (hT : S sT = []) (hTC : S sTC = []) :
    Runs wBlk S (Function.update (Function.update S sBW []) nO4 (natSyms (w + D) ++ S nO4))
      (fun _ => True)
      (9 * D + 4 + (D * (6 * bitLen (w + D) + 12) + 2 + (9 * bitLen (w + D) + 4 +
        (3 * bitLen (w + D) + 2)))) := by
  refine runs_congr (runs_seq' (runs_uCopy lP (by decide) (by decide) (by decide) S D hUD hT)
    (runs_seq' (runs_incLoop lP (by decide) _ D w (by simp [hDc])
      (by simp [hBW]))
    (runs_seq' (runs_copyNat lP (by decide) (by decide) (by decide) _ (w + D) []
      (by simp) termOK_nil'
      (by simp only [Function.update_apply]; simp +decide [hTC]; exact termOK_nil'))
      (runs_drainN lP sBW _ (w + D) (by simp))))) ?_
  funext x
  simp +decide only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_clBlk (S : PL → List Sym) (D ℓ Kp v y : ℕ) (hUD : S sUD = List.replicate D .mark)
    (hUL : S sUL = List.replicate ℓ .mark) (hUK : S sUK = List.replicate Kp .mark)
    (hUV : S sUV = List.replicate v .mark) (hY : S sY = List.replicate y .mark) :
    Runs clBlk S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        sUD []) sUL []) sUK []) sUV []) sY [])
      (fun _ => True) (3 * D + 2 + (3 * ℓ + 2 + (3 * Kp + 2 + (3 * v + 2 + (3 * y + 2))))) :=
  runs_seq' (runs_drainU lP sUD S D hUD)
    (runs_seq' (runs_drainU lP sUL _ ℓ (by simp [hUL]))
    (runs_seq' (runs_drainU lP sUK _ Kp (by simp [hUK]))
    (runs_seq' (runs_drainU lP sUV _ v (by simp [hUV]))
      (runs_drainU lP sY _ y (by simp [hY])))))

end SubNLogN.Machine.FFT.PrefixParamAux
