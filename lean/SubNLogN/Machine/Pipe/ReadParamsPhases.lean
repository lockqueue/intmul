import SubNLogN.Machine.Pipe.ReadParamsOut

/-!
# Read-parameters kernel, part 3: computation and output phases

Helpers (namespace `SubNLogN.Machine.Pipe.ReadParamsAux`), stated on the register file
`regs b k i p0 pp dk l m` (all work stacks empty):
* computation: `mkP0_ms` (`p0 = 2b + 2K0 + 6`), `mkPP_ms` (`P = 2 p0 + 12 K0 + 32 bitLen
  (p0 + K0 + 1) + 256`), `mkDk_ms` (`dK = ⌊K0^(1/15)⌋`), `mkLM_ms` (`ℓ = ⌈K0/dK⌉`,
  `m = dK·ℓ - K0`);
* field preparations (`prepD`, `prepd`, `prepKK`, `prepW`, `outLin`) and the output phases
  `outWW_ms` (`win`, `wout`), `outMparA_ms`, `outMparB_ms` (middle header on `mpar`),
  `outParA_ms`, `outParB_ms`, `outParC_ms` (bridge header on `par`), and `clean_ms`;
  each with its exact final state and an explicit cost bound.
-/

namespace SubNLogN.Machine.Pipe.ReadParamsAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Machine.Pipe.GuardAux

/-! ## The register file and the computation phase -/

/-- The register file: persistent registers `B K I P0 PP Dk L Mm`, all work stacks empty. -/
def regs (b k i p0 pp dk l m : ℕ) : RE → ℕ
  | .B => b
  | .K => k
  | .I => i
  | .P0 => p0
  | .PP => pp
  | .Dk => dk
  | .L => l
  | .Mm => m
  | _ => 0

theorem ArClean_regs (b k i p0 pp dk l m : ℕ) : ArClean (regs b k i p0 pp dk l m) := by
  intro e he
  cases e <;> first | rfl | exact absurd he (by decide)

/-- `NUM := c1·a1 + c2·a2 + c3` (from `NUM = 0`). -/
def linPrep (a1 a2 : RE) (c1 c2 c3 : ℕ) : SProg RK :=
  .seq (.seq (cpN a1 .NUM .T c1) (cpN a2 .NUM .T c2)) (pushMs .NUM c3)

theorem linPrep_ms {a1 a2 : RE} (h1 : isU a1 = true) (h2 : isU a2 = true) (h1N : a1 ≠ .NUM)
    (h2N : a2 ≠ .NUM) (h1T : a1 ≠ .T) (h2T : a2 ≠ .T) (c1 c2 c3 : ℕ) (S0 : RK → List Sym)
    (R : RE → ℕ) (hN : R .NUM = 0) (hT : R .T = 0) :
    MS (linPrep a1 a2 c1 c2 c3) S0 R S0 (Function.update R .NUM (c1 * R a1 + c2 * R a2 + c3))
      (c1 * (9 * R a1 + 4) + c2 * (9 * R a2 + 4) + c3 + 3) := by
  have h := ((cpN_ms h1 rfl rfl h1N h1T (by decide) S0 c1 R hT).seq
    (cpN_ms h2 rfl rfl h2N h2T (by decide) S0 c2 _
      (by rw [Function.update_of_ne (by decide)]; exact hT))).seq
    (pushMs_ms (a := .NUM) rfl S0 c3 _)
  simp only [Function.update_self, Function.update_idem, Function.update_of_ne h2N, hN] at h
  refine (h.mono (le_of_eq (by ring))).of_eq rfl ?_
  congr 1
  ring

/-- `P0 := 2B + 2K + 6`, `B := 0`. -/
def mkP0 : SProg RK := .seq (linPrep .B .K 2 2 6) (.seq (moveAll (.inr .NUM) (.inr .P0))
  (clearM (.inr .B)))

theorem mkP0_ms (S0 : RK → List Sym) (b k i : ℕ) :
    MS mkP0 S0 (regs b k i 0 0 0 0 0) S0 (regs 0 k i (2 * b + 2 * k + 6) 0 0 0 0)
      (40 * b + 40 * k + 60) := by
  have h := (linPrep_ms (a1 := .B) (a2 := .K) rfl rfl (by decide) (by decide) (by decide)
    (by decide) 2 2 6 S0 (regs b k i 0 0 0 0 0) rfl rfl).seq
    ((mv_ms (a := .NUM) (b := .P0) rfl rfl (by decide) S0 _).seq (clr_ms (a := .B) rfl S0 _))
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs]
    omega
  · funext x
    cases x <;> simp [regs]

/-- `PP := schedP P0 K = 2 P0 + 12 K + 32 ⌈log₂(P0 + K + 2)⌉ + 256`. -/
def mkPP : SProg RK :=
  .seq (.seq (.seq (linPrep .P0 .K 1 1 1) bitLenU) (linPrep .P0 .K 2 12 256))
    (.seq (.seq (cpN .Z .NUM .T 32) (moveAll (.inr .NUM) (.inr .PP))) (clearM (.inr .Z)))

theorem mkPP_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 : ℕ) :
    MS mkPP S0 (regs 0 k i p0 0 0 0 0) S0
      (regs 0 k i p0 (2 * p0 + 12 * k + 32 * bitLen (p0 + k + 1) + 256) 0 0 0)
      (2000 * (p0 + k + 1)) := by
  have hb := bitLen_le (p0 + k + 1)
  have h1 := linPrep_ms (a1 := .P0) (a2 := .K) rfl rfl (by decide) (by decide) (by decide)
    (by decide) 1 1 1 S0 (regs 0 k i p0 0 0 0 0) rfl rfl
  have h2 := bitLenU_ms S0 (Function.update (regs 0 k i p0 0 0 0 0) .NUM
    (1 * regs 0 k i p0 0 0 0 0 .P0 + 1 * regs 0 k i p0 0 0 0 0 .K + 1)) ⟨rfl, rfl, hO⟩
  have h := ((h1.seq h2).seq (linPrep_ms (a1 := .P0) (a2 := .K) rfl rfl (by decide) (by decide)
    (by decide) (by decide) 2 12 256 S0 _ (by simp) (by simp [regs]))).seq
    (((cpN_ms (a := .Z) (b := .NUM) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide)
      S0 32 _ (by simp [regs])).seq (mv_ms (a := .NUM) (b := .PP) rfl rfl (by decide) S0 _)).seq
      (clr_ms (a := .Z) rfl S0 _))
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs]
    omega
  · funext x
    cases x <;> simp [regs] <;> ring

/-- `Dk := ⌊K^{1/15}⌋`. -/
def mkDk : SProg RK :=
  .seq (.seq (.seq (copyAll (.inr .K) (.inr .RAD) (.inr .T)) (search (testRoot 15)))
    (moveAll (.inr .Y) (.inr .Dk))) (clearM (.inr .RAD))

theorem mkDk_ms (S0 : RK → List Sym) (k i p0 pp : ℕ) :
    MS mkDk S0 (regs 0 k i p0 pp 0 0 0) S0
      (regs 0 k i p0 pp (SubNLogN.Math.Cost.floorRatPow k 1 15) 0 0)
      ((SubNLogN.Math.Cost.floorRatPow k 1 15 + 1) *
        (rootB 15 (SubNLogN.Math.Cost.floorRatPow k 1 15) k + 2) + 16 * k + 10) := by
  have h1 := cp_ms (a := .K) (b := .RAD) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 (regs 0 k i p0 pp 0 0 0) rfl
  have h2 := rootSearch_ms 15 (by norm_num) S0 (Function.update (regs 0 k i p0 pp 0 0 0) .RAD
    (regs 0 k i p0 pp 0 0 0 .K + regs 0 k i p0 pp 0 0 0 .RAD))
    ((ArClean_regs 0 k i p0 pp 0 0 0).upd rfl _) (by simp [regs])
  have h := ((h1.seq h2).seq (mv_ms (a := .Y) (b := .Dk) rfl rfl (by decide) S0 _)).seq
    (clr_ms (a := .RAD) rfl S0 _)
  have hle := frp_le k 15 (by norm_num)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs]
    omega
  · funext x
    cases x <;> simp [regs]

/-- `L := ⌈K / Dk⌉`, then `Mm := Dk · L - K`. -/
def mkLM : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (search testDiv) (moveAll (.inr .Y) (.inr .L)))
    (copyAll (.inr .Dk) (.inr .MA) (.inr .T))) (copyAll (.inr .L) (.inr .MB) (.inr .T))) mulU)
    (clearM (.inr .MA))) (clearM (.inr .MB))) (moveAll (.inr .MZ) (.inr .Mm))) (subU .K .Mm)

theorem mkLM_ms (S0 : RK → List Sym) (k i p0 pp dk : ℕ) (hd : dk = 0 → k = 0) :
    MS mkLM S0 (regs 0 k i p0 pp dk 0 0) S0
      (regs 0 k i p0 pp dk ((k + dk - 1) / dk) (dk * ((k + dk - 1) / dk) - k))
      (((k + dk - 1) / dk + 1) * (divB ((k + dk - 1) / dk) dk k + 2) +
        30 * ((k + dk - 1) / dk + 1) * (dk + 1) + 20 * k + 40) := by
  have h1 := divSearch_ms S0 (regs 0 k i p0 pp dk 0 0) (ArClean_regs _ _ _ _ _ _ _ _) rfl hd
  have h := ((((((((h1.seq (mv_ms (a := .Y) (b := .L) rfl rfl (by decide) S0 _)).seq
    (cp_ms (a := .Dk) (b := .MA) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]))).seq
    (cp_ms (a := .L) (b := .MB) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]))).seq (mulU_ms S0 _ (by simp [regs]) (by simp [regs]))).seq
    (clr_ms (a := .MA) rfl S0 _)).seq (clr_ms (a := .MB) rfl S0 _)).seq
    (mv_ms (a := .MZ) (b := .Mm) rfl rfl (by decide) S0 _)).seq
    (subU_ms (src := .K) (tgt := .Mm) rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]) (by simp [regs])))
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs]
    generalize (k + dk - 1) / dk = Q
    generalize divB Q dk k = D'
    nlinarith
  · funext x
    cases x <;> simp [regs] <;> ring_nf

/-! ## Output phases -/

theorem pushVal_ms (prep : SProg RK) (tgt : PN) (S0 : RK → List Sym) (R : RE → ℕ) (v Bp : ℕ)
    (hprep : MS prep S0 R S0 (Function.update R .NUM v) Bp)
    (hX : R .X = 0) (hP : R .PAR = 0) (hN : R .NUM = 0) (hO : S0 (.inr .O) = []) :
    MS (.seq prep (pushNat tgt)) S0 R
      (Function.update S0 (.inl tgt) (hdrSyms [v] ++ S0 (.inl tgt))) R (Bp + (34 * v + 5)) := by
  have h := hprep.seq (pushNat_ms tgt S0 (Function.update R .NUM v)
    ⟨by simp [hX], by simp [hP], hO⟩)
  have hR : Function.update R .NUM 0 = R := by rw [← hN, Function.update_eq_self]
  simp only [Function.update_self, Function.update_idem, hR] at h
  exact h

theorem pushVal2_ms (prep : SProg RK) (tgt : PN) (S0 : RK → List Sym) (R : RE → ℕ) (v Bp : ℕ)
    (hprep : MS prep S0 R S0 (Function.update R .NUM v) Bp) (hN : R .NUM = 0) :
    MS (.seq prep (pushPow2 tgt)) S0 R
      (Function.update S0 (.inl tgt) (hdrSyms [2 ^ v] ++ S0 (.inl tgt))) R (Bp + (4 * v + 4)) := by
  have h := hprep.seq (pushPow2_ms tgt S0 (Function.update R .NUM v))
  have hR : Function.update R .NUM 0 = R := by rw [← hN, Function.update_eq_self]
  simp only [Function.update_self, Function.update_idem, hR] at h
  exact h

theorem hP_nat (tgt : PN) (a : ℕ) : ∀ (S0 : RK → List Sym) (u : RE → ℕ), OutOK S0 u →
    u .NUM = a → MS (pushNat tgt) S0 u (Function.update S0 (.inl tgt)
      (hdrSyms [a] ++ S0 (.inl tgt))) (Function.update u .NUM 0) (34 * a + 5) := by
  intro S0 u hok hu
  have h := pushNat_ms tgt S0 u hok
  rwa [hu] at h

theorem hP_pow2 (tgt : PN) (a : ℕ) : ∀ (S0 : RK → List Sym) (u : RE → ℕ), OutOK S0 u →
    u .NUM = a → MS (pushPow2 tgt) S0 u (Function.update S0 (.inl tgt)
      (hdrSyms [2 ^ a] ++ S0 (.inl tgt))) (Function.update u .NUM 0) (4 * a + 4) := by
  intro S0 u _ hu
  have h := pushPow2_ms tgt S0 u
  rwa [hu] at h

theorem rep_ms' (P : SProg RK) (tgt : PN) (y a Bp : ℕ)
    (hP : ∀ S0 u, OutOK S0 u → u .NUM = a → MS P S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt))) (Function.update u .NUM 0) Bp)
    (S0 : RK → List Sym) (u : RE → ℕ) (c' : ℕ) (hc : u .CNT ≤ c') (hV : u .V = a)
    (hN : u .NUM = 0) (hT : u .T = 0) (hok : OutOK S0 u) :
    MS (rep P) S0 u (Function.update S0 (.inl tgt) (hdrSyms (List.replicate (u .CNT) y) ++
      S0 (.inl tgt))) (Function.update u .CNT 0) (c' * (Bp + 9 * a + 8) + 2) :=
  (rep_ms P tgt y a Bp hP S0 u hV hN hT hok).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 2)

/-- `(Dk - 1 - Mm)` fields of the value `L` (via `P`). -/
def repA (P : SProg RK) : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (copyAll (.inr .L) (.inr .V) (.inr .T))
    (copyAll (.inr .Dk) (.inr .CNT) (.inr .T))) (popR (.inr .CNT))) (subU .Mm .CNT)) (rep P))
    (clearM (.inr .V))

/-- `Mm` fields of the value `L - 1` (via `P`). -/
def repB (P : SProg RK) : SProg RK :=
  .seq (.seq (.seq (.seq (copyAll (.inr .L) (.inr .V) (.inr .T)) (popR (.inr .V)))
    (copyAll (.inr .Mm) (.inr .CNT) (.inr .T))) (rep P)) (clearM (.inr .V))

theorem repA_ms (P : SProg RK) (tgt : PN) (y Bp : ℕ) (S0 : RK → List Sym)
    (hO : S0 (.inr .O) = []) (k i p0 pp dk l m : ℕ)
    (hP : ∀ S0 u, OutOK S0 u → u .NUM = l → MS P S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt))) (Function.update u .NUM 0) Bp) :
    MS (repA P) S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl tgt) (hdrSyms (List.replicate (dk - 1 - m) y) ++ S0 (.inl tgt)))
      (regs 0 k i p0 pp dk l m) (dk * (Bp + 9 * l + 8) + 12 * l + 9 * dk + 13 * m + 19) := by
  have h := (((((cp_ms (a := .L) (b := .V) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 (regs 0 k i p0 pp dk l m) rfl).seq
    (cp_ms (a := .Dk) (b := .CNT) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]))).seq (pop_ms (a := .CNT) rfl S0 _)).seq
    (subU_ms (src := .Mm) (tgt := .CNT) rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]) (by simp [regs]))).seq
    (rep_ms' P tgt y l Bp hP S0 _ dk (by simp [regs]; omega) (by simp [regs]) (by simp [regs])
      (by simp [regs]) ⟨by simp [regs], by simp [regs], hO⟩)).seq (clr_ms (a := .V) rfl _ _)
  refine (h.mono ?_).of_eq ?_ ?_
  · simp [regs]
    omega
  · simp [regs]
  · funext x
    cases x <;> simp [regs]

theorem repB_ms (P : SProg RK) (tgt : PN) (y Bp : ℕ) (S0 : RK → List Sym)
    (hO : S0 (.inr .O) = []) (k i p0 pp dk l m : ℕ)
    (hP : ∀ S0 u, OutOK S0 u → u .NUM = l - 1 → MS P S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt))) (Function.update u .NUM 0) Bp) :
    MS (repB P) S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl tgt) (hdrSyms (List.replicate m y) ++ S0 (.inl tgt)))
      (regs 0 k i p0 pp dk l m) (m * (Bp + 9 * l + 8) + 12 * l + 9 * m + 13) := by
  have h := ((((cp_ms (a := .L) (b := .V) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 (regs 0 k i p0 pp dk l m) rfl).seq (pop_ms (a := .V) rfl S0 _)).seq
    (cp_ms (a := .Mm) (b := .CNT) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide) S0 _
      (by simp [regs]))).seq
    (rep_ms' P tgt y (l - 1) Bp hP S0 _ m (by simp [regs]) (by simp [regs]) (by simp [regs])
      (by simp [regs]) ⟨by simp [regs], by simp [regs], hO⟩)).seq (clr_ms (a := .V) rfl _ _)
  refine (h.mono ?_).of_eq ?_ ?_
  · simp [regs]
    nlinarith [Nat.sub_le l 1, Nat.mul_le_mul_left m (Nat.sub_le l 1)]
  · simp [regs]
  · funext x
    cases x <;> simp [regs]

/-- `Z := max Z 1`. -/
def maxOne : SProg RK := .seq (peekR (.inr .Z)) (.ite isSomeB skip (pushC (.inr .Z) .mark))

theorem maxOne_ms (S0 : RK → List Sym) (u : RE → ℕ) :
    MS maxOne S0 u S0 (Function.update u .Z (max (u .Z) 1)) 3 := by
  intro v
  have e0 := peekU_eval (a := .Z) rfl v S0 u
  rcases Nat.eq_zero_or_pos (u .Z) with h | h
  · rw [h] at e0
    have e1 := Eval.ite_false (c := isSomeB) (p := (skip : SProg RK)) (by rfl)
      (pushU_eval (a := .Z) rfl (List.replicate 0 Sym.mark).head? S0 u)
    refine ⟨(List.replicate 0 Sym.mark).head?, _, le_refl _, (Eval.seq e0 e1).of_eq ?_ rfl⟩
    rw [h]
    simp
  · obtain ⟨j, hj⟩ : ∃ j, u .Z = j + 1 := ⟨u .Z - 1, by omega⟩
    rw [hj] at e0
    have e1 := Eval.ite_true (c := isSomeB) (q := (pushC (.inr .Z) .mark : SProg RK)) (by rfl)
      (skip_eval [] (⟨(List.replicate (j + 1) Sym.mark).head?, mkS S0 u⟩ : SSt RK))
    refine ⟨(List.replicate (j + 1) Sym.mark).head?, _, le_refl _,
      (Eval.seq e0 e1).of_eq ?_ rfl⟩
    have hu : Function.update u .Z (max (u .Z) 1) = u := by
      rw [show max (u .Z) 1 = u .Z by omega, Function.update_eq_self]
    rw [hu]

/-! ## Field preparations -/

/-- `NUM := Dk - 1` (the number `D = d - 1` of record axes). -/
def prepD : SProg RK := .seq (linPrep .Dk .Dk 1 0 0) (popR (.inr .NUM))

theorem prepD_ms (S0 : RK → List Sym) (k i p0 pp dk l m : ℕ) :
    MS prepD S0 (regs 0 k i p0 pp dk l m) S0
      (Function.update (regs 0 k i p0 pp dk l m) .NUM (dk - 1)) (9 * dk + 9) := by
  have h := (linPrep_ms (a1 := .Dk) (a2 := .Dk) rfl rfl (by decide) (by decide) (by decide)
    (by decide) 1 0 0 S0 (regs 0 k i p0 pp dk l m) rfl rfl).seq (pop_ms (a := .NUM) rfl S0 _)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs] <;> omega
  · funext x
    cases x <;> simp [regs]

/-- `NUM := (Dk - 1) + 1` (the number `d` of axes). -/
def prepd : SProg RK := .seq prepD (pushMs .NUM 1)

theorem prepd_ms (S0 : RK → List Sym) (k i p0 pp dk l m : ℕ) :
    MS prepd S0 (regs 0 k i p0 pp dk l m) S0
      (Function.update (regs 0 k i p0 pp dk l m) .NUM (dk - 1 + 1)) (9 * dk + 11) := by
  have h := (prepD_ms S0 k i p0 pp dk l m).seq (pushMs_ms (a := .NUM) rfl S0 1 _)
  refine (h.mono (by omega)).of_eq rfl ?_
  rw [Function.update_self, Function.update_idem]

/-- `NUM := ⌊Dk ^ (1/2^50)⌋ = KK`. -/
def prepKK : SProg RK :=
  .seq (.seq (copyAll (.inr .Dk) (.inr .RAD) (.inr .T)) (iterSqrt 50))
    (moveAll (.inr .RAD) (.inr .NUM))

theorem prepKK_ms (S0 : RK → List Sym) (k i p0 pp dk l m : ℕ) :
    MS prepKK S0 (regs 0 k i p0 pp dk l m) S0 (Function.update (regs 0 k i p0 pp dk l m) .NUM
      (SubNLogN.Math.Cost.floorRatPow dk 1 (2 ^ 50))) (50 * sqB dk + 13 * dk + 8) := by
  have h1 := cp_ms (a := .Dk) (b := .RAD) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 (regs 0 k i p0 pp dk l m) rfl
  have h2 := iterSqrt_ms S0 50 (Function.update (regs 0 k i p0 pp dk l m) .RAD
    (regs 0 k i p0 pp dk l m .Dk + regs 0 k i p0 pp dk l m .RAD))
    ((ArClean_regs _ _ _ _ _ _ _ _).upd rfl _) (by simp [regs])
  have h := (h1.seq h2).seq (mv_ms (a := .RAD) (b := .NUM) rfl rfl (by decide) S0 _)
  have hle := frp_le dk (2 ^ 50) (by positivity)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs] at hle ⊢ <;> omega
  · funext x
    cases x <;> simp [regs]

/-- `NUM := lg d + P0 + K + 20 = ω` (with `lg d = max (bitLen (Dk - 1)) 1`). -/
def prepW : SProg RK :=
  .seq (.seq (.seq (.seq prepD bitLenU) maxOne) (linPrep .P0 .K 1 1 20))
    (moveAll (.inr .Z) (.inr .NUM))

theorem prepW_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m : ℕ) :
    MS prepW S0 (regs 0 k i p0 pp dk l m) S0 (Function.update (regs 0 k i p0 pp dk l m) .NUM
      (max (bitLen (dk - 1)) 1 + (p0 + k + 20))) (60 * dk + 9 * p0 + 9 * k + 60) := by
  have hb := bitLen_le (dk - 1)
  have h := ((((prepD_ms S0 k i p0 pp dk l m).seq
    (bitLenU_ms S0 _ ⟨by simp [regs], by simp [regs], hO⟩)).seq (maxOne_ms S0 _)).seq
    (linPrep_ms (a1 := .P0) (a2 := .K) rfl rfl (by decide) (by decide) (by decide) (by decide)
      1 1 20 S0 _ (by simp) (by simp [regs]))).seq
    (mv_ms (a := .Z) (b := .NUM) rfl rfl (by decide) S0 _)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs] <;> omega
  · funext x
    cases x <;> simp [regs] <;> omega

/-- A linear field `c1·a1 + c2·a2 + c3` pushed on `tgt`. -/
def outLin (tgt : PN) (a1 a2 : RE) (c1 c2 c3 : ℕ) : SProg RK :=
  .seq (linPrep a1 a2 c1 c2 c3) (pushNat tgt)

theorem outLin_ms (tgt : PN) {a1 a2 : RE} (h1 : isU a1 = true) (h2 : isU a2 = true)
    (h1N : a1 ≠ .NUM) (h2N : a2 ≠ .NUM) (h1T : a1 ≠ .T) (h2T : a2 ≠ .T) (c1 c2 c3 : ℕ)
    (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m : ℕ) :
    MS (outLin tgt a1 a2 c1 c2 c3) S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl tgt) (hdrSyms [c1 * regs 0 k i p0 pp dk l m a1 +
        c2 * regs 0 k i p0 pp dk l m a2 + c3] ++ S0 (.inl tgt))) (regs 0 k i p0 pp dk l m)
      (c1 * (9 * regs 0 k i p0 pp dk l m a1 + 4) + c2 * (9 * regs 0 k i p0 pp dk l m a2 + 4) +
        c3 + 3 + (34 * (c1 * regs 0 k i p0 pp dk l m a1 + c2 * regs 0 k i p0 pp dk l m a2 + c3) +
          5)) :=
  pushVal_ms _ tgt S0 _ _ _ (linPrep_ms h1 h2 h1N h2N h1T h2T c1 c2 c3 S0 _ rfl rfl) rfl rfl rfl hO

/-! ## Output phases -/

/-- `win := [p0 + p_in + 2]`, `wout := [2 p0 + K0 + 8]`. -/
def outWW : SProg RK := .seq (outLin .win .P0 .I 1 1 2) (outLin .wout .P0 .K 2 1 8)

theorem outWW_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hk : k ≤ X) (hi : i ≤ X) (hp0 : p0 ≤ 2 * X) (h16 : 16 ≤ X) :
    MS outWW S0 (regs 0 k i p0 pp dk l m)
      (Function.update (Function.update S0 (.inl .win) (hdrSyms [p0 + i + 2] ++ S0 (.inl .win)))
        (.inl .wout) (hdrSyms [2 * p0 + k + 8] ++ S0 (.inl .wout)))
      (regs 0 k i p0 pp dk l m) (1000 * X) := by
  have h := (outLin_ms .win (a1 := .P0) (a2 := .I) rfl rfl (by decide) (by decide) (by decide)
    (by decide) 1 1 2 S0 hO k i p0 pp dk l m).seq
    (outLin_ms .wout (a1 := .P0) (a2 := .K) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 2 1 8 _ (by simp [hO]) k i p0 pp dk l m)
  refine (h.mono ?_).of_eq ?_ rfl
  · simp [regs] <;> omega
  · simp [regs]

/-- `mpar += hdrSyms (replicate m (l-1) ++ replicate (dk-1-m) l)` (the axis exponents). -/
def outMparA : SProg RK := .seq (repA (pushNat .mpar)) (repB (pushNat .mpar))

theorem outMparA_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hdk : dk ≤ X) (hl : l ≤ X) (hm : m ≤ X) (h16 : 16 ≤ X) :
    MS outMparA S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl .mpar) (hdrSyms (List.replicate m (l - 1)) ++
        (hdrSyms (List.replicate (dk - 1 - m) l) ++ S0 (.inl .mpar))))
      (regs 0 k i p0 pp dk l m) (200 * X * X) := by
  have h := (repA_ms (pushNat .mpar) .mpar l (34 * l + 5) S0 hO k i p0 pp dk l m
    (hP_nat .mpar l)).seq
    (repB_ms (pushNat .mpar) .mpar (l - 1) (34 * (l - 1) + 5) _ (by simp [hO]) k i p0 pp dk l m
      (hP_nat .mpar (l - 1)))
  refine (h.mono ?_).of_eq ?_ rfl
  · have h1 : dk * (34 * l + 5 + 9 * l + 8) ≤ X * (56 * X) := Nat.mul_le_mul hdk (by omega)
    have h2 : m * (34 * (l - 1) + 5 + 9 * l + 8) ≤ X * (56 * X) :=
      Nat.mul_le_mul hm (by omega)
    nlinarith
  · simp only [Function.update_idem, Function.update_self]

/-- `mpar += [P + 2, D, ℓ, KK, wI]` (pushed last to first). -/
def outMparB : SProg RK :=
  .seq (.seq (.seq (.seq (outLin .mpar .PP .K 1 2 16) (.seq prepKK (pushNat .mpar)))
    (outLin .mpar .L .L 1 0 0)) (.seq prepD (pushNat .mpar))) (outLin .mpar .PP .PP 1 0 2)

theorem outMparB_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hk : k ≤ X) (hpp : pp ≤ 128 * X) (hdk : dk ≤ X) (hl : l ≤ X) (h16 : 16 ≤ X) :
    MS outMparB S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl .mpar) (hdrSyms [pp + 2] ++ (hdrSyms [dk - 1] ++ (hdrSyms [l] ++
        (hdrSyms [SubNLogN.Math.Cost.floorRatPow dk 1 (2 ^ 50)] ++
          (hdrSyms [pp + 2 * k + 16] ++ S0 (.inl .mpar)))))))
      (regs 0 k i p0 pp dk l m) (50 * sqB X + 30000 * X) := by
  have h := ((((outLin_ms .mpar (a1 := .PP) (a2 := .K) rfl rfl (by decide) (by decide)
    (by decide) (by decide) 1 2 16 S0 hO k i p0 pp dk l m).seq
    (pushVal_ms _ .mpar _ _ _ _ (prepKK_ms _ k i p0 pp dk l m) rfl rfl rfl (by simp [hO]))).seq
    (outLin_ms .mpar (a1 := .L) (a2 := .L) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 0 0 _ (by simp [hO]) k i p0 pp dk l m)).seq
    (pushVal_ms _ .mpar _ _ _ _ (prepD_ms _ k i p0 pp dk l m) rfl rfl rfl (by simp [hO]))).seq
    (outLin_ms .mpar (a1 := .PP) (a2 := .PP) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 0 2 _ (by simp [hO]) k i p0 pp dk l m)
  have hs := sqB_mono hdk
  have hkk := frp_le dk (2 ^ 50) (by positivity)
  refine (h.mono ?_).of_eq ?_ rfl
  · simp [regs] at hkk ⊢ <;> omega
  · simp [regs]

/-- `par += [2^ℓ]`, then the shape entries `2^ℓ` (`dk-1-m` times) and `2^(ℓ-1)` (`m` times). -/
def outParA : SProg RK :=
  .seq (.seq (.seq (linPrep .L .L 1 0 0) (pushPow2 .par)) (repA (pushPow2 .par)))
    (repB (pushPow2 .par))

theorem outParA_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hdk : dk ≤ X) (hl : l ≤ X) (hm : m ≤ X) (h16 : 16 ≤ X) :
    MS outParA S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl .par) (hdrSyms (List.replicate m (2 ^ (l - 1))) ++
        (hdrSyms (List.replicate (dk - 1 - m) (2 ^ l)) ++ (hdrSyms [2 ^ l] ++ S0 (.inl .par)))))
      (regs 0 k i p0 pp dk l m) (100 * X * X) := by
  have h := ((pushVal2_ms _ .par S0 _ _ _ (linPrep_ms (a1 := .L) (a2 := .L) rfl rfl (by decide)
    (by decide) (by decide) (by decide) 1 0 0 S0 (regs 0 k i p0 pp dk l m) rfl rfl) rfl).seq
    (repA_ms (pushPow2 .par) .par (2 ^ l) (4 * l + 4) _ (by simp [hO]) k i p0 pp dk l m
      (hP_pow2 .par l))).seq
    (repB_ms (pushPow2 .par) .par (2 ^ (l - 1)) (4 * (l - 1) + 4) _ (by simp [hO]) k i p0 pp dk
      l m (hP_pow2 .par (l - 1)))
  have h1 : dk * (4 * l + 4 + 9 * l + 8) ≤ X * (25 * X) := Nat.mul_le_mul hdk (by omega)
  have h2 : m * (4 * (l - 1) + 4 + 9 * l + 8) ≤ X * (25 * X) := Nat.mul_le_mul hm (by omega)
  refine (h.mono ?_).of_eq ?_ rfl
  · simp only [regs, one_mul, zero_mul, Nat.add_zero]
    nlinarith
  · simp [regs]

/-- `par += [d, wIn, pIn, wOut]` (pushed last to first). -/
def outParB : SProg RK :=
  .seq (.seq (.seq (.seq prepd (pushNat .par)) (outLin .par .P0 .I 1 1 2))
    (outLin .par .I .I 1 0 2)) (outLin .par .P0 .K 2 1 8)

theorem outParB_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hk : k ≤ X) (hi : i ≤ X) (hp0 : p0 ≤ 2 * X) (hdk : dk ≤ X) (h16 : 16 ≤ X) :
    MS outParB S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl .par) (hdrSyms [2 * p0 + k + 8] ++ (hdrSyms [i + 2] ++
        (hdrSyms [p0 + i + 2] ++ (hdrSyms [dk - 1 + 1] ++ S0 (.inl .par))))))
      (regs 0 k i p0 pp dk l m) (2000 * X) := by
  have h := (((pushVal_ms _ .par S0 _ _ _ (prepd_ms S0 k i p0 pp dk l m) rfl rfl rfl hO).seq
    (outLin_ms .par (a1 := .P0) (a2 := .I) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 1 2 _ (by simp [hO]) k i p0 pp dk l m)).seq
    (outLin_ms .par (a1 := .I) (a2 := .I) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 0 2 _ (by simp [hO]) k i p0 pp dk l m)).seq
    (outLin_ms .par (a1 := .P0) (a2 := .K) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 2 1 8 _ (by simp [hO]) k i p0 pp dk l m)
  refine (h.mono ?_).of_eq ?_ rfl
  · simp [regs] <;> omega
  · simp [regs]

/-- `par += [wI, wT, ω, P, p0]` (pushed last to first). -/
def outParC : SProg RK :=
  .seq (.seq (.seq (.seq (outLin .par .PP .K 1 2 16) (outLin .par .PP .K 1 2 16))
    (.seq prepW (pushNat .par))) (outLin .par .PP .PP 1 0 0)) (outLin .par .P0 .P0 1 0 0)

theorem outParC_ms (S0 : RK → List Sym) (hO : S0 (.inr .O) = []) (k i p0 pp dk l m X : ℕ)
    (hk : k ≤ X) (hp0 : p0 ≤ 2 * X) (hpp : pp ≤ 128 * X) (hdk : dk ≤ X) (h16 : 16 ≤ X) :
    MS outParC S0 (regs 0 k i p0 pp dk l m)
      (Function.update S0 (.inl .par) (hdrSyms [p0] ++ (hdrSyms [pp] ++
        (hdrSyms [max (bitLen (dk - 1)) 1 + (p0 + k + 20)] ++ (hdrSyms [pp + 2 * k + 16] ++
          (hdrSyms [pp + 2 * k + 16] ++ S0 (.inl .par)))))))
      (regs 0 k i p0 pp dk l m) (30000 * X) := by
  have h := ((((outLin_ms .par (a1 := .PP) (a2 := .K) rfl rfl (by decide) (by decide)
    (by decide) (by decide) 1 2 16 S0 hO k i p0 pp dk l m).seq
    (outLin_ms .par (a1 := .PP) (a2 := .K) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 2 16 _ (by simp [hO]) k i p0 pp dk l m)).seq
    (pushVal_ms _ .par _ _ _ _ (prepW_ms _ (by simp [hO]) k i p0 pp dk l m) rfl rfl rfl
      (by simp [hO]))).seq
    (outLin_ms .par (a1 := .PP) (a2 := .PP) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 0 0 _ (by simp [hO]) k i p0 pp dk l m)).seq
    (outLin_ms .par (a1 := .P0) (a2 := .P0) rfl rfl (by decide) (by decide) (by decide)
      (by decide) 1 0 0 _ (by simp [hO]) k i p0 pp dk l m)
  have hb := bitLen_le (dk - 1)
  refine (h.mono ?_).of_eq ?_ rfl
  · simp [regs] <;> omega
  · simp [regs]

/-- Clear the persistent registers. -/
def cleanProg : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (.seq (clearM (.inr .K)) (clearM (.inr .I))) (clearM (.inr .P0)))
    (clearM (.inr .PP))) (clearM (.inr .Dk))) (clearM (.inr .L))) (clearM (.inr .Mm))

theorem clean_ms (S0 : RK → List Sym) (k i p0 pp dk l m : ℕ) :
    MS cleanProg S0 (regs 0 k i p0 pp dk l m) S0 (regs 0 0 0 0 0 0 0 0)
      (3 * (k + i + p0 + pp + dk + l + m) + 14) := by
  have h := ((((((clr_ms (a := .K) rfl S0 (regs 0 k i p0 pp dk l m)).seq
    (clr_ms (a := .I) rfl S0 _)).seq (clr_ms (a := .P0) rfl S0 _)).seq
    (clr_ms (a := .PP) rfl S0 _)).seq (clr_ms (a := .Dk) rfl S0 _)).seq
    (clr_ms (a := .L) rfl S0 _)).seq (clr_ms (a := .Mm) rfl S0 _)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [regs] <;> omega
  · funext x
    cases x <;> simp [regs]

end SubNLogN.Machine.Pipe.ReadParamsAux
