import SubNLogN.Machine.Pipe.GuardBase

/-!
# Input-guard kernel, part 2: the phases of the guard program

Helpers (namespace `SubNLogN.Machine.Pipe.GuardAux`) for
`SubNLogN.Machine.Pipe.guard_holds : GuardStmt` (proved in `SubNLogN/Machine/Pipe/Guard.lean`).

* The layout: nine scratch stacks `GE` (`GK := KLoc PN GE`).
* Phase A (`phaseA`, `phaseA_eval`): from the binary header fields `b`, `K0` (on `C0`) and `p_in`
  (on `C1`), build a unary ruler of `g = 2b + 2K0 + p_in + 7` marks on `U`; `C0`, `C1` restored.
* Phase B (`scan`, `scan_loop_eval`): pop the W9 entries of `S` onto `T` up to the node tag;
  at each sign symbol reload the ruler (`U → V`), at each bit pop `V` and record an underflow mark
  on `F`.  Counting lemmas: no underflow mark iff every numerator has bit length `≤ g`
  (`ffin_entries_eq_zero`), and the potential cost bound `scost_le`.
* Phases C, D (`readF`) and the whole program `guardProg`, which is closed (`closed_guardProg`).
-/

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## The layout -/

/-- Scratch stacks of the guard kernel. -/
inductive GE
  | U | V | X | T | H | G | D | D2 | F
  deriving DecidableEq

instance : Fintype GE where
  elems := {GE.U, GE.V, GE.X, GE.T, GE.H, GE.G, GE.D, GE.D2, GE.F}
  complete := by intro x; cases x <;> simp

/-- Stacks of the guard kernel. -/
abbrev GK : Type := KLoc PN GE

abbrev sS : GK := .inl .S
abbrev sC0 : GK := .inl .C0
abbrev sC1 : GK := .inl .C1
abbrev sU : GK := .inr .U
abbrev sV : GK := .inr .V
abbrev sX : GK := .inr .X
abbrev sT : GK := .inr .T
abbrev sH : GK := .inr .H
abbrev sG : GK := .inr .G
abbrev sD : GK := .inr .D
abbrev sD2 : GK := .inr .D2
abbrev sF : GK := .inr .F

/-! ## Phase A: the unary ruler -/

/-- Convert the top header field of `src` (bits, then `mark`) into `D`, restoring `src`. -/
def fieldToD (src : GK) : SProg GK := .seq (moveBlock src sH) (horner src sD sD2 sH)

/-- Cost of `fieldToD` on the field `natSyms n`. -/
def fcost (n : ℕ) : ℕ := 3 * bitLen n + 4 + (hcost 0 (encodeNat n).reverse + 1)

theorem fcost_le (n : ℕ) : fcost n ≤ 13 * n + 16 * bitLen n + 6 := by
  have h := hcost_le 0 (encodeNat n).reverse
  rw [hval_encodeNat, List.length_reverse] at h
  unfold fcost bitLen
  omega

theorem fieldToD_eval (src : GK) (hsH : src ≠ sH) (hsD : src ≠ sD) (hsD2 : src ≠ sD2)
    (ρ : List (SProg GK)) (v : Option Sym) (n : ℕ) (R : List Sym) (S : GK → List Sym)
    (hS : S src = natSyms n ++ Sym.mark :: R) (hH : S sH = []) (hD : S sD = [])
    (hD2 : S sD2 = []) :
    Eval ρ (fieldToD src) ⟨v, S⟩ ⟨none, Function.update S sD (List.replicate n Sym.mark)⟩
      (fcost n) := by
  have e1 := moveBlock_eval hsH ρ v (encodeNat n) (Sym.mark :: R) S (TermOK.cons rfl R) hS
  set S1 := Function.update (Function.update S src (Sym.mark :: R)) sH
    ((encodeNat n).reverse.map Sym.bit ++ S sH) with hS1
  have hS1H : S1 sH = (encodeNat n).reverse.map Sym.bit := by
    rw [hS1, Function.update_self, hH, List.append_nil]
  have hS1D : S1 sD = List.replicate 0 Sym.mark := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne hsD.symm, hD]; rfl
  have hS1D2 : S1 sD2 = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne hsD2.symm, hD2]
  have e2 := horner_eval hsD hsD2 hsH (by decide) (by decide) (by decide) ρ
    (Sym.mark :: R).head? (encodeNat n).reverse 0 S1 hS1H hS1D hS1D2
  rw [hval_encodeNat, List.reverse_reverse] at e2
  refine (Eval.seq e1 e2).of_eq ?_ (by unfold fcost bitLen; ring)
  congr 1
  funext k
  by_cases h1 : k = sD
  · subst h1; simp
  · by_cases h2 : k = src
    · subst h2
      simp [Function.update_of_ne h1, hS1, Function.update_of_ne hsH, hS, natSyms]
    · by_cases h3 : k = sH
      · subst h3; simp [Function.update_of_ne h1, Function.update_of_ne h2, hH]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, hS1]

/-- Push `n` copies of `mark` on `k`. -/
def pushMarks (k : GK) : ℕ → SProg GK
  | 0 => skip
  | n + 1 => .seq (pushC k .mark) (pushMarks k n)

theorem pushMarks_eval (k : GK) (ρ : List (SProg GK)) (v : Option Sym) :
    ∀ (n : ℕ) (S : GK → List Sym),
      Eval ρ (pushMarks k n) ⟨v, S⟩
        ⟨v, Function.update S k (List.replicate n Sym.mark ++ S k)⟩ (n + 1)
  | 0, S => (skip_eval ρ _).of_eq (by simp) rfl
  | n + 1, S => by
    have e1 := Eval.push ρ k (fun _ => Sym.mark) v S
    have e2 := pushMarks_eval k ρ v n (Function.update S k (Sym.mark :: S k))
    refine (Eval.seq e1 e2).of_eq ?_ (by ring)
    simp [List.replicate_succ']

/-- **Phase A**: `U := (2b + 2K0 + pin + 7)` marks; `C0`, `C1` restored. -/
def phaseA : SProg GK :=
  .seq (fieldToD sC0) <| .seq (moveDbl sD sU) <|
  .seq (moveBlock sC0 sG) <| .seq (popR sC0) <| .seq (pushR sG) <|
  .seq (fieldToD sC0) <| .seq (moveDbl sD sU) <|
  .seq (popR sG) <| .seq (pushR sC0) <| .seq (moveBlock sG sC0) <|
  .seq (fieldToD sC1) <| .seq (moveAll sD sU) <| pushMarks sU 7

/-- Cost of phase A. -/
def costA (b K0 pin : ℕ) : ℕ :=
  fcost b + (5 * b + 2) + (3 * bitLen b + 4) + 1 + 1 + fcost K0 + (5 * K0 + 2) + 1 + 1 +
    (3 * bitLen b + 4) + fcost pin + (4 * pin + 2) + 8

theorem phaseA_eval (ρ : List (SProg GK)) (v : Option Sym) (b K0 pin : ℕ) (R0 R1 : List Sym)
    (S : GK → List Sym) (hcl : KClean S)
    (hC0 : S sC0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: R0))
    (hC1 : S sC1 = natSyms pin ++ Sym.mark :: R1) :
    Eval ρ phaseA ⟨v, S⟩
      ⟨none, Function.update S sU (List.replicate (2 * b + 2 * K0 + pin + 7) Sym.mark)⟩
      (costA b K0 pin) := by
  have hU : S sU = [] := hcl _
  have hH : S sH = [] := hcl _
  have hG : S sG = [] := hcl _
  have hD : S sD = [] := hcl _
  have hD2 : S sD2 = [] := hcl _
  -- 1
  have e1 := fieldToD_eval sC0 (by decide) (by decide) (by decide) ρ v b _ S hC0 hH hD hD2
  set S1 := Function.update S sD (List.replicate b Sym.mark) with hS1
  -- 2
  have e2 := moveDbl_eval (src := sD) (dst := sU) (by decide) ρ none (List.replicate b Sym.mark)
    S1 (by simp [hS1])
  rw [List.length_replicate] at e2
  set S2 := Function.update (Function.update S1 sD []) sU
    (List.replicate (2 * b) Sym.mark ++ S1 sU) with hS2
  -- 3
  have hS2C0 : S2 sC0 = (encodeNat b).map Sym.bit ++ (Sym.mark :: (natSyms K0 ++ Sym.mark :: R0)) := by
    simp [hS2, hS1, hC0, natSyms]
  have e3 := moveBlock_eval (src := sC0) (dst := sG) (by decide) ρ none (encodeNat b) _ S2
    (TermOK.cons rfl _) hS2C0
  set S3 := Function.update (Function.update S2 sC0 (Sym.mark :: (natSyms K0 ++ Sym.mark :: R0)))
    sG ((encodeNat b).reverse.map Sym.bit ++ S2 sG) with hS3
  -- 4
  have e4 : Eval ρ (popR sC0) ⟨(Sym.mark :: (natSyms K0 ++ Sym.mark :: R0)).head?, S3⟩
      ⟨some Sym.mark, Function.update S3 sC0 (natSyms K0 ++ Sym.mark :: R0)⟩ 1 := by
    refine (Eval.pop ρ sC0 (fun _ o => o) _ S3).of_eq ?_ rfl
    simp [hS3]
  set S4 := Function.update S3 sC0 (natSyms K0 ++ Sym.mark :: R0) with hS4
  -- 5
  have e5 : Eval ρ (pushR sG) ⟨some Sym.mark, S4⟩
      ⟨some Sym.mark, Function.update S4 sG (Sym.mark :: S4 sG)⟩ 1 :=
    Eval.push ρ sG (fun r => r.getD .sep) (some Sym.mark) S4
  set S5 := Function.update S4 sG (Sym.mark :: S4 sG) with hS5
  -- 6
  have e6 := fieldToD_eval sC0 (by decide) (by decide) (by decide) ρ (some Sym.mark) K0 R0 S5
    (by simp [hS5, hS4]) (by simp [hS5, hS4, hS3, hS2, hS1, hH])
    (by simp [hS5, hS4, hS3, hS2]) (by simp [hS5, hS4, hS3, hS2, hS1, hD2])
  set S6 := Function.update S5 sD (List.replicate K0 Sym.mark) with hS6
  -- 7
  have e7 := moveDbl_eval (src := sD) (dst := sU) (by decide) ρ none (List.replicate K0 Sym.mark)
    S6 (by simp [hS6])
  rw [List.length_replicate] at e7
  set S7 := Function.update (Function.update S6 sD []) sU
    (List.replicate (2 * K0) Sym.mark ++ S6 sU) with hS7
  -- 8
  have hS7G : S7 sG = Sym.mark :: (encodeNat b).reverse.map Sym.bit := by
    simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hG]
  have e8 : Eval ρ (popR sG) ⟨none, S7⟩
      ⟨some Sym.mark, Function.update S7 sG ((encodeNat b).reverse.map Sym.bit)⟩ 1 := by
    refine (Eval.pop ρ sG (fun _ o => o) _ S7).of_eq ?_ rfl
    rw [hS7G]; rfl
  set S8 := Function.update S7 sG ((encodeNat b).reverse.map Sym.bit) with hS8
  -- 9
  have e9 : Eval ρ (pushR sC0) ⟨some Sym.mark, S8⟩
      ⟨some Sym.mark, Function.update S8 sC0 (Sym.mark :: S8 sC0)⟩ 1 :=
    Eval.push ρ sC0 (fun r => r.getD .sep) (some Sym.mark) S8
  set S9 := Function.update S8 sC0 (Sym.mark :: S8 sC0) with hS9
  -- 10
  have hS9G : S9 sG = ((encodeNat b).reverse).map Sym.bit ++ [] := by
    simp [hS9, hS8]
  have e10 := moveBlock_eval (src := sG) (dst := sC0) (by decide) ρ (some Sym.mark)
    (encodeNat b).reverse [] S9 TermOK.nil hS9G
  rw [List.reverse_reverse] at e10
  set S10 := Function.update (Function.update S9 sG []) sC0
    ((encodeNat b).map Sym.bit ++ S9 sC0) with hS10
  -- 11
  have e11 := fieldToD_eval sC1 (by decide) (by decide) (by decide) ρ none pin R1 S10
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hC1])
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hH])
    (by simp [hS10, hS9, hS8, hS7])
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hD2])
  set S11 := Function.update S10 sD (List.replicate pin Sym.mark) with hS11
  -- 12
  have e12 := moveAll_eval (src := sD) (dst := sU) (by decide) ρ none (List.replicate pin Sym.mark)
    S11 (by simp [hS11])
  rw [List.length_replicate, List.reverse_replicate] at e12
  set S12 := Function.update (Function.update S11 sD []) sU
    (List.replicate pin Sym.mark ++ S11 sU) with hS12
  -- 13
  have e13 := pushMarks_eval sU ρ none 7 S12
  have hall := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 (Eval.seq e11 (Eval.seq e12 e13)))))))))))
  refine hall.of_eq ?_ (by unfold costA bitLen; simp only [List.length_reverse]; ring)
  congr 1
  funext k
  by_cases h1 : k = sU
  · subst h1
    rw [Function.update_self, Function.update_self]
    have hS12U : S12 sU = List.replicate (pin + 2 * K0 + 2 * b) Sym.mark := by
      simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hU] <;> ring_nf
    rw [hS12U, List.replicate_append_replicate]
    congr 1
    ring
  · by_cases h2 : k = sC0
    · subst h2
      simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hC0, natSyms]
    · by_cases h3 : k = sD
      · subst h3
        simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hD]
      · by_cases h4 : k = sG
        · subst h4
          simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hG]
        · simp [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
            Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            Function.update_of_ne h4]

end SubNLogN.Machine.Pipe.GuardAux

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## Phase B: the scan -/

/-- The register holds a sign symbol. -/
def isSign (v : Option Sym) : Bool := decide (v = some Sym.pos) || decide (v = some Sym.neg)

/-- Loop test of the scan: the top of `S` is not the node end. -/
def notNode (v : Option Sym) : Bool := decide (v ≠ some symNode)

/-- The register is empty. -/
def isNoneB (v : Option Sym) : Bool := v.isNone

/-- A magnitude bit: consume one mark of `V`; on underflow record a mark on `F`. -/
def bitStep : SProg GK := .seq (popR sV) (.ite isNoneB (pushC sF .mark) skip)

/-- One scan step: move the top symbol of `S` to `T` and act on it. -/
def scanBody : SProg GK :=
  .seq (popR sS) <| .seq (pushR sT) <|
  .seq (.ite isSign (copyAll sU sV sX) (.ite optIsBit bitStep (clearM sV))) (peekR sS)

/-- The scan. -/
def scan : SProg GK := .seq (peekR sS) (.loop notNode scanBody)

/-- Marks on `V` after one symbol. -/
def kstep (g : ℕ) (s : Sym) (k : ℕ) : ℕ :=
  if isSign (some s) then g + k else if optIsBit (some s) then k - 1 else 0

/-- Marks added to `F` by one symbol. -/
def fstep (s : Sym) (k : ℕ) : ℕ :=
  if isSign (some s) then 0 else if optIsBit (some s) then (if k = 0 then 1 else 0) else 0

/-- Cost of one scan step. -/
def bodyCost (g : ℕ) (s : Sym) (k : ℕ) : ℕ :=
  if isSign (some s) then 9 * g + 8 else if optIsBit (some s) then 8 else 3 * k + 7

/-- Marks on `V` after a list of symbols. -/
def kfin (g : ℕ) : List Sym → ℕ → ℕ
  | [], k => k
  | s :: l, k => kfin g l (kstep g s k)

/-- Marks added to `F` by a list of symbols. -/
def ffin (g : ℕ) : List Sym → ℕ → ℕ
  | [], _ => 0
  | s :: l, k => fstep s k + ffin g l (kstep g s k)

/-- Cost of the scan loop over a list of symbols. -/
def scost (g : ℕ) : List Sym → ℕ → ℕ
  | [], _ => 1
  | s :: l, k => bodyCost g s k + 1 + scost g l (kstep g s k)

theorem bitStep_eval (ρ : List (SProg GK)) (v : Option Sym) (k f : ℕ) (S : GK → List Sym)
    (hV : S sV = List.replicate k Sym.mark) (hF : S sF = List.replicate f Sym.mark) :
    Eval ρ bitStep ⟨v, S⟩
      ⟨(List.replicate k Sym.mark).head?, Function.update (Function.update S sV
        (List.replicate (k - 1) Sym.mark)) sF
        (List.replicate ((if k = 0 then 1 else 0) + f) Sym.mark)⟩ 3 := by
  have e1 : Eval ρ (popR sV) ⟨v, S⟩ ⟨(List.replicate k Sym.mark).head?,
      Function.update S sV (List.replicate (k - 1) Sym.mark)⟩ 1 := by
    refine (Eval.pop ρ sV (fun _ o => o) v S).of_eq ?_ rfl
    rw [hV, List.tail_replicate]
  set S1 := Function.update S sV (List.replicate (k - 1) Sym.mark) with hS1
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have e2 : Eval ρ (.ite isNoneB (pushC sF .mark) skip) ⟨none, S1⟩
        ⟨none, Function.update S1 sF (Sym.mark :: S1 sF)⟩ 2 :=
      Eval.ite_true (by rfl) (Eval.push ρ sF (fun _ => .mark) none S1)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    simp [hS1, hF, Nat.add_comm 1 f, List.replicate_succ]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e2 : Eval ρ (.ite isNoneB (pushC sF .mark) skip) ⟨some Sym.mark, S1⟩
        ⟨some Sym.mark, S1⟩ 2 :=
      Eval.ite_false (by rfl) (skip_eval ρ _)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    congr 1
    rw [if_neg (by omega), zero_add]
    have h1 : S1 sF = List.replicate f Sym.mark := by simp [hS1, hF]
    rw [← h1, Function.update_eq_self]

theorem scanBody_eval (ρ : List (SProg GK)) (g k f : ℕ) (s : Sym) (rest : List Sym)
    (S : GK → List Sym) (hS : S sS = s :: rest) (hU : S sU = List.replicate g Sym.mark)
    (hX : S sX = []) (hV : S sV = List.replicate k Sym.mark)
    (hF : S sF = List.replicate f Sym.mark) :
    Eval ρ scanBody ⟨some s, S⟩
      ⟨rest.head?, Function.update (Function.update (Function.update (Function.update S sS rest)
        sT (s :: S sT)) sV (List.replicate (kstep g s k) Sym.mark))
        sF (List.replicate (fstep s k + f) Sym.mark)⟩ (bodyCost g s k) := by
  have e1 : Eval ρ (popR sS) ⟨some s, S⟩ ⟨some s, Function.update S sS rest⟩ 1 := by
    refine (Eval.pop ρ sS (fun _ o => o) _ S).of_eq ?_ rfl
    rw [hS]; rfl
  set S1 := Function.update S sS rest with hS1
  have e2 : Eval ρ (pushR sT) ⟨some s, S1⟩ ⟨some s, Function.update S1 sT (s :: S1 sT)⟩ 1 :=
    Eval.push ρ sT (fun r => r.getD .sep) (some s) S1
  set S2 := Function.update S1 sT (s :: S1 sT) with hS2
  have hS2S : S2 sS = rest := by simp [hS2, hS1]
  have hS2U : S2 sU = List.replicate g Sym.mark := by simp [hS2, hS1, hU]
  have hS2X : S2 sX = [] := by simp [hS2, hS1, hX]
  have hS2V : S2 sV = List.replicate k Sym.mark := by simp [hS2, hS1, hV]
  have hS2F : S2 sF = List.replicate f Sym.mark := by simp [hS2, hS1, hF]
  by_cases hsg : isSign (some s) = true
  · have e3 := copyAll_eval (src := sU) (dst := sV) (tmp := sX) (by decide) (by decide)
      (by decide) ρ (some s) _ S2 hS2U hS2X
    rw [List.length_replicate, List.reverse_replicate] at e3
    set S3 := Function.update S2 sV (List.replicate g Sym.mark ++ S2 sV) with hS3
    have e4 : Eval ρ (peekR sS) ⟨none, S3⟩ ⟨rest.head?, S3⟩ 1 := by
      refine (Eval.peek ρ sS (fun _ o => o) _ S3).of_eq ?_ rfl
      simp [hS3, hS2S]
    have hall := Eval.seq e1 (Eval.seq e2 (Eval.seq
      (Eval.ite_true (q := .ite optIsBit bitStep (clearM sV)) hsg e3) e4))
    refine hall.of_eq ?_ (by simp only [bodyCost, if_pos hsg]; ring)
    congr 1
    funext j
    by_cases j1 : j = sF
    · subst j1; simp [hS3, hS2F, fstep, hsg]
    · by_cases j2 : j = sV
      · subst j2
        simp [Function.update_of_ne j1, hS3, hS2V, kstep, hsg]
      · simp [hS3, hS2, hS1, Function.update_of_ne j1, Function.update_of_ne j2]
  · have hsg' : isSign (some s) = false := by simpa using hsg
    by_cases hbit : optIsBit (some s) = true
    · have e3 := bitStep_eval ρ (some s) k f S2 hS2V hS2F
      set S3 := Function.update (Function.update S2 sV (List.replicate (k - 1) Sym.mark)) sF
        (List.replicate ((if k = 0 then 1 else 0) + f) Sym.mark) with hS3
      have e4 : Eval ρ (peekR sS) ⟨(List.replicate k Sym.mark).head?, S3⟩ ⟨rest.head?, S3⟩ 1 := by
        refine (Eval.peek ρ sS (fun _ o => o) _ S3).of_eq ?_ rfl
        simp [hS3, hS2S]
      have hall := Eval.seq e1 (Eval.seq e2
        (Eval.seq (Eval.ite_false (p := copyAll sU sV sX) hsg'
          (Eval.ite_true (q := clearM sV) hbit e3)) e4))
      refine hall.of_eq ?_ (by simp only [bodyCost, if_neg hsg, if_pos hbit])
      congr 1
      funext j
      by_cases j1 : j = sF
      · subst j1; simp [hS3, fstep, hsg, hbit]
      · by_cases j2 : j = sV
        · subst j2; simp [Function.update_of_ne j1, hS3, kstep, hsg, hbit]
        · simp [hS3, hS2, hS1, Function.update_of_ne j1, Function.update_of_ne j2]
    · have hbit' : optIsBit (some s) = false := by simpa using hbit
      have e3 := clearM_eval (k := sV) ρ (some s) _ S2 hS2V
      rw [List.length_replicate] at e3
      set S3 := Function.update S2 sV [] with hS3
      have e4 : Eval ρ (peekR sS) ⟨none, S3⟩ ⟨rest.head?, S3⟩ 1 := by
        refine (Eval.peek ρ sS (fun _ o => o) _ S3).of_eq ?_ rfl
        simp [hS3, hS2S]
      have hall := Eval.seq e1 (Eval.seq e2
        (Eval.seq (Eval.ite_false (p := copyAll sU sV sX) hsg'
          (Eval.ite_false (p := bitStep) hbit' e3)) e4))
      refine hall.of_eq ?_ (by simp only [bodyCost, if_neg hsg, if_neg hbit]; ring)
      congr 1
      funext j
      by_cases j1 : j = sF
      · subst j1; simp [hS3, hS2F, fstep, hsg, hbit]
      · by_cases j2 : j = sV
        · subst j2; simp [Function.update_of_ne j1, hS3, kstep, hsg, hbit]
        · simp [hS3, hS2, hS1, Function.update_of_ne j1, Function.update_of_ne j2]

end SubNLogN.Machine.Pipe.GuardAux

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

theorem scan_loop_eval (ρ : List (SProg GK)) (g : ℕ) (T0 : List Sym)
    (hT0 : T0.head? = some symNode) :
    ∀ (l : List Sym), symNode ∉ l → ∀ (k f : ℕ) (S : GK → List Sym),
      S sS = l ++ T0 → S sU = List.replicate g Sym.mark → S sX = [] →
      S sV = List.replicate k Sym.mark → S sF = List.replicate f Sym.mark →
      Eval ρ (.loop notNode scanBody) ⟨(l ++ T0).head?, S⟩
        ⟨some symNode, Function.update (Function.update (Function.update
          (Function.update S sS T0) sT (l.reverse ++ S sT)) sV
          (List.replicate (kfin g l k) Sym.mark)) sF
          (List.replicate (ffin g l k + f) Sym.mark)⟩ (scost g l k)
  | [], _, k, f, S, hS, _, _, hV, hF => by
    refine (Eval.loop_false (by simp [notNode, hT0])).of_eq ?_ (by simp [scost])
    rw [List.nil_append, hT0]
    congr 1
    funext j
    by_cases j1 : j = sF
    · subst j1; simp [ffin, hF]
    · by_cases j2 : j = sV
      · subst j2; simp [Function.update_of_ne j1, kfin, hV]
      · by_cases j3 : j = sT
        · subst j3; simp [Function.update_of_ne j1, Function.update_of_ne j2]
        · by_cases j4 : j = sS
          · subst j4
            simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3, hS]
          · simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3,
              Function.update_of_ne j4]
  | s :: l, hl, k, f, S, hS, hU, hX, hV, hF => by
    have hs : s ≠ symNode := fun h => hl (h ▸ List.mem_cons_self ..)
    have hl' : symNode ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    have e1 := scanBody_eval ρ g k f s (l ++ T0) S hS hU hX hV hF
    set S1 := Function.update (Function.update (Function.update (Function.update S sS (l ++ T0))
        sT (s :: S sT)) sV (List.replicate (kstep g s k) Sym.mark))
        sF (List.replicate (fstep s k + f) Sym.mark) with hS1
    have ih := scan_loop_eval ρ g T0 hT0 l hl' (kstep g s k) (fstep s k + f) S1
      (by simp [hS1]) (by simp [hS1, hU]) (by simp [hS1, hX]) (by simp [hS1]) (by simp [hS1])
    refine (Eval.loop_true (by simp [notNode, hs]) e1 ih).of_eq ?_ (by simp only [scost]; ring)
    congr 1
    funext j
    by_cases j1 : j = sF
    · subst j1; simp only [Function.update_self, ffin]; congr 1; ring
    · by_cases j2 : j = sV
      · subst j2; simp [Function.update_of_ne j1, kfin]
      · by_cases j3 : j = sT
        · subst j3; simp [Function.update_of_ne j1, Function.update_of_ne j2, hS1]
        · by_cases j4 : j = sS
          · subst j4; simp [Function.update_of_ne j1, Function.update_of_ne j2,
              Function.update_of_ne j3]
          · simp [Function.update_of_ne j1, Function.update_of_ne j2, Function.update_of_ne j3,
              Function.update_of_ne j4, hS1]

/-! ## Counting -/

theorem kstep_bit (g : ℕ) (e : Bool) (k : ℕ) : kstep g (Sym.bit e) k = k - 1 := by
  simp [kstep, isSign, optIsBit]

theorem fstep_bit (e : Bool) (k : ℕ) : fstep (Sym.bit e) k = if k = 0 then 1 else 0 := by
  simp [fstep, isSign, optIsBit]

theorem kstep_sgn (g : ℕ) (z : ℤ) (k : ℕ) : kstep g (sgnSym z) k = g + k := by
  unfold sgnSym; split_ifs <;> simp [kstep, isSign]

theorem fstep_sgn (z : ℤ) (k : ℕ) : fstep (sgnSym z) k = 0 := by
  unfold sgnSym; split_ifs <;> simp [fstep, isSign]

theorem kstep_sep2 (g k : ℕ) : kstep g Sym.sep2 k = 0 := by simp [kstep, isSign, optIsBit]
theorem fstep_sep2 (k : ℕ) : fstep Sym.sep2 k = 0 := by simp [fstep, isSign, optIsBit]
theorem kstep_sep (g k : ℕ) : kstep g Sym.sep k = 0 := by simp [kstep, isSign, optIsBit]
theorem fstep_sep (k : ℕ) : fstep Sym.sep k = 0 := by simp [fstep, isSign, optIsBit]

theorem ffin_bits (g : ℕ) : ∀ (es : List Bool) (k : ℕ) (rest : List Sym),
    ffin g (es.map Sym.bit ++ rest) k = (es.length - k) + ffin g rest (k - es.length)
  | [], k, rest => by simp [ffin]
  | e :: es, k, rest => by
    have ih := ffin_bits g es (k - 1) rest
    simp only [List.map_cons, List.cons_append, ffin, kstep_bit, fstep_bit, List.length_cons]
    rw [ih, Nat.sub_sub, Nat.add_comm 1 es.length]
    split_ifs <;> omega

theorem kfin_bits (g : ℕ) : ∀ (es : List Bool) (k : ℕ) (rest : List Sym),
    kfin g (es.map Sym.bit ++ rest) k = kfin g rest (k - es.length)
  | [], k, rest => by simp [kfin]
  | e :: es, k, rest => by
    have ih := kfin_bits g es (k - 1) rest
    simp only [List.map_cons, List.cons_append, kfin, kstep_bit, List.length_cons]
    rw [ih, Nat.sub_sub, Nat.add_comm 1 es.length]

theorem entrySyms_append (z : ℤ × ℤ) (rest : List Sym) :
    entrySyms z ++ rest = sgnSym z.1 :: ((encodeNat z.1.natAbs).map Sym.bit ++
      (Sym.sep2 :: sgnSym z.2 :: ((encodeNat z.2.natAbs).map Sym.bit ++ (Sym.sep :: rest)))) := by
  simp [entrySyms, intSyms, natSyms]

theorem ffin_entry (g : ℕ) (z : ℤ × ℤ) (rest : List Sym) :
    ffin g (entrySyms z ++ rest) 0 =
      (bitLen z.1.natAbs - g) + (bitLen z.2.natAbs - g) + ffin g rest 0 := by
  rw [entrySyms_append]
  simp only [ffin, kstep_sgn, fstep_sgn, ffin_bits, kfin_bits, kstep_sep2, fstep_sep2, kstep_sep,
    fstep_sep, bitLen]
  omega

theorem kfin_entry (g : ℕ) (z : ℤ × ℤ) (rest : List Sym) (k : ℕ) :
    kfin g (entrySyms z ++ rest) k = kfin g rest 0 := by
  rw [entrySyms_append]
  simp only [kfin, kstep_sgn, kfin_bits, kstep_sep2, kstep_sep]

theorem ffin_entries_eq_zero (g : ℕ) : ∀ zs : List (ℤ × ℤ),
    ffin g (zs.map entrySyms).flatten 0 = 0 ↔
      ∀ z ∈ zs, bitLen z.1.natAbs ≤ g ∧ bitLen z.2.natAbs ≤ g
  | [] => by simp [ffin]
  | z :: zs => by
    rw [List.map_cons, List.flatten_cons, ffin_entry, List.forall_mem_cons,
      ← ffin_entries_eq_zero g zs]
    omega

theorem kfin_entries (g : ℕ) : ∀ zs : List (ℤ × ℤ), kfin g (zs.map entrySyms).flatten 0 = 0
  | [] => by simp [kfin]
  | z :: zs => by
    rw [List.map_cons, List.flatten_cons, kfin_entry, kfin_entries g zs]

theorem ffin_le_length (g : ℕ) : ∀ (l : List Sym) (k : ℕ), ffin g l k ≤ l.length
  | [], _ => by simp [ffin]
  | s :: l, k => by
    have ih := ffin_le_length g l (kstep g s k)
    have h1 : fstep s k ≤ 1 := by unfold fstep; split_ifs <;> omega
    simp only [ffin, List.length_cons]
    omega

/-- Number of sign symbols. -/
def nsgn (l : List Sym) : ℕ := l.countP (fun s => isSign (some s))

theorem nsgn_entries : ∀ zs : List (ℤ × ℤ), nsgn (zs.map entrySyms).flatten = 2 * zs.length
  | [] => by simp [nsgn]
  | z :: zs => by
    have ih := nsgn_entries zs
    unfold nsgn at ih ⊢
    rw [List.map_cons, List.flatten_cons, List.countP_append, ih]
    have h1 : (entrySyms z).countP (fun s => isSign (some s)) = 2 := by
      have hb : ∀ es : List Bool, (es.map Sym.bit).countP (fun s => isSign (some s)) = 0 := by
        intro es; induction es with
        | nil => rfl
        | cons e es ihe => simp [List.countP_cons, isSign, ihe]
      simp only [entrySyms, intSyms, natSyms]
      unfold sgnSym
      split_ifs <;> simp only [List.countP_cons, List.countP_append, hb] <;> simp [isSign]
    rw [h1, List.length_cons]
    ring

theorem scost_le (g : ℕ) : ∀ (l : List Sym) (k : ℕ),
    scost g l k + 3 * kfin g l k ≤ 3 * k + 12 * (g + 1) * nsgn l + 10 * l.length + 1
  | [], k => by simp only [scost, kfin, nsgn, List.countP_nil, List.length_nil]; omega
  | s :: l, k => by
    have ih := scost_le g l (kstep g s k)
    have hn : nsgn (s :: l) = nsgn l + (if isSign (some s) then 1 else 0) := by
      simp [nsgn, List.countP_cons]
    simp only [scost, kfin, List.length_cons, hn]
    unfold bodyCost
    unfold kstep at ih ⊢
    by_cases h1 : isSign (some s) = true
    · simp only [h1, if_true] at ih ⊢
      nlinarith [ih]
    · simp only [h1, if_false, Bool.false_eq_true, Nat.add_zero] at ih ⊢
      by_cases h2 : optIsBit (some s) = true
      · simp only [h2, if_true] at ih ⊢
        omega
      · simp only [h2, if_false, Bool.false_eq_true] at ih ⊢
        omega

end SubNLogN.Machine.Pipe.GuardAux

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-! ## Phases C, D and the program -/

/-- Read the failure flag: register `none` iff `F` is empty; `F` is cleared. -/
def readF : SProg GK :=
  .seq (peekR sF) (.ite isSomeB (.seq (clearM sF) (.seq (pushC sF .mark) (popR sF))) skip)

theorem readF_eval (ρ : List (SProg GK)) (v : Option Sym) (f : ℕ) (S : GK → List Sym)
    (hF : S sF = List.replicate f Sym.mark) :
    ∃ t, t ≤ 3 * f + 7 ∧ Eval ρ readF ⟨v, S⟩
      ⟨if f = 0 then none else some Sym.mark, Function.update S sF []⟩ t := by
  have e0 : Eval ρ (peekR sF) ⟨v, S⟩ ⟨(List.replicate f Sym.mark).head?, S⟩ 1 := by
    refine (Eval.peek ρ sF (fun _ o => o) v S).of_eq ?_ rfl
    rw [hF]
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf
    refine ⟨3, by omega, ?_⟩
    have e1 : Eval ρ (.ite isSomeB (.seq (clearM sF) (.seq (pushC sF .mark) (popR sF))) skip)
        ⟨none, S⟩ ⟨none, S⟩ 2 := Eval.ite_false (by rfl) (skip_eval ρ _)
    refine (Eval.seq e0 e1).of_eq ?_ rfl
    rw [if_pos rfl]
    congr 1
    have h0 : S sF = [] := by rw [hF]; rfl
    rw [← h0, Function.update_eq_self]
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    refine ⟨3 * (f' + 1) + 6, by omega, ?_⟩
    have e1 := clearM_eval (k := sF) ρ (some Sym.mark) _ S hF
    rw [List.length_replicate] at e1
    have e2 : Eval ρ (pushC sF .mark) ⟨none, Function.update S sF []⟩
        ⟨none, Function.update S sF [Sym.mark]⟩ 1 := by
      refine (Eval.push ρ sF (fun _ => .mark) none _).of_eq ?_ rfl
      simp
    have e3 : Eval ρ (popR sF) ⟨none, Function.update S sF [Sym.mark]⟩
        ⟨some Sym.mark, Function.update S sF []⟩ 1 := by
      refine (Eval.pop ρ sF (fun _ o => o) none _).of_eq ?_ rfl
      simp
    have e4 := Eval.ite_true (q := skip) (c := isSomeB)
      (s := ⟨some Sym.mark, S⟩) (by rfl) (Eval.seq e1 (Eval.seq e2 e3))
    refine (Eval.seq e0 e4).of_eq ?_ (by ring)
    rw [if_neg (by omega)]

/-- **The guard program.** -/
def guardProg : SProg GK :=
  .seq phaseA (.seq scan (.seq (moveAll sT sS) (.seq (clearM sU) readF)))

theorem freeBelow_pushMarks (k : GK) (d : ℕ) : ∀ n, (pushMarks k n).FreeBelow d
  | 0 => by simp [pushMarks, skip, Prog.FreeBelow]
  | n + 1 => by simp [pushMarks, pushC, Prog.FreeBelow, freeBelow_pushMarks k d n]

theorem closed_guardProg : guardProg.Closed := by
  simp [Prog.Closed, guardProg, phaseA, fieldToD, horner, hornerBody, moveDbl, moveDblBody,
    moveAll, moveAllBody, moveBlock, moveBits, moveBitsBody, restoreR, popR, peekR, pushR, pushC,
    skip, scan, scanBody, copyAll, moveDup, moveDupBody, bitStep, clearM, clearBody, readF,
    Prog.FreeBelow, freeBelow_pushMarks]

/-! ## Formats -/

theorem node_not_mem_intSyms (z : ℤ) : symNode ∉ intSyms z := by
  simp [intSyms, natSyms, sgnSym, symNode]
  split_ifs <;> simp

theorem node_not_mem_entrySyms (z : ℤ × ℤ) : symNode ∉ entrySyms z := by
  simp only [entrySyms, List.mem_append, List.mem_cons, not_or]
  refine ⟨node_not_mem_intSyms _, by simp [symNode], node_not_mem_intSyms _, by simp [symNode]⟩

theorem node_not_mem_blk (l : List (ℤ × ℤ)) : symNode ∉ (l.map entrySyms).flatten := by
  intro h
  obtain ⟨e, he, hm⟩ := List.mem_flatten.1 h
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
  exact node_not_mem_entrySyms z hm

theorem streamSyms_append_eq (x : Array (ℤ × ℤ)) (restS : List Sym) :
    streamSyms [x] ++ restS =
      (x.toList.map entrySyms).flatten ++ (symNode :: symLevel :: restS) := by
  simp [streamSyms, nodeSyms, blkE, blk]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem costA_le (b K0 pin : ℕ) : costA b K0 pin ≤ 40 * (b + K0 + pin) + 44 := by
  have h1 := fcost_le b
  have h2 := fcost_le K0
  have h3 := fcost_le pin
  have h4 := bitLen_le_self b
  have h5 := bitLen_le_self K0
  have h6 := bitLen_le_self pin
  unfold costA
  omega

end SubNLogN.Machine.Pipe.GuardAux
