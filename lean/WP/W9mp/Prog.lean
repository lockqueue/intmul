import WP.W9mp.GlueP0
import Contracts.W9.Pipeline

/-!
# WP.W9mp.Prog — the root composite of the multiplier, its stage specs and cost arithmetic

`multProg` is the composite of `W9_multiply`. Its stage programs are parameters:

`splitPack ; pushB ; pipeline ; dropTo C1 ; square ; pushP0 ; pipeline ; dropTo C1 ; extract ;
reconstruct`

* `pushB` / `pushP0` put the pipeline's input precision on `C1` (`hdrSyms [b]`, then
  `hdrSyms [rootPrecision b K0]`); `dropTo C1 mark` pops it after each transform, so `C1` is restored.
  The glue (`WP.W9mp.Glue`, `WP.W9mp.GlueP0`) uses three composite scratch stacks `gX`, `gY`, `gT`.
* `SpecPipe` … `SpecRecon` are the stage contract bodies (verbatim from `Contracts.W9.Pipeline` and
  `Contracts.W9.Root`); `SpecMult` is `W9_multiply`'s body.
* `multCost_le`: the composite's cost is within `(Cs + 2·Cp + Cq + Ce + Cr + 200)·(rootBound + …)`.
  Each root stage costs at most `rootBound` (reconstruct's `(k1+k2)·K0 ≤ 2^K0·K0` is covered by the
  `3·(b+K0)·2^K0` term); the glue costs at most `124·rootBound`.
-/

namespace WP.W9mp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync WP.W9comp

attribute [local instance 10000] instZeroIntElementary

/-! ## The stage contract bodies (verbatim) -/

def SpecPipe (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (wd : ℕ → ℕ) (xs : List (Array (ℤ × ℤ)))
    (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
    ChainOK wd cSpec p_in 0 xs →
    σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
    σ (.inl .TR) = tapeSyms cSpec ++ restT → restT.head? ≠ some symPost →
    σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
    Runs P σ (Function.update σ (.inl .S) (streamSyms (levelEvalV cSpec p_in xs) ++ restS))
      (fun _ => True) (C * (pipeBound Mul wd cSpec p_in 0 xs.length + (tapeSyms cSpec).length + 1))

def SpecSplit (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (b K0 k1 k2 A B : ℕ) (σ : BLoc m → List Sym) (rA rB r0 : List Sym),
    A < 2 ^ (b * k1) → B < 2 ^ (b * k2) → k1 + k2 ≤ 2 ^ K0 → TermOK rA → TermOK rB →
    σ (.inl .OA) = natSyms A ++ rA → σ (.inl .OB) = natSyms B ++ rB →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 →
    Runs P σ (Function.update (Function.update (Function.update σ (.inl .OA) rA) (.inl .OB) rB)
        (.inl .S) (streamSyms [rootPackV b K0 k1 k2 A B] ++ σ (.inl .S))) (fun _ => True)
      (C * (b * (k1 + k2) + 2 ^ K0 * (b + 1) + rootHdrLen b K0 k1 k2 + 1))

def SpecSquare (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (b K0 k1 k2 wR : ℕ) (z : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restS r0 : List Sym),
    z.size = 2 ^ K0 → ArrW wR z → ArrW wR (rootSquareV (rootPrecision b K0) K0 z) →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .S) = streamSyms [z] ++ restS →
    Runs P σ (Function.update σ (.inl .S)
        (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS)) (fun _ => True)
      (C * (2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1))

def SpecExtract (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) (σ : BLoc m → List Sym) (restS r0 : List Sym),
    v.size = 2 ^ K0 → k1 + k2 ≤ 2 ^ K0 → ArrW wR v →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .S) = streamSyms [v] ++ restS →
    Runs P σ (Function.update (Function.update σ (.inl .S) restS) (.inl .OA)
        (hdrSyms (rootDigits b K0 k1 k2 v) ++ σ (.inl .OA))) (fun _ => True)
      (C * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1))

def SpecRecon (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) : Prop :=
  ∀ (b K0 k1 k2 wD : ℕ) (cs : List ℕ) (σ : BLoc m → List Sym) (rA r0 : List Sym),
    cs.length = k1 + k2 → k1 + k2 ≤ 2 ^ K0 →
    (∀ c ∈ cs, bitLen c ≤ wD) → TermOK rA →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .OA) = hdrSyms cs ++ rA →
    Runs P σ (Function.update σ (.inl .OA) (natSyms (reconstructChunksTree b cs) ++ rA))
      (fun _ => True) (C * (cs.length * (b + wD + K0 + 1) + rootHdrLen b K0 k1 k2 + 1))

/-- `W9_multiply`'s body. -/
def SpecMult (Mul : ℕ → ℕ) (m : ℕ) (R : Type) (C : ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) :
    Prop :=
  ∀ (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) (wdF wdI : ℕ → ℕ) (wR : ℕ)
    (σ : BLoc m → List Sym) (rA rB r0 restT : List Sym),
    A < 2 ^ (b * k1) → B < 2 ^ (b * k2) → k1 + k2 ≤ 2 ^ K0 → TermOK rA → TermOK rB →
    RootOK cSpec b K0 k1 k2 A B wdF wdI wR →
    σ (.inl .OA) = natSyms A ++ rA → σ (.inl .OB) = natSyms B ++ rB →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .W0) = [] →
    σ (.inl .TR) = tapeSyms cSpec ++ restT → restT.head? ≠ some symPost →
    Runs P σ (Function.update (Function.update σ (.inl .OA)
        (natSyms (computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ rA)) (.inl .OB) rB)
      (fun _ => True)
      (C * (rootBound Mul wR b K0 k1 k2 + pipeBound Mul wdF cSpec b 0 1 +
        pipeBound Mul wdI cSpec (rootPrecision b K0) 0 1 + (tapeSyms cSpec).length + 1))

/-! ## The composite program -/

/-- Registers: one component per stage program and the glue register. -/
abbrev MRegs (R1 R2 R3 R4 R5 : Type) : Type := R1 × R2 × R3 × R4 × R5 × Option Sym

section Lenses

variable (R1 R2 R3 R4 R5 : Type)

def mlP : Lens (MRegs R1 R2 R3 R4 R5) R1 := Lens.fst _ _
def mlS : Lens (MRegs R1 R2 R3 R4 R5) R2 := lsnd (Lens.fst _ _)
def mlQ : Lens (MRegs R1 R2 R3 R4 R5) R3 := lsnd (lsnd (Lens.fst _ _))
def mlE : Lens (MRegs R1 R2 R3 R4 R5) R4 := lsnd (lsnd (lsnd (Lens.fst _ _)))
def mlR : Lens (MRegs R1 R2 R3 R4 R5) R5 := lsnd (lsnd (lsnd (lsnd (Lens.fst _ _))))
def mlg : Lens (MRegs R1 R2 R3 R4 R5) (Option Sym) := lsnd (lsnd (lsnd (lsnd (Lens.snd _ _))))

end Lenses

/-- Glue scratch stacks of the composite (restored by every glue step). -/
def gX {m : ℕ} (hx : 3 ≤ m) : BLoc m := .inr ⟨0, by omega⟩
def gY {m : ℕ} (hx : 3 ≤ m) : BLoc m := .inr ⟨1, by omega⟩
def gT {m : ℕ} (hx : 3 ≤ m) : BLoc m := .inr ⟨2, by omega⟩

/-- **The root composite.** -/
def multProg {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (hx : 3 ≤ m)
    (Pp : Prog (BLoc m1) (fun _ => Sym) R1) (Ps : Prog (BLoc m2) (fun _ => Sym) R2)
    (Pq : Prog (BLoc m3) (fun _ => Sym) R3) (Pe : Prog (BLoc m4) (fun _ => Sym) R4)
    (Pr : Prog (BLoc m5) (fun _ => Sym) R5) :
    Prog (BLoc m) (fun _ => Sym) (MRegs R1 R2 R3 R4 R5) :=
  .seq (callB h2 (mlS R1 R2 R3 R4 R5) Ps) <|
  .seq ((pushB (K := BLoc m) (.inl .C0) (.inl .C1) (gX hx)).liftRegs (mlg R1 R2 R3 R4 R5)) <|
  .seq (callB h1 (mlP R1 R2 R3 R4 R5) Pp) <|
  .seq ((dropTo (K := BLoc m) (.inl .C1) .mark).liftRegs (mlg R1 R2 R3 R4 R5)) <|
  .seq (callB h3 (mlQ R1 R2 R3 R4 R5) Pq) <|
  .seq ((pushP0 (K := BLoc m) (.inl .C0) (.inl .C1) (gX hx) (gY hx) (gT hx)).liftRegs
    (mlg R1 R2 R3 R4 R5)) <|
  .seq (callB h1 (mlP R1 R2 R3 R4 R5) Pp) <|
  .seq ((dropTo (K := BLoc m) (.inl .C1) .mark).liftRegs (mlg R1 R2 R3 R4 R5)) <|
  .seq (callB h4 (mlE R1 R2 R3 R4 R5) Pe) <|
  callB h5 (mlR R1 R2 R3 R4 R5) Pr

theorem multProg_closed {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}
    (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m) (hx : 3 ≤ m)
    {Pp : Prog (BLoc m1) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5}
    (cp : Pp.Closed) (cs : Ps.Closed) (cq : Pq.Closed) (ce : Pe.Closed) (cr : Pr.Closed) :
    (multProg h1 h2 h3 h4 h5 hx Pp Ps Pq Pe Pr).Closed :=
  closed_seq (closed_callB _ _ cs) <| closed_seq (closed_liftRegs _ (closed_pushB _ _ _)) <|
  closed_seq (closed_callB _ _ cp) <| closed_seq (closed_liftRegs _ (closed_dropTo _ _)) <|
  closed_seq (closed_callB _ _ cq) <| closed_seq (closed_liftRegs _ (closed_pushP0 _ _ _ _ _)) <|
  closed_seq (closed_callB _ _ cp) <| closed_seq (closed_liftRegs _ (closed_dropTo _ _)) <|
  closed_seq (closed_callB _ _ ce) <| closed_callB _ _ cr

/-! ## The glue on the composite's stacks -/

section BGlue

variable {m : ℕ} (hx : 3 ≤ m)

theorem runs_pushB_m (b : ℕ) (rest : List Sym) (S : BLoc m → List Sym) (hrest : TermOK rest)
    (hS : S (.inl .C0) = natSyms b ++ rest) :
    Runs (pushB (.inl .C0) (.inl .C1) (gX hx)) S
      (Function.update S (.inl .C1) (hdrSyms [b] ++ S (.inl .C1))) (fun _ => True)
      (7 * bitLen b + 8) :=
  runs_pushB (by simp) (by simp [gX]) (by simp [gX]) b rest S hrest hS

theorem runs_pushP0_m (b K0 : ℕ) (rest0 : List Sym) (S : BLoc m → List Sym)
    (hS : S (.inl .C0) = natSyms b ++ .mark :: (natSyms K0 ++ .mark :: rest0)) :
    Runs (pushP0 (.inl .C0) (.inl .C1) (gX hx) (gY hx) (gT hx)) S
      (Function.update S (.inl .C1) (hdrSyms [rootPrecision b K0] ++ S (.inl .C1)))
      (fun _ => True) (100 * (b + K0 + 1) * (K0 + 1)) :=
  runs_pushP0 (by simp) (by simp [gX]) (by simp [gY]) (by simp [gT]) (by simp [gX])
    (by simp [gY]) (by simp [gT]) (by simp [gX, gY]) (by simp [gX, gT]) (by simp [gY, gT])
    b K0 rest0 S hS

end BGlue

/-! ## Cost arithmetic -/

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- The composite's cost (the chain's right-nested sum) is within
`(Cs + 2·Cp + Cq + Ce + Cr + 200)·(rootBound + pF + pI + L + 1)`. -/
theorem multCost_le (Mul : ℕ → ℕ) (wR b K0 k1 k2 pF pI L Cs Cp Cq Ce Cr : ℕ)
    (hk : k1 + k2 ≤ 2 ^ K0) :
    Cs * (b * (k1 + k2) + 2 ^ K0 * (b + 1) + rootHdrLen b K0 k1 k2 + 1) +
      (7 * bitLen b + 8 +
      (Cp * (pF + L + 1) +
      (2 * bitLen b + 2 +
      (Cq * (2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1) +
      (100 * (b + K0 + 1) * (K0 + 1) +
      (Cp * (pI + L + 1) +
      (2 * bitLen (rootPrecision b K0) + 2 +
      (Ce * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1) +
      Cr * ((k1 + k2) * (b + wR + K0 + 1) + rootHdrLen b K0 k1 k2 + 1))))))))) ≤
    (Cs + 2 * Cp + Cq + Ce + Cr + 200) * (rootBound Mul wR b K0 k1 k2 + pF + pI + L + 1) := by
  have hP : 0 < 2 ^ K0 := Nat.two_pow_pos K0
  have hK : K0 + 1 ≤ 2 ^ K0 := succ_le_two_pow K0
  have hb := WP.W7pure.bitLen_le_self b
  have hp := WP.W7pure.bitLen_le_self (rootPrecision b K0)
  have hp0 : rootPrecision b K0 = 2 * b + 2 * K0 + 6 := rfl
  have hR : rootBound Mul wR b K0 k1 k2 = b * (k1 + k2) +
      2 ^ K0 * (4 * Mul wR + 3 * eb wR + 3 * (b + K0) + 1) + (k1 + k2) * (b + wR + 1) +
      4 * rootHdrLen b K0 k1 k2 + 1 := rfl
  generalize hX : 4 * Mul wR + 3 * eb wR + 3 * (b + K0) + 1 = X at hR
  have a1 : 2 ^ K0 * (b + 1) ≤ 2 ^ K0 * X := Nat.mul_le_mul_left _ (by omega)
  have a2 : 2 ^ K0 * (4 * Mul wR + eb wR + b + K0) ≤ 2 ^ K0 * X :=
    Nat.mul_le_mul_left _ (by omega)
  have a3 : 2 ^ K0 * (eb wR + b + K0) ≤ 2 ^ K0 * X := Nat.mul_le_mul_left _ (by omega)
  have a4 : (k1 + k2) * (b + wR + K0 + 1) = (k1 + k2) * (b + wR + 1) + (k1 + k2) * K0 := by
    ring
  have a5 : (k1 + k2) * K0 ≤ 2 ^ K0 * K0 := Nat.mul_le_mul_right _ hk
  have a6 : 2 ^ K0 * K0 ≤ 2 ^ K0 * X := Nat.mul_le_mul_left _ (by omega)
  have a7 : X ≤ 2 ^ K0 * X := Nat.le_mul_of_pos_left X hP
  have a8 : (b + K0 + 1) * (K0 + 1) ≤ X * 2 ^ K0 := Nat.mul_le_mul (by omega) hK
  have a9 : X * 2 ^ K0 = 2 ^ K0 * X := Nat.mul_comm _ _
  have a10 : 100 * (b + K0 + 1) * (K0 + 1) = 100 * ((b + K0 + 1) * (K0 + 1)) :=
    Nat.mul_assoc _ _ _
  have s1 : b * (k1 + k2) + 2 ^ K0 * (b + 1) + rootHdrLen b K0 k1 k2 + 1 ≤
      rootBound Mul wR b K0 k1 k2 := by omega
  have s2 : 2 ^ K0 * (4 * Mul wR + eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1 ≤
      rootBound Mul wR b K0 k1 k2 := by omega
  have s3 : 2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1 ≤
      rootBound Mul wR b K0 k1 k2 := by omega
  have s4 : (k1 + k2) * (b + wR + K0 + 1) + rootHdrLen b K0 k1 k2 + 1 ≤
      rootBound Mul wR b K0 k1 k2 := by omega
  have g1 : 7 * bitLen b + 8 ≤ 8 * rootBound Mul wR b K0 k1 k2 := by omega
  have g2 : 2 * bitLen b + 2 ≤ 2 * rootBound Mul wR b K0 k1 k2 := by omega
  have g3 : 100 * (b + K0 + 1) * (K0 + 1) ≤ 100 * rootBound Mul wR b K0 k1 k2 := by omega
  have g4 : 2 * bitLen (rootPrecision b K0) + 2 ≤ 14 * rootBound Mul wR b K0 k1 k2 := by omega
  have m1 := Nat.mul_le_mul_left Cs s1
  have m2 := Nat.mul_le_mul_left Cq s2
  have m3 := Nat.mul_le_mul_left Ce s3
  have m4 := Nat.mul_le_mul_left Cr s4
  have m5 : Cp * (pF + L + 1) ≤ Cp * (pF + pI + L + 1) := Nat.mul_le_mul_left _ (by omega)
  have m6 : Cp * (pI + L + 1) ≤ Cp * (pF + pI + L + 1) := Nat.mul_le_mul_left _ (by omega)
  have expand : (Cs + 2 * Cp + Cq + Ce + Cr + 200) * (rootBound Mul wR b K0 k1 k2 + pF + pI + L + 1)
      = Cs * rootBound Mul wR b K0 k1 k2 + Cq * rootBound Mul wR b K0 k1 k2 +
        Ce * rootBound Mul wR b K0 k1 k2 + Cr * rootBound Mul wR b K0 k1 k2 +
        200 * rootBound Mul wR b K0 k1 k2 + Cp * (pF + pI + L + 1) + Cp * (pF + pI + L + 1) +
        (2 * Cp * rootBound Mul wR b K0 k1 k2 + (Cs + Cq + Ce + Cr + 200) * (pF + pI + L + 1)) := by
    ring
  rw [expand]
  omega

#assert_std_axioms multProg_closed runs_pushB_m runs_pushP0_m succ_le_two_pow multCost_le

end WP.W9mp
