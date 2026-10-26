import WP.W9c.Tool2
import WP.W9c.Iface

/-!
# WP.W9c.PassDefs — one coordinate pass of the spread row: program and pure model

One pass turns the coordinate values `x` (a number list on `X`) into the `r` cells of one
coordinate of the spread row (pushed, last cell on top, onto `OUT`):

1. **init**: cyclic tape `OUT` (left, `zl` zero cells) / `TR` (right, `zr` zero cells), window
   `WIN` (`W` zeros), markers on the work stacks;
2. **blocks** (`whileTop` while `X` holds a number): `blockPack` → `Pf`, W5 product `Pf·Pg`,
   drop `Pf`, `unpack` (`ol` digits), `window` (emit `W` complete buckets), `cycEmit`;
3. **final**: `cycEmit` of the last window, rewind (all right cells to the left), pop markers.

Stacks (`Loc 10 24`): named `X PG OUT K PIN Q WW ZL ZR OL`, scratch `TR WIN D E PF PP CT TT`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-! ## Pure model -/

/-- The machine's blocks of `W` (fuel `n`). -/
def chunks (W : ℕ) : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, v :: vs => (v :: vs).take W :: chunks W n ((v :: vs).drop W)

/-- Digits of one block: quantize, pack at radix `2^k`, multiply by `Pg`, `ol` balanced digits. -/
def blockDigits (k p_in q ol : ℕ) (Pg : ℤ) (blk : List ℤ) : List ℤ :=
  unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) ol
    (packSignedKronecker ((2 ^ k : ℕ) : ℤ) (blk.map (gQuantizeCoordToScale p_in q)) * Pg)

/-- All digit lists of a pass. -/
def passDigits (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ) : List (List ℤ) :=
  (chunks W x.length x).map (blockDigits k p_in q ol Pg)

/-- The global emitted bucket list of a pass. -/
def passEmit (k p_in q W ol : ℕ) (Pg : ℤ) (x : List ℤ) : List ℤ :=
  emitAll W (List.replicate W 0) (passDigits k p_in q W ol Pg x)

/-- The cells a pass computes. -/
def passCells (k p_in q W r z ol : ℕ) (Pg : ℤ) (x : List ℤ) : List ℤ :=
  (cycAdd r (List.replicate r 0) z (passEmit k p_in q W ol Pg x)).1

/-- `outLen` of the snapshot's block product (`|blockF| = W ≥ 1`). -/
def outLenOf (W : ℕ) (taps : List ℤ) : ℕ := if taps = [] then W else W + taps.length - 1

/-! ## Stacks -/

/-- Pass host stacks. -/
abbrev PL : Type := Loc 10 24

/-- input values -/ abbrev pX : PL := .inl 0
/-- packed taps -/ abbrev pPG : PL := .inl 1
/-- output (tape left) -/ abbrev pOUT : PL := .inl 2
/-- slot width `k` -/ abbrev pK : PL := .inl 3
/-- `p_in` -/ abbrev pPIN : PL := .inl 4
/-- `q` -/ abbrev pQ : PL := .inl 5
/-- block size `W` -/ abbrev pWW : PL := .inl 6
/-- initial left cells `zl` -/ abbrev pZL : PL := .inl 7
/-- initial right cells `zr` -/ abbrev pZR : PL := .inl 8
/-- digits per block `ol` -/ abbrev pOL : PL := .inl 9
/-- tape right -/ abbrev pTR : PL := .inr 0
/-- window -/ abbrev pWIN : PL := .inr 1
/-- digits -/ abbrev pD : PL := .inr 2
/-- emitted buckets -/ abbrev pE : PL := .inr 3
/-- block pack -/ abbrev pPF : PL := .inr 4
/-- product -/ abbrev pPP : PL := .inr 5
/-- counter -/ abbrev pCT : PL := .inr 6
/-- move temp -/ abbrev pTT : PL := .inr 7

/-! ## The kit: instances and register lenses -/

/-- The sub-programs a pass calls, each with a register lens. -/
structure PKit (σ : Type) where
  lS : Lens σ (Option Sym)
  pk : Inst 6 24 Unit
  lpk : Lens σ pk.R
  up : Inst 4 24 Unit
  lup : Lens σ up.R
  wn : Inst 4 24 Unit
  lwn : Lens σ wn.R
  ce : Inst 3 24 Unit
  lce : Lens σ ce.R
  mu : Inst 3 8 Unit
  lmu : Lens σ mu.R
  cp : Inst 2 4 Unit
  lcp : Lens σ cp.R
  dr : Inst 1 4 Unit
  ldr : Lens σ dr.R
  iz : Inst 1 4 Bool
  liz : Lens σ iz.R
  dc : Inst 1 4 Unit
  ldc : Lens σ dc.R

/-! ## Programs -/

/-- A number starts with a sign symbol. -/
def isSgn : Sym → Bool
  | .pos => true
  | .neg => true
  | _ => false

variable {σ : Type} (K : PKit σ)

/-- Push one zero cell `[pos, sep]`. -/
def zeroCell (dst : PL) : HP 10 24 σ := (pushS dst .sep).seq (pushS dst .pos)

/-- Push `n` zero cells onto `dst`, `n` read from `src` (copied to the counter `CT`). -/
def pushZeros (src dst : PL) : HP 10 24 σ :=
  (pushS pCT .mark).seq ((callI K.cp [src, pCT] pX K.lcp).seq
    ((cdLoop K.iz K.dc K.liz K.ldc pCT pX (zeroCell dst)).seq (popS pCT)))

/-- Initialisation. -/
def passInit : HP 10 24 σ :=
  (pushS pOUT .mark).seq ((pushS pTR .mark).seq ((pushZeros K pZL pOUT).seq
    ((pushZeros K pZR pTR).seq ((pushS pWIN .mark).seq ((pushZeros K pWW pWIN).seq
    ((pushS pD .mark).seq ((pushS pE .mark).seq ((pushS pPF .mark).seq (pushS pPP .mark)))))))))

/-- One block. -/
def blockBody : HP 10 24 σ :=
  (callI K.pk [pX, pK, pPIN, pQ, pWW, pPF] pX K.lpk).seq
    ((callI K.mu [pPF, pPG, pPP] pX K.lmu).seq
    ((popS pPF).seq ((callI K.dr [pPF] pX K.ldr).seq
    ((callI K.up [pPP, pK, pOL, pD] pX K.lup).seq
    ((callI K.wn [pD, pWIN, pE, pWW] pX K.lwn).seq
    (callI K.ce [pE, pOUT, pTR] pX K.lce))))))

/-- Final emit, rewind, markers. -/
def passFinal : HP 10 24 σ :=
  (callI K.ce [pWIN, pOUT, pTR] pX K.lce).seq
    ((whileTop K.lS pTR isSgn (mvNum K.lS pTR pOUT pTT)).seq
    ((popS pTR).seq ((popS pWIN).seq ((popS pD).seq ((popS pE).seq ((popS pPF).seq
      (popS pPP)))))))

/-- The pass. -/
def passProg : HP 10 24 σ :=
  (passInit K).seq ((whileTop K.lS pX isSgn (blockBody K)).seq (passFinal K))

theorem passProg_closed : (passProg K).Closed := by
  refine ⟨?_, whileTop_closed _ _ _ ?_, ?_⟩
  · refine ⟨trivial, trivial, ?_, ?_, trivial, ?_, trivial, trivial, trivial, trivial⟩ <;>
      exact ⟨trivial, callI_closed _ _ _ _, cdLoop_closed _ _ _ _ _ _ ⟨trivial, trivial⟩, trivial⟩
  · exact ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  · exact ⟨callI_closed _ _ _ _, whileTop_closed _ _ _ (mvNum_closed _ _ _ _), trivial, trivial,
      trivial, trivial, trivial, trivial⟩

#assert_std_axioms passProg_closed

end WP.W9c
