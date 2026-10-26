import WP.W9c.PassInst
import WP.W9c.Iface2

/-!
# WP.W9c.RowDefs — the row driver of `W9_spreadRow`: stacks, kit, program

Host `Loc 12 40`: the named stacks in `LB` order (`S W0 TL TR RET RQ C0 C1 C2 C3 OA OB`), then
scratch. Phases:

* **A** markers on the scratch stacks; header (`rowHdr`); `k := s - 1 + 1`;
  `ZR := m1 mod 2^mr`, then `(zl, zr) := (0, r)` or `(r - ZR, ZR)`;
* **B** filter row (`rowTaps`); `ol := W + T - [T ≠ 0]`; the constant `2`; `Pg := pack taps`
  (`blockPack` with `p_in = 0`, `q = 2`, i.e. no quantization); split `W0` (`rowSplit`);
* **C** the two coordinate passes (`passInst`); zip (`rowZip`) into `W0`;
* **D** cleanup: drop the counters, pop the markers.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-- Row host stacks. -/
abbrev RL : Type := Loc 12 40

/-- `S` -/ abbrev rS : RL := .inl 0
/-- `W0` -/ abbrev rW0 : RL := .inl 1
/-- `TL` -/ abbrev rTL : RL := .inl 2
/-- `TR` -/ abbrev rTR : RL := .inl 3
/-- `C0` -/ abbrev rC0 : RL := .inl 6
/-- `C1` -/ abbrev rC1 : RL := .inl 7
/-- real parts -/ abbrev rXR : RL := .inr 0
/-- imaginary parts -/ abbrev rXI : RL := .inr 1
/-- real output -/ abbrev rOR : RL := .inr 2
/-- imaginary output -/ abbrev rOI : RL := .inr 3
/-- `Pg` -/ abbrev rPG : RL := .inr 4
/-- `k` -/ abbrev rK : RL := .inr 5
/-- `p_in` -/ abbrev rPIN : RL := .inr 6
/-- `q` -/ abbrev rQ : RL := .inr 7
/-- `W` -/ abbrev rWW : RL := .inr 8
/-- `zl` -/ abbrev rZL : RL := .inr 9
/-- `zr` -/ abbrev rZR : RL := .inr 10
/-- `ol` -/ abbrev rOL : RL := .inr 11
/-- `m1` -/ abbrev rM1 : RL := .inr 12
/-- `r` -/ abbrev rRR : RL := .inr 13
/-- `log₂ r` -/ abbrev rMR : RL := .inr 14
/-- taps copy -/ abbrev rTP : RL := .inr 15
/-- tap count -/ abbrev rTC : RL := .inr 16
/-- constant 0 -/ abbrev rP0 : RL := .inr 17
/-- constant 2 -/ abbrev rP2 : RL := .inr 18
/-- temporary -/ abbrev rT1 : RL := .inr 19

/-- The sub-programs of the row driver, with register lenses. -/
structure RKit (σ : Type) where
  hd : Inst 9 24 Unit
  lhd : Lens σ hd.R
  tp : Inst 4 24 Unit
  ltp : Lens σ tp.R
  sp : Inst 3 24 Unit
  lsp : Lens σ sp.R
  zp : Inst 3 24 Unit
  lzp : Lens σ zp.R
  pk : Inst 6 24 Unit
  lpk : Lens σ pk.R
  ps : Inst 10 24 Unit
  lps : Lens σ ps.R
  cp : Inst 2 4 Unit
  lcp : Lens σ cp.R
  dr : Inst 1 4 Unit
  ldr : Lens σ dr.R
  iz : Inst 1 4 Bool
  liz : Lens σ iz.R
  ic : Inst 1 4 Unit
  lic : Lens σ ic.R
  dc : Inst 1 4 Unit
  ldc : Lens σ dc.R
  ad : Inst 3 4 Unit
  lad : Lens σ ad.R
  sb : Inst 3 4 Unit
  lsb : Lens σ sb.R
  sa : Inst 3 4 Unit
  lsa : Lens σ sa.R

variable {σ : Type} (K : RKit σ)

/-- Push `mark` on each listed stack. -/
def pushMarks : List RL → HP 12 40 σ
  | [] => TMFw.Lib.skip
  | k :: ks => (pushS k .mark).seq (pushMarks ks)

/-- The scratch stacks that get a marker. -/
def rMarked : List RL :=
  [rXR, rXI, rPG, rK, rPIN, rQ, rWW, rZL, rZR, rOL, rM1, rRR, rMR, rTP, rTC, rP0, rP2, rT1]

/-- `callI` then branch on a zero test of `k`. -/
def ifZero (k : RL) (p q : HP 12 40 σ) : HP 12 40 σ :=
  (callI K.iz [k] rS K.liz).seq (.ite (fun v => K.iz.obs (K.liz.get v)) p q)

/-- Phase A. -/
def rowA : HP 12 40 σ :=
  (pushMarks rMarked).seq
    ((callI K.hd [rC0, rC1, rQ, rM1, rRR, rMR, rWW, rK, rPIN] rS K.lhd).seq
    ((ifZero K rK (callI K.ic [rK] rS K.lic) TMFw.Lib.skip).seq
    ((callI K.cp [rM1, rT1] rS K.lcp).seq
    ((callI K.sa [rT1, rMR, rZR] rS K.lsa).seq
    ((callI K.dr [rT1] rS K.ldr).seq
    (ifZero K rZR (callI K.cp [rRR, rZR] rS K.lcp) (callI K.sb [rRR, rZR, rZL] rS K.lsb)))))))

/-- Phase B. -/
def rowB : HP 12 40 σ :=
  (callI K.tp [rTR, rTL, rTP, rTC] rS K.ltp).seq
    ((callI K.ad [rWW, rTC, rOL] rS K.lad).seq
    ((ifZero K rTC TMFw.Lib.skip (callI K.dc [rOL] rS K.ldc)).seq
    ((pushS rP2 (.bit true)).seq ((pushS rP2 (.bit false)).seq
    ((callI K.pk [rTP, rK, rP0, rP2, rWW, rPG] rS K.lpk).seq
    (callI K.sp [rW0, rXR, rXI] rS K.lsp))))))

/-- Phase C. -/
def rowC : HP 12 40 σ :=
  (callI K.ps [rXR, rPG, rOR, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps).seq
    ((callI K.ps [rXI, rPG, rOI, rK, rPIN, rQ, rWW, rZL, rZR, rOL] rS K.lps).seq
    (callI K.zp [rOR, rOI, rW0] rS K.lzp))

/-- Drop a number and pop its marker. -/
def dropPop (k : RL) : HP 12 40 σ := (callI K.dr [k] rS K.ldr).seq (popS k)

/-- Phase D. -/
def rowD : HP 12 40 σ :=
  (popS rOR).seq ((popS rOI).seq ((popS rPG).seq ((dropPop K rPG).seq
    ((dropPop K rK).seq ((dropPop K rPIN).seq ((dropPop K rQ).seq ((dropPop K rWW).seq
    ((dropPop K rZL).seq ((dropPop K rZR).seq ((dropPop K rOL).seq ((dropPop K rM1).seq
    ((dropPop K rRR).seq ((dropPop K rMR).seq ((dropPop K rTC).seq ((dropPop K rP2).seq
    ((popS rP0).seq ((popS rTP).seq ((popS rT1).seq ((popS rXR).seq (popS rXI))))))))))))))))))))

/-- The row driver. -/
def rowProg : HP 12 40 σ := (rowA K).seq ((rowB K).seq ((rowC K).seq (rowD K)))

theorem pushMarks_closed : ∀ ks : List RL, (pushMarks (σ := σ) ks).Closed
  | [] => trivial
  | _ :: ks => ⟨trivial, pushMarks_closed ks⟩

theorem rowProg_closed : (rowProg K).Closed := by
  refine ⟨⟨pushMarks_closed _, callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _,
    trivial⟩, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩, ?_, ?_, ?_⟩
  · exact ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, trivial,
      callI_closed _ _ _ _⟩, trivial, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  · exact ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩
  · simp only [rowD, dropPop]
    exact ⟨trivial, trivial, trivial, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩,
      ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩, trivial, trivial,
      trivial, trivial, trivial⟩

#assert_std_axioms pushMarks_closed rowProg_closed

end WP.W9c
