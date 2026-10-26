/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.CCore
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Math.Networks.AppCCore
import SubNLogN.Math.Networks.Proofs.Counting

/-!
# C-core skeleton: vocabulary and leaf kernel statements (`CCore/SkelDefs.lean`)

This file states the **leaf kernel contracts** of the recursive C-core (`CCoreStmt`,
`Contracts/CCore.lean`). The skeleton reduction (`CCore/Skel*.lean`) proves `CCoreStmt` from
them. No kernel is implemented here, and nothing about `CCoreStmt` is proved here.
Paper: Lemma A.10 (`lem:transfer-phase`) and Proposition A.11 (`prop:prop14-param`), Sections A.5–A.6.

## Machine protocol (fixed by these statements)
* **Entry state** of a call `t`: `io = Enc t z ++ tio` (`BlkTerm tio`), `desc = t.hdr ++ tdesc`,
  every framed stack (`park`, roles, private scratch) has empty visible content.
* **Node.** `split` moves the array from `io` to the `W` role stacks. Role `u` then holds
  `Enc (compactRT t) (restrictRole t u z) ++ [mark]`; the `mark` is owned by the current call.
  The fixed node code (`cxNodeOps`, with the final relabel fused into `collect`) then runs
  role kernels (`phase`, Lemma A.9 `rowAdd`, `scalarRow`) on the role streams. `collect π` merges
  physical role `π u` into row class `u` and writes the result to `io`.
* **Child call** on role `u`, slot `a`: `roleToIo u ; pushChildHdr a ; recur 0 ; dropChildHdr ;
  ioToRole u`. The other role streams, and the delimiter left on role `u`, are protected tails of
  the child (`SafeRunsIn.frame_tail`). No parking is needed.
* **Leaf** (`t.k = 0` or `e^βd < d^βn`): one closed kernel computes `cCoreVal` on `io` directly.

## Conventions shared by all leaf statements
* Each kernel is a `KContract (CCoreN W) Par`: one cost constant, a fixed finite private scratch
  type `E` and register type `R` chosen before any runtime data, and a closed program. `Par` is
  `Unit` or a *static* index (a role, a slot, a phase kind, a scalar row). `KContract` already
  requires `Nonempty R`.
* Every kernel runs as `Calculus.SafeRunsIn ccoreFramed [] …` on its own layout
  `KLoc (CCoreN W) E`: it never peeks or pops a framed stack (`park`, a role stack) whose visible
  content is empty. The caller embeds it by `SafeRunsIn.callInj`. The private scratch is unframed
  and clean at entry (`KClean S`, as in `CCoreStmt`). Every stack that is not mentioned is
  preserved exactly; the final state is always `Function.update` of `S` or `setRoles` of `S`.
* `io`, `desc` and the private scratch are unframed, so a kernel may read `tio`/`tdesc`. A legacy
  closed `Runs` kernel whose reads hit only unframed stacks is a `SafeRunsIn` by the read-footprint
  bridge (`SafeRunsIn.of_runs_readsIn`, `Calculus/SafeFootprint.lean`), embedded by `callInj`
  with the inner framed set `fun x => ccoreFramed (ι x)`. Only reads of role stacks need native
  safety (e.g. the safe passes of `FramePassSafe`).
* Node-level costs are `C * t.volG` (Lemma A.9: `C * t.volG * (Uτ (e*K) + 1)`). A kernel may assume
  the bands `CCoreBands p P₀ t` for a cutoff `P₀` that it chooses, so that lower-order terms (header
  arithmetic, `log` factors) can be absorbed.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-! ## Fixed numbers, layout, stack names -/

/-- `W = W_c`, the number of role streams. -/
abbrev Wn : ℕ := tripleWc 100
/-- `m`, the branching factor (`e = m^k`). -/
abbrev mn : ℕ := tripleM 100
/-- `s = s_c`, the number of child calls of a node. -/
abbrev sn : ℕ := tripleSc 100

/-- The stack layout of a C-core kernel with private scratch `E`. -/
abbrev CL (E : Type) : Type := KLoc (CCoreN Wn) E

/-- The array stack. -/
abbrev ioL {E : Type} : CL E := .inl .io
/-- The descriptor stack. -/
abbrev descL {E : Type} : CL E := .inl .desc
/-- The parking stack. -/
abbrev parkL {E : Type} : CL E := .inl .park
/-- Role stream `u`. -/
abbrev roleL {E : Type} (u : Fin Wn) : CL E := .inl (.role u)

/-- Replace the content of every role stack by `g`. -/
def setRoles {E : Type} (S : CL E → List Sym) (g : Fin Wn → List Sym) : CL E → List Sym
  | .inl (.role u) => g u
  | k => S k

/-! ## Encodings and contexts -/

/-- The `io` encoding of an array at context `t`: records of width `w_g` at fractional precision
`P + Δ`, in lexicographic address order (as in `CCoreStmt`). -/
noncomputable def Enc (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : List Sym :=
  carrSyms t.wg (encArr (t.P + t.Δ) (layerAddrs t.A t.K t.D t.S hA hS) z)

/-- The compact (role-stream) context: `A` and `R` divided by `W`; every other field unchanged. -/
abbrev compactRT (t : CCoreRT) : CCoreRT := { t with A := t.A / Wn, R := t.R / Wn }

/-- The child context on slot `a` at a parent of depth `k + 1`. -/
abbrev childRT (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ) : CCoreRT :=
  { t with A := t.A / Wn, R := t.R / Wn, k := k, j0 := t.j0 + a.val * mn ^ k, b := b' }

/-- The child header pushed above the parent header: `(childRT t (t.k - 1) a _).hdr` (`b` is not
part of the header). -/
def childHdr (t : CCoreRT) (a : Fin mn) : List Sym := (childRT t (t.k - 1) a 0).hdr

/-- The role embedding `(a, x, s) ↦ (a·W + u, x, s)` of the compact shape into the parent shape. -/
def roleEmb (t : CCoreRT) (u : Fin Wn) :
    LayerAddr (t.A / Wn) t.K t.D t.S → LayerAddr t.A t.K t.D t.S := fun x =>
  (⟨x.1.val * Wn + u.val, by
    have h1 : x.1.val + 1 ≤ t.A / Wn := x.1.isLt
    have h2 : u.val < Wn := u.isLt
    have h3 : t.A / Wn * Wn ≤ t.A := Nat.div_mul_le_self t.A Wn
    have h4 : (x.1.val + 1) * Wn ≤ t.A / Wn * Wn := Nat.mul_le_mul_right _ h1
    have h5 : (x.1.val + 1) * Wn = x.1.val * Wn + Wn := by ring
    omega⟩, x.2.1, x.2.2)

/-- The role stream `u` of an array: its restriction along `roleEmb`, as a compact array. -/
def restrictRole (t : CCoreRT) (u : Fin Wn) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r := fun x => z (roleEmb t u x)

/-! ## Value-level effects of the role kernels (on compact role arrays) -/

open Model in
/-- Run value-level steps (`Step.run`) on a whole compact array. -/
noncomputable def runSteps {A K D S r : ℕ} (ss : List (Step (layerLayout A K D S) (Fin r → ℂ)))
    (w : RArr (LayerAddr A K D S) r) : RArr (LayerAddr A K D S) r :=
  decodeArr (ss.foldl (fun B s => s.run B) (encodeArr w))

/-- The static phase kernels of an internal node (Lemma A.10 (`lem:transfer-phase`)). -/
inductive PhaseKind where
  /-- the source/sink mask `Z_{a,f}` -/
  | zMask (a : Addr 100)
  /-- `Z^{⊗f}` on the selected bits of slot `sl` -/
  | zSlot (sl : Fin mn)
  /-- the scalar `(-i)^f` -/
  | negIPow
  /-- the scalar `i^{27 f}` -/
  | iPow27
  /-- the scalar `-1` -/
  | neg

open Model in
/-- The value-level step of a phase kernel at a node of depth `t.k` (`f = m^(t.k - 1)`), on the
compact role layout. -/
noncomputable def phaseStep (t : CCoreRT) :
    PhaseKind → Step (layerLayout (t.A / Wn) t.K t.D t.S) (Fin t.r → ℂ)
  | .zMask a => zMask t.ρ (mn ^ (t.k - 1)) t.j0 a
  | .zSlot sl => zSlot t.ρ (mn ^ (t.k - 1)) t.j0 sl.val
  | .negIPow => .recMap fun v => ((-Complex.I) ^ (mn ^ (t.k - 1))) • v
  | .iPow27 => .recMap fun v => (Complex.I ^ (27 * mn ^ (t.k - 1))) • v
  | .neg => .recMap fun v => (-1 : ℂ) • v

open Model in
/-- The value-level steps of the Lemma A.9 row addition between slots `p₁`, `p₂` (`coreEdgeOps`
`rowAdd`, with `f = m^(t.k - 1)`), on the compact role layout. -/
noncomputable def rowAddSteps (t : CCoreRT) (p₁ p₂ : Fin mn) :
    List (Step (layerLayout (t.A / Wn) t.K t.D t.S) (Fin t.r → ℂ)) :=
  (packedAddProc (Ly := layerLayout (t.A / Wn) t.K t.D t.S) (β := Fin t.r → ℂ)
    (mn ^ (t.k - 1) * t.K) t.K t.ρ (mn ^ (t.k - 1))
    ⟨1 + (t.j0 + p₂.val * mn ^ (t.k - 1)) * t.K, 1 + (t.j0 + p₁.val * mn ^ (t.k - 1)) * t.K,
      1 + (t.j0 + thirdSlot p₁.val p₂.val * mn ^ (t.k - 1)) * t.K⟩ :
    List (Step (layerLayout (t.A / Wn) t.K t.D t.S) (Fin t.r → ℂ)))

/-- Role indices of the complex network as `Fin W` (`roleIdxC` and `card Role = W_c`). -/
noncomputable def roleIdxN : Role .complex 100 ≃ Fin Wn :=
  roleIdxC.trans (finCongr (cardRole_holds 100).2)

/-- The scalar row `(j, ι, r)` on the vector of aligned role values (`gateOpC`). -/
noncomputable def gateFn (j : Stage) (ι : Fix 100) (r : Fin 8) {rr : ℕ}
    (vals : Fin Wn → Fin rr → ℂ) : Fin Wn → Fin rr → ℂ := fun idx =>
  rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r) ((rowSign j r : ℤ) : ℂ) (fun w => vals (roleIdxN w))
    (roleIdxN.symm idx)

/-- The scalar row on the role streams: pointwise on aligned compact addresses. -/
noncomputable def gateVal (j : Stage) (ι : Fix 100) (r : Fin 8) {A K D S rr : ℕ}
    (w : Fin Wn → RArr (LayerAddr A K D S) rr) : Fin Wn → RArr (LayerAddr A K D S) rr :=
  fun u x => gateFn j ι r (fun u' => w u' x) u

/-- `Uτ(x) = ⌈x^τ⌉₊`, the ghost cost function of Lemma A.9 (`lem:transfer13`) (not computed by any program). -/
noncomputable def Utau (τ : ℝ) (x : ℕ) : ℕ := ⌈(x : ℝ) ^ τ⌉₊

/-! ## Leaf kernel statements -/

/-- **[LEAF] Header test.** Reads the descriptor and returns the leaf flag
`t.k = 0 ∨ e^βd < d^βn` (`e = m^k`) in a register; every stack is restored. -/
def HdrTestStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) Unit fun _ E _ _ R C Pr =>
    ∃ obs : R → Bool, ∀ (t : CCoreRT) (tdesc : List Sym) (S : CL E → List Sym),
      CCoreBands p P₀ t → KClean S → S descL = t.hdr ++ tdesc →
      Calculus.SafeRunsIn ccoreFramed [] Pr S S
        (fun v => obs v = decide (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn)) (C * t.volG)

/-- **[LEAF] Push the child header** (static slot `a`). At a node (`1 ≤ t.k`), prepend
`childHdr t a` to the descriptor stack; the parent header stays below it. -/
def PushChildHdrStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) (Fin mn) fun a E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (tdesc : List Sym) (S : CL E → List Sym),
      CCoreBands p P₀ t → 1 ≤ t.k → KClean S → S descL = t.hdr ++ tdesc →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update S descL (childHdr t a ++ (t.hdr ++ tdesc))) (fun _ => True) (C * t.volG)

/-- **[LEAF] Drop a 12-field header** from the top of the descriptor stack (count-controlled;
never a mark scan, since `hdrSyms` is not `MarkFree`). -/
def DropHdr12Stmt : Prop :=
  KContract (CCoreN Wn) Unit fun _ E _ _ _ C Pr =>
    ∀ (fs : List ℕ) (rest : List Sym) (S : CL E → List Sym),
      fs.length = 12 → KClean S → S descL = hdrSyms fs ++ rest →
      Calculus.SafeRunsIn ccoreFramed [] Pr S (Function.update S descL rest) (fun _ => True)
        (C * ((hdrSyms fs).length + 1))

/-- **[LEAF] Move role stream `u` to `io`** (static `u`; symbol order preserved). The owned
delimiter `mark` stays on the role; `io` holds only its tail `tio` before the move. -/
def RoleToIoStmt : Prop :=
  KContract (CCoreN Wn) (Fin Wn) fun u E _ _ _ C Pr =>
    ∀ (v : List (List Bool)) (tio : List Sym) (S : CL E → List Sym),
      KClean S → S (roleL u) = arrSyms v ++ [Sym.mark] → S ioL = tio →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update (Function.update S (roleL u) [Sym.mark]) ioL (arrSyms v ++ tio))
        (fun _ => True) (C * ((arrSyms v).length + 1))

/-- **[LEAF] Move the array on `io` back to role stream `u`** (static `u`; symbol order
preserved), above the owned delimiter. The end of the array is the `BlkTerm` tail. -/
def IoToRoleStmt : Prop :=
  KContract (CCoreN Wn) (Fin Wn) fun u E _ _ _ C Pr =>
    ∀ (v : List (List Bool)) (tio : List Sym) (S : CL E → List Sym),
      KClean S → BlkTerm tio → S ioL = arrSyms v ++ tio → S (roleL u) = [Sym.mark] →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update (Function.update S ioL tio) (roleL u) (arrSyms v ++ [Sym.mark]))
        (fun _ => True) (C * ((arrSyms v).length + 1))

/-- **[LEAF] Row split.** Distribute the array on `io` into the `W` role streams by
`a = a'·W + u`. Role stream `u` becomes the compact array `restrictRole t u z` followed by an
owned `mark`; `io` keeps its tail. -/
def SplitStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym) (S : CL E → List Sym),
      CCoreBands p P₀ t → Wn ∣ t.A → KClean S → BlkTerm tio →
      S ioL = Enc t hA hS z ++ tio → S descL = t.hdr ++ tdesc → (∀ u, S (roleL u) = []) →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (setRoles (Function.update S ioL tio)
          (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++ [Sym.mark]))
        (fun _ => True) (C * t.volG)

/-- **[LEAF] Collect, with the relabel `π` fused** (static `π`). Physical role `π u` holds row
class `u` of the result `z'`. The kernel writes `Enc t z'` to `io` and empties every role stack,
including the owned delimiters. -/
def CollectStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) (Equiv.Perm (Fin Wn)) fun π E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
      (z' : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym) (S : CL E → List Sym),
      CCoreBands p P₀ t → Wn ∣ t.A → KClean S → BlkTerm tio → S ioL = tio →
      S descL = t.hdr ++ tdesc →
      (∀ u, S (roleL (π u)) = Enc (compactRT t) hA' hS (restrictRole t u z') ++ [Sym.mark]) →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (setRoles (Function.update S ioL (Enc t hA hS z' ++ tio)) (fun _ => []))
        (fun _ => True) (C * t.volG)

/-- **[LEAF] Phase kernel** (static role `u = par.1`, kind `κ = par.2`). Applies `phaseStep t κ`
to role stream `u`. The phases multiply by unit-modulus constants, so a growth bound `b ≤ Δ` of the
input suffices. -/
def PhaseStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) (Fin Wn × PhaseKind) fun par E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
      (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (b : ℕ) (tdesc : List Sym)
      (S : CL E → List Sym),
      CCoreBands p P₀ t → 1 ≤ t.k → ArrGrowth t.P b w → b ≤ t.Δ → KClean S →
      S descL = t.hdr ++ tdesc → S (roleL par.1) = Enc (compactRT t) hA' hS w ++ [Sym.mark] →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update S (roleL par.1)
          (Enc (compactRT t) hA' hS (runSteps [phaseStep t par.2] w) ++ [Sym.mark]))
        (fun _ => True) (C * t.volG)

/-- **[LEAF] Packed row addition, Lemma A.9** (static role `u = par.1`, slots `par.2`). Applies
`rowAddSteps t p₁ p₂` (`packedAddProc`) to role stream `u`, for distinct slots `p₁ ≠ p₂`
(valid edge data has no `p₁ = p₂` row addition). No growth hypothesis: the step moves whole
records. -/
def RowAddStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) (Fin Wn × Fin mn × Fin mn) fun par E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
      (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (tdesc : List Sym)
      (S : CL E → List Sym),
      CCoreBands p P₀ t → 1 ≤ t.k → 6 ≤ t.K → par.2.1 ≠ par.2.2 → KClean S →
      S descL = t.hdr ++ tdesc → S (roleL par.1) = Enc (compactRT t) hA' hS w ++ [Sym.mark] →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update S (roleL par.1)
          (Enc (compactRT t) hA' hS (runSteps (rowAddSteps t par.2.1 par.2.2) w) ++ [Sym.mark]))
        (fun _ => True) (C * (t.volG * (Utau p.τ (t.e * t.K) + 1)))

/-- **[LEAF] Scalar row** (static `(j, ι, r) = par`). Applies `gateFn j ι r` pointwise to the
aligned role streams. The kernel fixes its arithmetic depth `Erow`; inputs have growth bound `b`
with `b + Erow ≤ Δ`. -/
def ScalarRowStmt (p : LayerParams) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) (Stage × Fix 100 × Fin 8) fun par E _ _ _ C Pr =>
    ∃ Erow : ℕ, ∀ (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
      (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (b : ℕ) (tdesc : List Sym)
      (S : CL E → List Sym),
      CCoreBands p P₀ t → (∀ u, ArrGrowth t.P b (w u)) → b + Erow ≤ t.Δ → KClean S →
      S descL = t.hdr ++ tdesc →
      (∀ u, S (roleL u) = Enc (compactRT t) hA' hS (w u) ++ [Sym.mark]) →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (setRoles S (fun u =>
          Enc (compactRT t) hA' hS (gateVal par.1 par.2.1 par.2.2 w u) ++ [Sym.mark]))
        (fun _ => True) (C * t.volG)

/-- **[LEAF] Leaf kernel.** At a leaf (`t.k = 0` or `e^βd < d^βn`), compute `cCoreVal` on `io`
directly (`e` individual kernels and a runtime loop), from the entry state of the call. The
depth hypothesis is the leaf value `8e` of `cDepth`. -/
def LeafStmt (p : LayerParams) (βn βd : ℕ) : Prop :=
  ∃ P₀ : ℕ, KContract (CCoreN Wn) Unit fun _ E _ _ _ C Pr =>
    ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym) (S : CL E → List Sym),
      CCoreBands p P₀ t → ArrGrowth t.P t.b z → t.b + 8 * t.e ≤ t.Δ →
      (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn) → BlkTerm tio →
      S ioL = Enc t hA hS z ++ tio → S descL = t.hdr ++ tdesc →
      (∀ k, ccoreFramed k → S k = []) → KClean S →
      Calculus.SafeRunsIn ccoreFramed [] Pr S
        (Function.update S ioL (Enc t hA hS (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) ++ tio))
        (fun _ => True) (C * (t.e * t.volG))

/-- **All leaf kernels** of the C-core skeleton. -/
def CCoreLeaves (p : LayerParams) (βn βd : ℕ) : Prop :=
  HdrTestStmt p βn βd ∧ PushChildHdrStmt p ∧ DropHdr12Stmt ∧ RoleToIoStmt ∧ IoToRoleStmt ∧
    SplitStmt p ∧ CollectStmt p ∧ PhaseStmt p ∧ RowAddStmt p ∧ ScalarRowStmt p ∧
    LeafStmt p βn βd

end SubNLogN.Machine.CCore
