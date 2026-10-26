/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.RotateBlock
import SubNLogN.Machine.K1.RotatePure

/-!
# K1, K4-ctl (`K1/RotateFiber.lean`): layout and the rotation of one fiber

**Scope (honest summary).** The stack layout of the controlled-rotation kernel and the proof
(no `sorry`) that `fibProg` rotates one fiber (`runs_fib_fst`, from the steps `runs_fib_pow`,
`runs_fib_cnt`, `runs_fib_tail` and the cost bookkeeping `fib_cost_arith`). Paper: Lemma A.4
(`lem:transfer-streams`, proof: "the target fiber consists of `Q` consecutive
suffix blocks, and a rotation splits it at the computed cut and concatenates the two intervals in
the opposite order".

## Layout (`RotL Eo = KLoc (Fin 8) (Eo ⊕ Fin 14)`)
Named stacks as in `K4RotateCtlStmt`: `0` source, `1` destination, `2..7` the counters
`b1, n1, b2, n2, b, s`. `Eo` is the offset routine's private scratch. Own scratch (`Fin 14`):
`C1, C2` (control counters), `O` (offset), `L1, L2, Lb` (unary depth counters), `N1c, N2c, Sc`
(working down-counters), `Kb` (unary build counter), `Tm` (temporary), `H, H2` (holding stacks),
`U` (output staging, up orientation). Registers `Option Sym × Ro` (work register; the routine's).

## The fiber program (`fibProg`), for a fiber `f` of `Q = q^b` blocks of `s` records
1. offset routine on `(b, C1, C2) → O` (above a guard): `o = off b c1 c2 < Q`;
2. `powLoop` over the `Q` blocks: each block of `s` records goes `src → H` (records reversed);
3. `cntLoop` on `O`: `o` times, the last block on `H` goes back to `H2` (normal orientation);
4. three rewinds: `H2 → U`, `H → H2`, `H2 → U`, so `U` gains the reversed `A2 ++ A1`, where
   `A1 ++ A2 = f` and `A2` is the last `o` blocks: this is `rotB Q s o f`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Layout -/

/-- Private scratch of the rotation kernel: the offset routine's and fourteen own stacks. -/
abbrev RotE (Eo : Type) : Type := Eo ⊕ Fin 14

/-- Stacks of the rotation kernel. -/
abbrev RotL (Eo : Type) : Type := KLoc (Fin 8) (RotE Eo)

/-- Registers of the rotation kernel: a work register and the offset routine's registers. -/
abbrev RotR (Ro : Type) : Type := Option Sym × Ro

section Names

variable {Eo : Type}

/-- Named `0`: the source. -/
abbrev rSrc : RotL Eo := .inl 0
/-- Named `1`: the destination. -/
abbrev rDst : RotL Eo := .inl 1
/-- Named `2`: the counter `b1`. -/
abbrev rB1 : RotL Eo := .inl 2
/-- Named `3`: the counter `n1`. -/
abbrev rN1 : RotL Eo := .inl 3
/-- Named `4`: the counter `b2`. -/
abbrev rB2 : RotL Eo := .inl 4
/-- Named `5`: the counter `n2`. -/
abbrev rN2 : RotL Eo := .inl 5
/-- Named `6`: the counter `b`. -/
abbrev rB : RotL Eo := .inl 6
/-- Named `7`: the counter `s`. -/
abbrev rS : RotL Eo := .inl 7
/-- Own: the control counter `c1`. -/
abbrev rC1 : RotL Eo := .inr (.inr 0)
/-- Own: the control counter `c2`. -/
abbrev rC2 : RotL Eo := .inr (.inr 1)
/-- Own: the offset. -/
abbrev rO : RotL Eo := .inr (.inr 2)
/-- Own: unary depth counter for `b1`. -/
abbrev rL1 : RotL Eo := .inr (.inr 3)
/-- Own: unary depth counter for `b2`. -/
abbrev rL2 : RotL Eo := .inr (.inr 4)
/-- Own: unary depth counter for `b`. -/
abbrev rLb : RotL Eo := .inr (.inr 5)
/-- Own: working counter of the `n1` loop. -/
abbrev rN1c : RotL Eo := .inr (.inr 6)
/-- Own: working counter of the `n2` loop. -/
abbrev rN2c : RotL Eo := .inr (.inr 7)
/-- Own: working counter of the block loops (`s`). -/
abbrev rSc : RotL Eo := .inr (.inr 8)
/-- Own: working counter when building a unary counter. -/
abbrev rKb : RotL Eo := .inr (.inr 9)
/-- Own: temporary of counter operations. -/
abbrev rTm : RotL Eo := .inr (.inr 10)
/-- Own: holding stack `H`. -/
abbrev rH : RotL Eo := .inr (.inr 11)
/-- Own: holding stack `H2`. -/
abbrev rH2 : RotL Eo := .inr (.inr 12)
/-- Own: output staging `U` (up orientation). -/
abbrev rU : RotL Eo := .inr (.inr 13)

/-- Extensionality over the rotation kernel's stacks, by cases (the routine's scratch family `Eo`
is handled uniformly, never enumerated). -/
theorem rotL_funext {f g : RotL Eo → List Sym} (hn : ∀ i : Fin 8, f (.inl i) = g (.inl i))
    (he : ∀ e, f (.inr (.inl e)) = g (.inr (.inl e)))
    (ho : ∀ i : Fin 14, f (.inr (.inr i)) = g (.inr (.inr i))) : f = g := by
  funext k
  rcases k with i | e | i
  · exact hn i
  · exact he e
  · exact ho i

/-- The offset routine's stacks inside the kernel: `0 ↦ b`, `1 ↦ C1`, `2 ↦ C2`, `3 ↦ O`. -/
def embO : KLoc (Fin 4) Eo → RotL Eo
  | .inl i => if i = 0 then rB else if i = 1 then rC1 else if i = 2 then rC2 else rO
  | .inr e => .inr (.inl e)

theorem embO_injective : Function.Injective (embO : KLoc (Fin 4) Eo → RotL Eo) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [embO]
  · fin_cases i <;> simp [embO] at h
  · fin_cases j <;> simp [embO] at h
  · simp only [embO, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

end Names

/-- Lens onto the work register. -/
def rlO {Ro : Type} : Lens (RotR Ro) (Option Sym) := Lens.fst _ _

/-- Lens onto the offset routine's registers. -/
def rlR {Ro : Type} : Lens (RotR Ro) Ro := Lens.snd _ _

/-! ## The offset routine -/

/-- The spec in `K4OffsetCtlStmt off J` (`Contracts/Streams.lean:617`), for one program `P` with
constant `C`. -/
def OffSpec (off : ℕ → ℕ → ℕ → ℕ) (J : ℕ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (b c1 c2 : ℕ) (r0 r1 r2 : List Sym) (S : KLoc (Fin 4) E → List Sym),
    TermOK r0 → TermOK r1 → TermOK r2 →
    S (.inl 0) = natSyms b ++ r0 → S (.inl 1) = natSyms c1 ++ r1 →
    S (.inl 2) = natSyms c2 ++ r2 →
    Runs P S (Function.update S (.inl 3) (natSyms (off b c1 c2) ++ S (.inl 3)))
      (fun _ => True) (C * (b + bitLen c1 + bitLen c2 + 1) ^ J)

theorem runs_callO {Eo Ro : Type} [DecidableEq Eo] {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po)
    (B : RotL Eo → List Sym) (b c1 c2 : ℕ) (r0 r1 r2 : List Sym) (hr0 : TermOK r0)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hb : B rB = natSyms b ++ r0)
    (h1 : B rC1 = natSyms c1 ++ r1) (h2 : B rC2 = natSyms c2 ++ r2) :
    Runs (callInj embO (rlR (Ro := Ro)) Po) B
      (Function.update B rO (natSyms (off b c1 c2) ++ B rO)) (fun _ => True)
      (Co * (b + bitLen c1 + bitLen c2 + 1) ^ J) := by
  have he : (embO (.inl 3) : RotL Eo) = rO := by simp [embO]
  have hP := hO b c1 c2 r0 r1 r2 (B ∘ embO) hr0 hr1 hr2 (by simpa [embO] using hb)
    (by simpa [embO] using h1) (by simpa [embO] using h2)
  refine runs_callInj (Q := fun _ => True) embO_injective rlR ?_ ?_
  · rw [← he, Function.update_comp_eq_of_injective B embO_injective]
    exact hP
  · intro k hk
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hk (.inl 3) he

/-! ## Chunk bookkeeping -/

theorem take_chunk {α : Type} (m k : ℕ) (l : List α) :
    l.take (k * m) ++ chunk m k l = l.take ((k + 1) * m) := by
  rw [chunk, Nat.add_mul, Nat.one_mul, List.take_add]

theorem sum_vol_chunk (m : ℕ) (l : List (List Bool)) :
    ∀ n, ((List.range n).map fun k => vol (chunk m k l)).sum = vol (l.take (n * m))
  | 0 => by simp [vol_nil]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_vol_chunk m l n, ← take_chunk,
      vol_append]
    simp

/-! ## Fiber-level states -/

section FibStates

variable {Eo : Type} [DecidableEq Eo]

/-- Fiber-level stacks: source, `O`, `H`, `H2`, `U` set, everything else from `B`. -/
def fst (B : RotL Eo → List Sym) (src O H H2 U : List Sym) : RotL Eo → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B
    rSrc src) rO O) rH H) rH2 H2) rU U

variable (B : RotL Eo → List Sym) (src O H H2 U : List Sym)

@[simp] theorem fst_src : fst B src O H H2 U rSrc = src := by simp [fst]
@[simp] theorem fst_O : fst B src O H H2 U rO = O := by simp [fst]
@[simp] theorem fst_H : fst B src O H H2 U rH = H := by simp [fst]
@[simp] theorem fst_H2 : fst B src O H H2 U rH2 = H2 := by simp [fst]
@[simp] theorem fst_U : fst B src O H H2 U rU = U := by simp [fst]
@[simp] theorem fst_B : fst B src O H H2 U rB = B rB := by simp [fst]
@[simp] theorem fst_S : fst B src O H H2 U rS = B rS := by simp [fst]
@[simp] theorem fst_C1 : fst B src O H H2 U rC1 = B rC1 := by simp [fst]
@[simp] theorem fst_C2 : fst B src O H H2 U rC2 = B rC2 := by simp [fst]
@[simp] theorem fst_Lb : fst B src O H H2 U rLb = B rLb := by simp [fst]
@[simp] theorem fst_Sc : fst B src O H H2 U rSc = B rSc := by simp [fst]
@[simp] theorem fst_Kb : fst B src O H H2 U rKb = B rKb := by simp [fst]
@[simp] theorem fst_Tm : fst B src O H H2 U rTm = B rTm := by simp [fst]

@[simp] theorem fst_upd_src (x : List Sym) :
    Function.update (fst B src O H H2 U) rSrc x = fst B x O H H2 U := by
  apply rotL_funext <;> intros <;> simp [fst, Function.update_apply] <;> split_ifs <;> simp_all

@[simp] theorem fst_upd_O (x : List Sym) :
    Function.update (fst B src O H H2 U) rO x = fst B src x H H2 U := by
  apply rotL_funext <;> intros <;> simp [fst, Function.update_apply] <;> split_ifs <;> simp_all

@[simp] theorem fst_upd_H (x : List Sym) :
    Function.update (fst B src O H H2 U) rH x = fst B src O x H2 U := by
  apply rotL_funext <;> intros <;> simp [fst, Function.update_apply] <;> split_ifs <;> simp_all

@[simp] theorem fst_upd_H2 (x : List Sym) :
    Function.update (fst B src O H H2 U) rH2 x = fst B src O H x U := by
  apply rotL_funext <;> intros <;> simp [fst, Function.update_apply] <;> split_ifs <;> simp_all

@[simp] theorem fst_upd_U (x : List Sym) :
    Function.update (fst B src O H H2 U) rU x = fst B src O H H2 x := by
  apply rotL_funext <;> intros <;> simp [fst, Function.update_apply] <;> split_ifs <;> simp_all

theorem fst_self : fst B (B rSrc) (B rO) (B rH) (B rH2) (B rU) = B := by
  simp only [fst, Function.update_eq_self]

theorem fst_upd_comm (k : RotL Eo) (x : List Sym) (h1 : k ≠ rSrc) (h2 : k ≠ rO) (h3 : k ≠ rH)
    (h4 : k ≠ rH2) (h5 : k ≠ rU) :
    Function.update (fst B src O H H2 U) k x = fst (Function.update B k x) src O H H2 U := by
  funext k'
  simp only [fst, Function.update_apply]
  split_ifs <;> simp_all

theorem fst_apply_ne (k : RotL Eo) (h1 : k ≠ rSrc) (h2 : k ≠ rO) (h3 : k ≠ rH) (h4 : k ≠ rH2)
    (h5 : k ≠ rU) : fst B src O H H2 U k = B k := by
  simp only [fst, Function.update_apply]
  split_ifs <;> simp_all

end FibStates

/-! ## The fiber program -/

section Fiber

variable {Eo Ro : Type}

/-- A work-register program inside the rotation kernel. -/
abbrev rwk (p : SProg (RotL Eo)) : Prog (RotL Eo) (fun _ => Sym) (RotR Ro) := p.liftRegs rlO

/-- **Rotation of one fiber** (see the module docstring). -/
def fibProg (q : ℕ) (Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro) :
    Prog (RotL Eo) (fun _ => Sym) (RotR Ro) :=
  .seq (rwk (pushC rO .mark)) (.seq (callInj embO rlR Po) (.seq (rwk (pushC rH .mark))
  (.seq (powLoop rlO q rB rLb rKb rTm (blkMove rlO rS rSc rTm rSrc rH))
  (.seq (rwk (pushC rH2 .mark)) (.seq (cntLoop rlO rO rTm (blkMoveRev rlO rS rSc rTm rH rH2))
  (.seq (rwk (dropBits rO)) (.seq (rwk (WP.W9comp.rewindTo rH2 rU .mark))
  (.seq (rwk (pushC rH2 .mark)) (.seq (rwk (WP.W9comp.rewindTo rH rH2 .mark))
    (rwk (WP.W9comp.rewindTo rH2 rU .mark)))))))))))

variable [DecidableEq Eo]

omit [DecidableEq Eo] in
theorem closed_fibProg (q : ℕ) {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro}
    (hPo : Po.Closed) : (fibProg q Po).Closed :=
  ⟨closed_pushC_lift _ _ _, closed_callInj _ _ hPo, closed_pushC_lift _ _ _,
    closed_powLoop _ _ _ _ _ _ (closed_blkMove _ _ _ _ _ _), closed_pushC_lift _ _ _,
    closed_cntLoop _ _ _ (closed_blkMoveRev _ _ _ _ _ _), closed_dropBits_lift _ _,
    WP.W9comp.closed_rewind _ _ _ _, closed_pushC_lift _ _ _, WP.W9comp.closed_rewind _ _ _ _,
    WP.W9comp.closed_rewind _ _ _ _⟩

/-- Cost factor of one fiber (per symbol of the fiber). -/
def fibK (q : ℕ) : ℕ := 4 * q + 250

theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ arrSyms v := by
  intro h
  rcases mem_arrSyms h with h | ⟨b, h⟩ <;> cases h

theorem mark_not_mem_rev_arrSyms (v : List (List Bool)) : Sym.mark ∉ (arrSyms v).reverse := by
  rw [List.mem_reverse]
  exact mark_not_mem_arrSyms v

/-- Step 4 of `fibProg`: the `q^b` blocks of `f` go from the source to `H` (reversed). -/
theorem runs_fib_pow (q : ℕ) (B : RotL Eo → List Sym) (f w : List (List Bool))
    (rest : List Sym) (b s : ℕ) (rb rs : List Sym) (hrb : TermOK rb) (hrs : TermOK rs)
    (hf : f.length = q ^ b * s) (hbS : B rB = natSyms b ++ rb) (hsS : B rS = natSyms s ++ rs)
    (O1 H0 H20 U0 : List Sym) :
    Runs (powLoop (rlO (Ro := Ro)) q rB rLb rKb rTm (blkMove rlO rS rSc rTm rSrc rH))
      (fst B (arrSyms (f ++ w) ++ rest) O1 (Sym.mark :: H0) H20 U0)
      (fst B (arrSyms w ++ rest) O1 ((arrSyms f).reverse ++ Sym.mark :: H0) H20 U0)
      (fun _ => True)
      (enumE q (fun k => 3 * vol (chunk s k f) + 16 * s + 13 * bitLen s + 12) b 0 +
        19 * b + 13 * bitLen b + 17) := by
  set St : ℕ → RotL Eo → List Sym := fun k => fst B (arrSyms (f.drop (k * s) ++ w) ++ rest)
    O1 ((arrSyms (f.take (k * s))).reverse ++ Sym.mark :: H0) H20 U0 with hSt
  have x4 := runs_powLoop (rlO (Ro := Ro)) q (bs := rB) (L := rLb) (Kc := rKb) (t := rTm)
    (by simp) (by simp) (by simp) (by simp) (by simp) (blkMove rlO rS rSc rTm rSrc rH)
    (closed_blkMove _ _ _ _ _ _) St b rb hrb (by simp [hSt, hbS]) (by simp [hSt])
    (fun k => 3 * vol (chunk s k f) + 16 * s + 13 * bitLen s + 12)
    (fun k hk => by
      have hlen : (chunk s k f).length = s :=
        length_chunk (by rw [hf]; exact Nat.mul_le_mul_right _ hk)
      have hm := runs_blkMove (σ := RotR Ro) rlO (sS := rS) (Sc := rSc) (Tm := rTm) (src := rSrc)
        (H := rH) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (Function.update (St k) rLb (Sym.mark :: St 0 rLb)) (chunk s k f)
        (f.drop ((k + 1) * s) ++ w) rest s rs hrs hlen
        (by simp [hSt, drop_chunk s k f]) (by simp [hSt, hsS])
      refine WP.W9comp.runs_congr hm ?_
      have hH : (arrSyms (chunk s k f)).reverse ++
          ((arrSyms (f.take (k * s))).reverse ++ Sym.mark :: H0) =
          (arrSyms (f.take ((k + 1) * s))).reverse ++ Sym.mark :: H0 := by
        rw [← take_chunk, arrSyms_append, List.reverse_append, List.append_assoc]
      apply rotL_funext <;> intros <;> simp [hSt, fst, Function.update_apply, hH] <;>
        split_ifs <;> simp_all)
  have h40 : St 0 = fst B (arrSyms (f ++ w) ++ rest) O1 (Sym.mark :: H0) H20 U0 := by
    simp [hSt, arrSyms_nil]
  have h4Q : St (q ^ b) = fst B (arrSyms w ++ rest) O1
      ((arrSyms f).reverse ++ Sym.mark :: H0) H20 U0 := by
    simp only [hSt, ← hf, List.drop_length, List.take_length, List.nil_append]
  rw [h40, h4Q] at x4
  exact x4

/-- Step 6 of `fibProg`: `o` blocks come back from `H` to `H2`, in normal orientation. -/
theorem runs_fib_cnt (q : ℕ) (B : RotL Eo → List Sym) (f w : List (List Bool))
    (rest : List Sym) (b s o : ℕ) (rs : List Sym) (hrs : TermOK rs)
    (hf : f.length = q ^ b * s) (ho : o < q ^ b) (hsS : B rS = natSyms s ++ rs)
    (O0 H0 H20 U0 : List Sym) :
    Runs (cntLoop (rlO (Ro := Ro)) rO rTm (blkMoveRev rlO rS rSc rTm rH rH2))
      (fst B (arrSyms w ++ rest) (natSyms o ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) (Sym.mark :: H20) U0)
      (fst B (arrSyms w ++ rest) (Sym.mark :: O0)
        ((arrSyms (f.take ((q ^ b - o) * s))).reverse ++ Sym.mark :: H0)
        (arrSyms (f.drop ((q ^ b - o) * s)) ++ Sym.mark :: H20) U0)
      (fun _ => True)
      (((List.range o).map fun j =>
          3 * vol (chunk s (q ^ b - 1 - j) f) + 22 * s + 13 * bitLen s + 12).sum +
        16 * o + 6 * bitLen o + 2) := by
  set St' : ℕ → RotL Eo → List Sym := fun j => fst B (arrSyms w ++ rest) O0
    ((arrSyms (f.take ((q ^ b - j) * s))).reverse ++ Sym.mark :: H0)
    (arrSyms (f.drop ((q ^ b - j) * s)) ++ Sym.mark :: H20) U0 with hSt'
  have x6 := runs_cntLoop (rlO (Ro := Ro)) (Kc := rO) (t := rTm) (by simp)
    (blkMoveRev rlO rS rSc rTm rH rH2) St' (Sym.mark :: O0) (TermOK.cons rfl _) o
    (fun j => 3 * vol (chunk s (q ^ b - 1 - j) f) + 22 * s + 13 * bitLen s + 12)
    (fun j hj => by
      have hjq : q ^ b - 1 - j + 1 = q ^ b - j := by omega
      have hlen : (chunk s (q ^ b - 1 - j) f).length = s :=
        length_chunk (by rw [hf, hjq]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      have hm := runs_blkMoveRev (σ := RotR Ro) rlO (sS := rS) (Sc := rSc) (Tm := rTm) (H := rH)
        (H2 := rH2) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (Function.update (St' j) rO (natSyms (o - (j + 1)) ++ Sym.mark :: O0))
        (f.take ((q ^ b - 1 - j) * s)) (chunk s (q ^ b - 1 - j) f) (Sym.mark :: H0)
        (TermOK.cons rfl _) s rs hrs hlen
        (by simp [hSt', take_chunk, hjq]) (by simp [hSt', hsS])
      refine WP.W9comp.runs_congr hm ?_
      have hH2 : arrSyms (chunk s (q ^ b - 1 - j) f) ++
          (arrSyms (f.drop ((q ^ b - j) * s)) ++ Sym.mark :: H20) =
          arrSyms (f.drop ((q ^ b - (j + 1)) * s)) ++ Sym.mark :: H20 := by
        rw [show q ^ b - (j + 1) = q ^ b - 1 - j by omega, drop_chunk s (q ^ b - 1 - j) f, hjq,
          arrSyms_append, List.append_assoc]
      have hj1 : q ^ b - (j + 1) = q ^ b - 1 - j := by omega
      apply rotL_funext <;> intros <;> simp [hSt', fst, Function.update_apply, hH2, hj1] <;>
        split_ifs <;> simp_all)
  have h60 : Function.update (St' 0) rO (natSyms o ++ Sym.mark :: O0) =
      fst B (arrSyms w ++ rest) (natSyms o ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) (Sym.mark :: H20) U0 := by
    simp only [hSt', Nat.sub_zero, ← hf, List.drop_length, List.take_length, arrSyms_nil,
      List.nil_append, fst_upd_O]
  have h6o : Function.update (St' o) rO (Sym.mark :: O0) =
      fst B (arrSyms w ++ rest) (Sym.mark :: O0)
        ((arrSyms (f.take ((q ^ b - o) * s))).reverse ++ Sym.mark :: H0)
        (arrSyms (f.drop ((q ^ b - o) * s)) ++ Sym.mark :: H20) U0 := by
    simp only [hSt', fst_upd_O]
  rw [h60, h6o] at x6
  exact x6

/-- Steps 7-11 of `fibProg`: drop the guard of `O`, then the three rewinds. -/
theorem runs_fib_tail (B : RotL Eo → List Sym) (A1 A2 : List (List Bool)) (src : List Sym)
    (O0 H0 H20 U0 : List Sym) :
    Runs (.seq (rwk (Ro := Ro) (dropBits rO)) (.seq (rwk (WP.W9comp.rewindTo rH2 rU .mark))
      (.seq (rwk (pushC rH2 .mark)) (.seq (rwk (WP.W9comp.rewindTo rH rH2 .mark))
        (rwk (WP.W9comp.rewindTo rH2 rU .mark))))))
      (fst B src (Sym.mark :: O0) ((arrSyms A1).reverse ++ Sym.mark :: H0)
        (arrSyms A2 ++ Sym.mark :: H20) U0)
      (fst B src O0 H0 H20 ((arrSyms (A2 ++ A1)).reverse ++ U0)) (fun _ => True)
      (3 * vol A2 + 6 * vol A1 + 11) := by
  have x7 : Runs (rwk (Ro := Ro) (dropBits rO))
      (fst B src (Sym.mark :: O0) ((arrSyms A1).reverse ++ Sym.mark :: H0)
        (arrSyms A2 ++ Sym.mark :: H20) U0)
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) (arrSyms A2 ++ Sym.mark :: H20) U0)
      (fun _ => True) (2 * ([] : List Bool).length + 2) :=
    WP.W9comp.runs_congr (runs_wk_dropBits rlO rO [] Sym.mark O0 _ rfl (by simp)) (by simp)
  have x8 : Runs (rwk (Ro := Ro) (WP.W9comp.rewindTo rH2 rU .mark))
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) (arrSyms A2 ++ Sym.mark :: H20) U0)
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) H20 ((arrSyms A2).reverse ++ U0))
      (fun _ => True) (3 * (arrSyms A2).length + 2) :=
    WP.W9comp.runs_congr (WP.W9comp.runs_rewind rlO (src := rH2) (dst := rU) (by simp) Sym.mark
      (arrSyms A2) H20 _ (mark_not_mem_arrSyms _) (by simp)) (by simp)
  have x9 : Runs (rwk (Ro := Ro) (pushC rH2 .mark))
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) H20 ((arrSyms A2).reverse ++ U0))
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) (Sym.mark :: H20)
        ((arrSyms A2).reverse ++ U0)) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rH2 Sym.mark _) (by simp)
  have x10 : Runs (rwk (Ro := Ro) (WP.W9comp.rewindTo rH rH2 .mark))
      (fst B src O0 ((arrSyms A1).reverse ++ Sym.mark :: H0) (Sym.mark :: H20)
        ((arrSyms A2).reverse ++ U0))
      (fst B src O0 H0 (arrSyms A1 ++ Sym.mark :: H20) ((arrSyms A2).reverse ++ U0))
      (fun _ => True) (3 * ((arrSyms A1).reverse).length + 2) :=
    WP.W9comp.runs_congr (WP.W9comp.runs_rewind rlO (src := rH) (dst := rH2) (by simp) Sym.mark
      (arrSyms A1).reverse H0 _ (mark_not_mem_rev_arrSyms _) (by simp)) (by simp)
  have x11 : Runs (rwk (Ro := Ro) (WP.W9comp.rewindTo rH2 rU .mark))
      (fst B src O0 H0 (arrSyms A1 ++ Sym.mark :: H20) ((arrSyms A2).reverse ++ U0))
      (fst B src O0 H0 H20 ((arrSyms (A2 ++ A1)).reverse ++ U0))
      (fun _ => True) (3 * (arrSyms A1).length + 2) :=
    WP.W9comp.runs_congr (WP.W9comp.runs_rewind rlO (src := rH2) (dst := rU) (by simp) Sym.mark
      (arrSyms A1) H20 _ (mark_not_mem_arrSyms _) (by simp)) (by simp [arrSyms_append])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq x7 (WP.W9comp.runs_seq x8
    (WP.W9comp.runs_seq x9 (WP.W9comp.runs_seq x10 x11)))) (fun _ h => h) ?_
  simp only [List.length_nil, List.length_reverse]
  have e1 : (arrSyms A2).length = vol A2 := rfl
  have e2 : (arrSyms A1).length = vol A1 := rfl
  omega

/-- The cost bookkeeping of one fiber. -/
theorem fib_cost_arith (q b s o T2 : ℕ) (f : List (List Bool)) (hq : 2 ≤ q) (hs1 : 1 ≤ s)
    (hf : f.length = q ^ b * s) (ho : o < q ^ b) :
    1 + (T2 + (1 + ((enumE q (fun k => 3 * vol (chunk s k f) + 16 * s + 13 * bitLen s + 12) b 0
      + 19 * b + 13 * bitLen b + 17) + (1 + ((((List.range o).map fun j =>
        3 * vol (chunk s (q ^ b - 1 - j) f) + 22 * s + 13 * bitLen s + 12).sum +
        16 * o + 6 * bitLen o + 2) + (3 * vol (f.drop ((q ^ b - o) * s)) +
        6 * vol (f.take ((q ^ b - o) * s)) + 11)))))) ≤ T2 + fibK q * vol f := by
  have hQ1 : 1 ≤ q ^ b := Nat.one_le_pow _ _ (by omega)
  have hbQ : b + 1 ≤ q ^ b := by
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
    omega
  have hV : f.length ≤ vol f := length_le_vol f
  have hQs : q ^ b ≤ q ^ b * s := Nat.le_mul_of_pos_right _ hs1
  have hvolA : vol (f.take ((q ^ b - o) * s)) + vol (f.drop ((q ^ b - o) * s)) = vol f := by
    rw [← vol_append, List.take_append_drop]
  have hbits := bitLen_le_self' s
  have hbitb := bitLen_le_self' b
  have hbito := bitLen_le_self' o
  have hT : ∀ k, 3 * vol (chunk s k f) + 16 * s + 13 * bitLen s + 12 ≤
      3 * (vol (chunk s k f) + 10 * s) + 12 := fun k => by omega
  have henum := enumE_le q hq _ (fun k => vol (chunk s k f) + 10 * s) 3 12 (q ^ b)
    (fun k _ => hT k) b 0 (by simp)
  have hwsum : wsum (fun k => vol (chunk s k f) + 10 * s) 0 (q ^ b) =
      vol f + q ^ b * (10 * s) := by
    simp only [wsum, Nat.zero_add]
    rw [listSum_range, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← listSum_range, sum_vol_chunk, ← hf, List.take_length]
  rw [hwsum] at henum
  have hsub : ∑ j ∈ Finset.range o, vol (chunk s (q ^ b - 1 - j) f) ≤ vol f := by
    calc ∑ j ∈ Finset.range o, vol (chunk s (q ^ b - 1 - j) f)
        ≤ ∑ j ∈ Finset.range (q ^ b), vol (chunk s (q ^ b - 1 - j) f) :=
          Finset.sum_le_sum_of_subset (by
            intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega)
      _ = ∑ j ∈ Finset.range (q ^ b), vol (chunk s j f) :=
          Finset.sum_range_reflect (fun j => vol (chunk s j f)) _
      _ = vol f := by
          rw [← listSum_range, sum_vol_chunk, ← hf, List.take_length]
  have hsumO : ((List.range o).map fun j =>
      3 * vol (chunk s (q ^ b - 1 - j) f) + 22 * s + 13 * bitLen s + 12).sum ≤
      3 * vol f + o * (35 * s + 12) := by
    rw [listSum_range, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, ← Finset.mul_sum]
    nlinarith [hsub]
  have hoQ : o * (35 * s + 12) ≤ q ^ b * (35 * s + 12) := Nat.mul_le_mul_right _ ho.le
  have hqV : q * q ^ b ≤ q * vol f := Nat.mul_le_mul_left _ (by omega)
  unfold fibK
  nlinarith [henum, hsumO, hoQ, hqV, hvolA, hV, hQs, hbQ, hbits, hbitb, hbito]

/-- **One fiber, in `fst` form**: the fiber `f` (`q^b` blocks of `s` records) leaves the source
and its rotation by `off b c1 c2` blocks is staged, reversed, on `U`. -/
theorem runs_fib_fst {off : ℕ → ℕ → ℕ → ℕ} {J Co : ℕ}
    {Po : Prog (KLoc (Fin 4) Eo) (fun _ => Sym) Ro} (hO : OffSpec off J Co Po) (q : ℕ)
    (hq : 2 ≤ q) (B : RotL Eo → List Sym) (f w : List (List Bool)) (rest : List Sym)
    (b c1 c2 s : ℕ) (rb r1 r2 rs : List Sym) (hrb : TermOK rb) (hr1 : TermOK r1)
    (hr2 : TermOK r2) (hrs : TermOK rs) (hs1 : 1 ≤ s) (hf : f.length = q ^ b * s)
    (hoff : off b c1 c2 < q ^ b) (hbS : B rB = natSyms b ++ rb)
    (hC1 : B rC1 = natSyms c1 ++ r1) (hC2 : B rC2 = natSyms c2 ++ r2)
    (hsS : B rS = natSyms s ++ rs) (O0 H0 H20 U0 : List Sym) :
    Runs (fibProg q Po) (fst B (arrSyms (f ++ w) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms w ++ rest) O0 H0 H20
        ((arrSyms (rotB (q ^ b) s (off b c1 c2) f)).reverse ++ U0))
      (fun _ => True) (Co * (b + bitLen c1 + bitLen c2 + 1) ^ J + fibK q * vol f) := by
  have x1 : Runs (rwk (Ro := Ro) (pushC rO .mark))
      (fst B (arrSyms (f ++ w) ++ rest) O0 H0 H20 U0)
      (fst B (arrSyms (f ++ w) ++ rest) (Sym.mark :: O0) H0 H20 U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rO Sym.mark _) (by simp)
  have x2 : Runs (callInj embO (rlR (Ro := Ro)) Po)
      (fst B (arrSyms (f ++ w) ++ rest) (Sym.mark :: O0) H0 H20 U0)
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off b c1 c2) ++ Sym.mark :: O0) H0 H20 U0)
      (fun _ => True) (Co * (b + bitLen c1 + bitLen c2 + 1) ^ J) :=
    WP.W9comp.runs_congr (runs_callO hO _ b c1 c2 rb r1 r2 hrb hr1 hr2 (by simp [hbS])
      (by simp [hC1]) (by simp [hC2])) (by simp)
  have x3 : Runs (rwk (Ro := Ro) (pushC rH .mark))
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off b c1 c2) ++ Sym.mark :: O0) H0 H20 U0)
      (fst B (arrSyms (f ++ w) ++ rest) (natSyms (off b c1 c2) ++ Sym.mark :: O0)
        (Sym.mark :: H0) H20 U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rH Sym.mark _) (by simp)
  have x4 := runs_fib_pow (Ro := Ro) q B f w rest b s rb rs hrb hrs hf hbS hsS
    (natSyms (off b c1 c2) ++ Sym.mark :: O0) H0 H20 U0
  have x5 : Runs (rwk (Ro := Ro) (pushC rH2 .mark))
      (fst B (arrSyms w ++ rest) (natSyms (off b c1 c2) ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) H20 U0)
      (fst B (arrSyms w ++ rest) (natSyms (off b c1 c2) ++ Sym.mark :: O0)
        ((arrSyms f).reverse ++ Sym.mark :: H0) (Sym.mark :: H20) U0) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_wk_pushC rlO rH2 Sym.mark _) (by simp)
  have x6 := runs_fib_cnt (Ro := Ro) q B f w rest b s (off b c1 c2) rs hrs hf hoff hsS
    O0 H0 H20 U0
  have x7 := runs_fib_tail (Ro := Ro) B (f.take ((q ^ b - off b c1 c2) * s))
    (f.drop ((q ^ b - off b c1 c2) * s)) (arrSyms w ++ rest) O0 H0 H20 U0
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq x1 (WP.W9comp.runs_seq x2
    (WP.W9comp.runs_seq x3 (WP.W9comp.runs_seq x4 (WP.W9comp.runs_seq x5
    (WP.W9comp.runs_seq x6 x7)))))) (fun _ h => h) ?_
  exact fib_cost_arith q b s (off b c1 c2) _ f hq hs1 hf hoff

end Fiber

end SubNLogN.Machine.K1.Rot
