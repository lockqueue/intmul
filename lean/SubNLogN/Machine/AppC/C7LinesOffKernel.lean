/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesOffBody

/-!
# Lemma A.9 offset routine: the kernel (`Machine/AppC/C7LinesOffKernel.lean`)

`offMain neg xF par` computes `natSyms (lineOff ε par xF k1 k2 b c1 c2)` onto the destination
(`neg = decide (ε = -1)`):
* `k1 = 0`: nothing to push (`lineOff … 0 … = 0`).
* `k1 ≥ 1`: `setupG` places mark floors on the field stacks, copies the control `x` (bits read)
  and the tested chunk `o`, and the counters `D = k2`, `KM = k1 - 1`, `E2 = 2 k1`, `W = b + k2`,
  and the countdown counter `b`. Then `countdown` runs `body` `b` times (`r_loop`). Finally
  `post` strips the high zero bits of the output stack, moves it onto the destination (LSB on
  top), and drops every scratch number together with its floor (`r_post`).
Cost `≤ 900 (b + |c1| + |c2| + |k1| + |k2| + 1)^2 + 2`. Main result: `c7LinesOff_holds`
(namespace `SubNLogN.Machine`). Fully proved. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7LinesOffAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith
  SubNLogN.Machine.Calculus SubNLogN.Math.Networks SubNLogN.Machine.AppC.C7LinesAux

/-! ## Size facts -/

theorem lt_two_pow_self' : ∀ n : ℕ, n < 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have := lt_two_pow_self' n
    rw [pow_succ]
    omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt' (lt_two_pow_self' n)

theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  apply bitLen_le_of_lt'
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem bitLen_add_self_le (n : ℕ) : bitLen (n + n) ≤ bitLen n + 1 := by
  apply bitLen_le_of_lt'
  have := lt_two_pow_bitLen n
  rw [pow_succ]
  omega

theorem distR_le {k1 : ℕ} (hk1 : 1 ≤ k1) (k2 p : ℕ) : distR k1 k2 p ≤ k1 + k2 := by
  by_cases hp : p ≤ k2
  · rw [distR_below k1 k2 p hp]
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, p = k2 + t := ⟨p - k2, by omega⟩
    rw [distR_above k1 k2 hk1 t]
    have := Nat.mod_lt (k1 - t % k1) (by omega : 0 < k1)
    omega

theorem sum_map_const_range (K : ℕ) : ∀ n, ((List.range n).map (fun _ => K)).sum = n * K
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_const_range K n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-! ## Setup -/

abbrev nB : Stk := .inl 0
abbrev nC1 : Stk := .inl 1
abbrev nC2 : Stk := .inl 2
abbrev nK1 : Stk := .inl 4
abbrev nK2 : Stk := .inl 5

/-- Setup, with the control sources `xs` (bits read) and `os` (bits tested). -/
def setupG (xs os : Stk) : OProg :=
  .seq (pushMark (loc .X)) <| .seq (copyN xs (loc .X) sT1) <|
  .seq (pushMark (loc .O)) <| .seq (copyN os (loc .O) sT1) <|
  .seq (pushMark (loc .D)) <| .seq (copyN nK2 (loc .D) sT1) <|
  .seq (pushMark (loc .KM)) <| .seq (copyN nK1 (loc .KM) sT1) <|
  .seq ((dec (loc .KM) sT1).liftRegs lW) <|
  .seq (pushMark (loc .E2)) <| .seq (copyN nK1 (loc .E2) sT1) <| .seq (dblN (loc .E2)) <|
  .seq (pushMark (loc .W)) <| .seq (addN nB nK2 (loc .W) sT1 sT2 sT3) <|
  .seq (pushMark (loc .Cn)) <| .seq (copyN nB (loc .Cn) sT1) <|
  .seq (pushMark (loc .Out)) (pushMark (loc .F))

theorem closed_setupG (xs os : Stk) : (setupG xs os).Closed :=
  ⟨closed_pushMark _, closed_copyN _ _ _, closed_pushMark _, closed_copyN _ _ _,
    closed_pushMark _, closed_copyN _ _ _, closed_pushMark _, closed_copyN _ _ _,
    WP.W9comp.closed_liftRegs lW (FramePassRAux.closed_dec _ _),
    closed_pushMark _, closed_copyN _ _ _, closed_dblN _, closed_pushMark _,
    closed_addN _ _ _ _ _ _, closed_pushMark _, closed_copyN _ _ _, closed_pushMark _,
    closed_pushMark _⟩

theorem r_setupG (S : Stk → List Sym) {xs os : Stk} (hxN : fldOf xs = none)
    (hoN : fldOf os = none) (hxT : xs ≠ sT1) (hoT : os ≠ sT1) {xv ov k1 k2 b : ℕ}
    {rx ro r4 r5 r0 : List Sym} (hrx : TermOK rx) (hro : TermOK ro) (h4 : TermOK r4)
    (h5 : TermOK r5) (h0 : TermOK r0) (hxs : S xs = natSyms xv ++ rx)
    (hos : S os = natSyms ov ++ ro) (hS4 : S nK1 = natSyms k1 ++ r4)
    (hS5 : S nK2 = natSyms k2 ++ r5) (hS0 : S nB = natSyms b ++ r0) (hk1 : 1 ≤ k1) :
    RunsIn [] (setupG xs os) (stk S (ofS S))
      (stk S ⟨natSyms xv ++ Sym.mark :: S (loc .X), natSyms ov ++ Sym.mark :: S (loc .O),
        natSyms k2 ++ Sym.mark :: S (loc .D), natSyms (k1 - 1) ++ Sym.mark :: S (loc .KM),
        natSyms (k1 + k1) ++ Sym.mark :: S (loc .E2),
        natSyms (b + k2) ++ Sym.mark :: S (loc .W), natSyms b ++ Sym.mark :: S (loc .Cn),
        Sym.mark :: S (loc .Out), Sym.mark :: S (loc .F), S (loc .Dst)⟩) (fun _ => True)
      (7 * bitLen xv + 7 * bitLen ov + 20 * bitLen k1 + 27 * bitLen k2 + 27 * bitLen b +
        100) := by
  have hxX : xs ≠ loc .X := fun h => by rw [h, fldOf_loc] at hxN; cases hxN
  have hoO : os ≠ loc .O := fun h => by rw [h, fldOf_loc] at hoN; cases hoN
  have hK4 : fldOf nK1 = none := rfl
  have hK5 : fldOf nK2 = none := rfl
  have hB0 : fldOf nB = none := rfl
  have h := RunsIn.seq (r_pushMark S (ofS S) .X) <|
    RunsIn.seq (r_copyN S hxX hxT _ xv rx hrx (by rw [stk_none S _ hxN]; exact hxs)) <|
    RunsIn.seq (r_pushMark S _ .O) <|
    RunsIn.seq (r_copyN S hoO hoT _ ov ro hro (by rw [stk_none S _ hoN]; exact hos)) <|
    RunsIn.seq (r_pushMark S _ .D) <|
    RunsIn.seq (r_copyN S (src := nK2) (f := .D) (by decide) (by decide) _ k2 r5 h5
      (by rw [stk_none S _ hK5]; exact hS5)) <|
    RunsIn.seq (r_pushMark S _ .KM) <|
    RunsIn.seq (r_copyN S (src := nK1) (f := .KM) (by decide) (by decide) _ k1 r4 h4
      (by rw [stk_none S _ hK4]; exact hS4)) <|
    RunsIn.seq (r_dec S _ .KM (k1 - 1) (Sym.mark :: S (loc .KM)) (termOK_mark _)
      (by rw [Nat.sub_add_cancel hk1] <;> rfl)) <|
    RunsIn.seq (r_pushMark S _ .E2) <|
    RunsIn.seq (r_copyN S (src := nK1) (f := .E2) (by decide) (by decide) _ k1 r4 h4
      (by rw [stk_none S _ hK4]; exact hS4)) <|
    RunsIn.seq (r_dblN S _ .E2 k1 (Sym.mark :: S (loc .E2)) (termOK_mark _) (by rfl)) <|
    RunsIn.seq (r_pushMark S _ .W) <|
    RunsIn.seq (r_addN S (x := nB) (y := nK2) (f := .W) (by decide) _ b k2 r0 r5 h0 h5
      (by rw [stk_none S _ hB0]; exact hS0) (by rw [stk_none S _ hK5]; exact hS5)) <|
    RunsIn.seq (r_pushMark S _ .Cn) <|
    RunsIn.seq (r_copyN S (src := nB) (f := .Cn) (by decide) (by decide) _ b r0 h0
      (by rw [stk_none S _ hB0]; exact hS0)) <|
    RunsIn.seq (r_pushMark S _ .Out) (r_pushMark S _ .F)
  refine RunsIn.mono h (fun _ h => h) ?_
  have hz := zerosLead_le_length (encodeNat (k1 - 1 + 1))
  simp only [Nat.sub_add_cancel hk1] at hz
  simp only [Nat.sub_add_cancel hk1, bitLen]
  omega

/-! ## The scan loop -/

theorem r_loop (S : Stk → List Sym) (neg : Bool) (k1 k2 b par x o : ℕ) (hpar : par ≤ 1)
    (hk1 : 1 ≤ k1) :
    RunsIn [] (countdown lW (loc .Cn) sT1 (body neg par))
      (stk S ((cAt S neg k1 k2 b par x o 0).set .Cn (natSyms b ++ Sym.mark :: S (loc .Cn))))
      (stk S (cAt S neg k1 k2 b par x o b)) (fun _ => True)
      (b * (25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) + 16 * b + 2) := by
  have hB : ∀ n, n < b → RunsIn [] (body neg par)
      (Function.update (stk S (cAt S neg k1 k2 b par x o (b - (n + 1)))) (loc .Cn)
        (natSyms (n + 1) ++ Sym.mark :: S (loc .Cn)))
      (Function.update (stk S (cAt S neg k1 k2 b par x o (b - n))) (loc .Cn)
        (natSyms (n + 1) ++ Sym.mark :: S (loc .Cn))) (fun _ => True)
      (25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) := by
    intro n hn
    rw [upd_stk, upd_stk]
    have h := r_body S neg k1 k2 b par x o (b - (n + 1)) hpar (by omega)
      (natSyms (n + 1) ++ Sym.mark :: S (loc .Cn))
    rw [show b - (n + 1) + 1 = b - n by omega] at h
    refine RunsIn.mono h (fun _ h => h) ?_
    have e1 := bitLen_add_self_le k1
    have e2 : bitLen (distR k1 k2 (b - (n + 1))) ≤ bitLen k1 + bitLen k2 + 1 :=
      (bitLen_mono'' (distR_le hk1 k2 _)).trans (bitLen_add_le k1 k2)
    have e3 : bitLen (k1 - 1) ≤ bitLen k1 := bitLen_mono'' (Nat.sub_le k1 1)
    have e4 : bitLen (b - (b - (n + 1)) + k2) ≤ bitLen b + bitLen k2 + 1 :=
      (bitLen_mono'' (by omega : b - (b - (n + 1)) + k2 ≤ b + k2)).trans (bitLen_add_le b k2)
    omega
  have hc := runsIn_countdown (ρ := []) lW (c := loc .Cn) (t := sT1) (by decide)
    (body := body neg par) b (Sym.mark :: S (loc .Cn)) (termOK_mark _)
    (fun m => stk S (cAt S neg k1 k2 b par x o (b - m)))
    (fun _ => 25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) hB
  simp only [Nat.sub_self, Nat.sub_zero] at hc
  rw [upd_stk, upd_stk] at hc
  have e : (cAt S neg k1 k2 b par x o b).set .Cn (Sym.mark :: S (loc .Cn)) =
      cAt S neg k1 k2 b par x o b := Sc.set_get _ .Cn
  rw [e] at hc
  refine RunsIn.mono hc (fun _ _ => trivial) ?_
  have := countdownCost_le (fun _ => 25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) b
  rw [sum_map_const_range] at this
  exact this

/-! ## Output and cleanup -/

/-- Drop every scratch number together with its floor. -/
def cleanupP : OProg :=
  .seq (dropF (loc .X)) <| .seq (dropF (loc .O)) <| .seq (dropF (loc .D)) <|
  .seq (dropF (loc .KM)) <| .seq (dropF (loc .E2)) <| .seq (dropF (loc .W)) <|
  .seq (popW (loc .Cn)) (dropF (loc .F))

/-- Strip the high zeros, move the output onto the destination, clean up. -/
def postP : OProg := .seq strip (.seq ((moveBits (loc .Out) (loc .Dst)).liftRegs lW) cleanupP)

theorem closed_postP : postP.Closed :=
  ⟨closed_strip, WP.W9comp.closed_liftRegs lW (by
      simp [Prog.Closed, Prog.FreeBelow, moveBits, moveBitsBody, pushR, popR]),
    closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _,
    closed_dropF _, closed_popW _, closed_dropF _⟩

theorem r_postP (S : Stk → List Sym) (neg : Bool) (k1 k2 b par x o : ℕ) :
    RunsIn [] postP (stk S (cAt S neg k1 k2 b par x o b))
      (stk S ((ofS S).set .Dst (natSyms (bitsVal ((List.range b).map
        (outBit neg (sBit k1 k2 b par x o)))) ++ S (loc .Dst)))) (fun _ => True)
      (6 * b + 2 * bitLen (x / 2 ^ b) + 2 * bitLen (o / 2 ^ b) + 2 * bitLen (distR k1 k2 b) +
        2 * bitLen (k1 - 1) + 2 * bitLen (k1 + k1) + 2 * bitLen (b - b + k2) +
        2 * bitLen (neg && seenB (sBit k1 k2 b par x o) b).toNat + 20) := by
  have hlen : ((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse.length = b := by
    simp
  have hes : (((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse.dropWhile
      (fun t => !t)).length ≤ b :=
    (List.length_dropWhile_le _ _).trans hlen.le
  have hnat : (((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse.dropWhile
      (fun t => !t)).reverse.map Sym.bit =
      natSyms (bitsVal ((List.range b).map (outBit neg (sBit k1 k2 b par x o)))) := by
    rw [reverse_dropWhile_eq_encodeNat, List.reverse_reverse] <;> rfl
  have h := RunsIn.seq (r_strip S (cAt S neg k1 k2 b par x o b)
      ((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse (S (loc .Out)) rfl) <|
    RunsIn.seq (r_moveBits S (f := .Out) (g := .Dst) (by decide) _
      (((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse.dropWhile
        (fun t => !t)) (Sym.mark :: S (loc .Out)) (termOK_mark _) (by rfl)) <|
    RunsIn.seq (r_dropF S _ .X (x / 2 ^ b) Sym.mark (S (loc .X)) rfl (by rfl)) <|
    RunsIn.seq (r_dropF S _ .O (o / 2 ^ b) Sym.mark (S (loc .O)) rfl (by rfl)) <|
    RunsIn.seq (r_dropF S _ .D (distR k1 k2 b) Sym.mark (S (loc .D)) rfl (by rfl)) <|
    RunsIn.seq (r_dropF S _ .KM (k1 - 1) Sym.mark (S (loc .KM)) rfl (by rfl)) <|
    RunsIn.seq (r_dropF S _ .E2 (k1 + k1) Sym.mark (S (loc .E2)) rfl (by rfl)) <|
    RunsIn.seq (r_dropF S _ .W (b - b + k2) Sym.mark (S (loc .W)) rfl (by rfl)) <|
    RunsIn.seq (r_popW S _ .Cn)
      (r_dropF S _ .F (neg && seenB (sBit k1 k2 b par x o) b).toNat Sym.mark (S (loc .F)) rfl
        (by rfl))
  refine RunsIn.congr h (congrArg (stk S) (Sc.ext' rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_))
    (by omega)
  show (((List.range b).map (outBit neg (sBit k1 k2 b par x o))).reverse.dropWhile
      (fun t => !t)).reverse.map Sym.bit ++ S (loc .Dst) =
    natSyms (bitsVal ((List.range b).map (outBit neg (sBit k1 k2 b par x o)))) ++ S (loc .Dst)
  rw [hnat]

/-! ## The kernel -/

/-- The kernel for `k1 ≥ 1`; `xs`, `os`: sources of the control and of the tested chunk. -/
def mainPosG (neg : Bool) (par : ℕ) (xs os : Stk) : OProg :=
  .seq (setupG xs os) (.seq (countdown lW (loc .Cn) sT1 (body neg par)) postP)

/-- **The offset kernel** (`neg = decide (ε = -1)`). -/
def offMain (neg xF : Bool) (par : ℕ) : OProg :=
  .seq (peekW nK1) (.ite (fun r => optIsBit r.1)
    (mainPosG neg par (if xF then nC1 else nC2) (if xF then nC2 else nC1)) (.load id))

theorem closed_offMain (neg xF : Bool) (par : ℕ) : (offMain neg xF par).Closed :=
  ⟨closed_peekW _, ⟨closed_setupG _ _, closed_countdown lW _ _ (closed_body neg par),
    closed_postP⟩, trivial⟩

theorem r_mainPosG (S : Stk → List Sym) (neg : Bool) (par : ℕ) (hpar : par ≤ 1) {xs os : Stk}
    (hxN : fldOf xs = none) (hoN : fldOf os = none) (hxT : xs ≠ sT1) (hoT : os ≠ sT1)
    {x o k1 k2 b : ℕ} {rx ro r4 r5 r0 : List Sym} (hrx : TermOK rx) (hro : TermOK ro)
    (h4 : TermOK r4) (h5 : TermOK r5) (h0 : TermOK r0) (hxs : S xs = natSyms x ++ rx)
    (hos : S os = natSyms o ++ ro) (hS4 : S nK1 = natSyms k1 ++ r4)
    (hS5 : S nK2 = natSyms k2 ++ r5) (hS0 : S nB = natSyms b ++ r0) (hk1 : 1 ≤ k1) :
    RunsIn [] (mainPosG neg par xs os) (stk S (ofS S))
      (stk S ((ofS S).set .Dst (natSyms (bitsVal ((List.range b).map
        (outBit neg (sBit k1 k2 b par x o)))) ++ S (loc .Dst)))) (fun _ => True)
      (900 * (b + bitLen x + bitLen o + bitLen k1 + bitLen k2 + 1) ^ 2) := by
  have hs := r_setupG S hxN hoN hxT hoT hrx hro h4 h5 h0 hxs hos hS4 hS5 hS0 hk1
  have hl := r_loop S neg k1 k2 b par x o hpar hk1
  have hp := r_postP S neg k1 k2 b par x o
  have e : (⟨natSyms x ++ Sym.mark :: S (loc .X), natSyms o ++ Sym.mark :: S (loc .O),
      natSyms k2 ++ Sym.mark :: S (loc .D), natSyms (k1 - 1) ++ Sym.mark :: S (loc .KM),
      natSyms (k1 + k1) ++ Sym.mark :: S (loc .E2),
      natSyms (b + k2) ++ Sym.mark :: S (loc .W), natSyms b ++ Sym.mark :: S (loc .Cn),
      Sym.mark :: S (loc .Out), Sym.mark :: S (loc .F), S (loc .Dst)⟩ : Sc) =
      (cAt S neg k1 k2 b par x o 0).set .Cn (natSyms b ++ Sym.mark :: S (loc .Cn)) := by
    refine Sc.ext' ?_ ?_ rfl rfl rfl ?_ rfl rfl ?_ rfl
    · show natSyms x ++ Sym.mark :: S (loc .X) = natSyms (x / 2 ^ 0) ++ Sym.mark :: S (loc .X)
      rw [pow_zero, Nat.div_one]
    · show natSyms o ++ Sym.mark :: S (loc .O) = natSyms (o / 2 ^ 0) ++ Sym.mark :: S (loc .O)
      rw [pow_zero, Nat.div_one]
    · show natSyms (b + k2) ++ Sym.mark :: S (loc .W) =
        natSyms (b - 0 + k2) ++ Sym.mark :: S (loc .W)
      rw [Nat.sub_zero]
    · show Sym.mark :: S (loc .F) =
        natSyms (neg && seenB (sBit k1 k2 b par x o) 0).toNat ++ Sym.mark :: S (loc .F)
      have h0' : seenB (sBit k1 k2 b par x o) 0 = false := rfl
      rw [h0', Bool.and_false, Bool.toNat_false, natSyms_zero, List.nil_append]
  have h := RunsIn.seq (RunsIn.congr hs (congrArg (stk S) e) le_rfl) (RunsIn.seq hl hp)
  refine RunsIn.mono h (fun _ h => h) ?_
  obtain ⟨V, hV⟩ : ∃ V, V = b + bitLen x + bitLen o + bitLen k1 + bitLen k2 + 1 := ⟨_, rfl⟩
  rw [← hV, sq]
  have f1 : bitLen (x / 2 ^ b) ≤ bitLen x := bitLen_mono'' (Nat.div_le_self _ _)
  have f2 : bitLen (o / 2 ^ b) ≤ bitLen o := bitLen_mono'' (Nat.div_le_self _ _)
  have f3 : bitLen (distR k1 k2 b) ≤ bitLen k1 + bitLen k2 + 1 :=
    (bitLen_mono'' (distR_le hk1 k2 _)).trans (bitLen_add_le k1 k2)
  have f4 : bitLen (k1 - 1) ≤ bitLen k1 := bitLen_mono'' (Nat.sub_le k1 1)
  have f5 := bitLen_add_self_le k1
  have f6 : bitLen (b - b + k2) ≤ bitLen k2 := bitLen_mono'' (by omega)
  have f7 : bitLen (neg && seenB (sBit k1 k2 b par x o) b).toNat ≤ 1 := by
    generalize (neg && seenB (sBit k1 k2 b par x o) b) = t
    exact (bitLen_le_self _).trans (by cases t <;> decide)
  have f8 := bitLen_le_self b
  have hK : 25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81 ≤ 124 * V := by omega
  have hbV : b ≤ V := by omega
  have hprod : b * (25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) ≤ 124 * (V * V) :=
    calc b * (25 * bitLen k1 + 12 * bitLen k2 + 6 * bitLen b + 81) ≤ V * (124 * V) :=
          Nat.mul_le_mul hbV hK
      _ = 124 * (V * V) := by ring
  have hVV : V ≤ V * V := Nat.le_mul_self V
  omega

theorem r_offMain (S : Stk → List Sym) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {par : ℕ}
    (hpar : par ≤ 1) (xF : Bool) (k1 k2 b c1 c2 : ℕ) (r0 r1 r2 r4 r5 : List Sym)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h4 : TermOK r4) (h5 : TermOK r5)
    (hS0 : S (.inl 0) = natSyms b ++ r0) (hS1 : S (.inl 1) = natSyms c1 ++ r1)
    (hS2 : S (.inl 2) = natSyms c2 ++ r2) (hS4 : S (.inl 4) = natSyms k1 ++ r4)
    (hS5 : S (.inl 5) = natSyms k2 ++ r5) :
    Runs (offMain (decide (ε = -1)) xF par) S
      (Function.update S (.inl 3) (natSyms (lineOff ε par xF k1 k2 b c1 c2) ++ S (.inl 3)))
      (fun _ => True) (1000 * (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ 2) := by
  have hpos : 0 < (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ 2 :=
    pow_pos (by omega) 2
  have key : RunsIn [] (offMain (decide (ε = -1)) xF par) (stk S (ofS S))
      (stk S ((ofS S).set .Dst (natSyms (lineOff ε par xF k1 k2 b c1 c2) ++ S (loc .Dst))))
      (fun _ => True)
      (900 * (b + bitLen c1 + bitLen c2 + bitLen k1 + bitLen k2 + 1) ^ 2 + 2) := by
    have hhead : optIsBit (stk S (ofS S) nK1).head? = decide (k1 ≠ 0) := by
      rw [stk_none S _ (rfl : fldOf nK1 = none), hS4, optIsBit_head_natSyms _ _ h4]
    refine r_ite_peek S optIsBit (fun h => ?_) (fun h => ?_)
    · have hk1 : 1 ≤ k1 := by
        rw [hhead] at h
        have : k1 ≠ 0 := by simpa using h
        omega
      rw [← bitsVal_outs hk1 hε par xF k2 b c1 c2]
      cases xF
      · have hm := r_mainPosG S (decide (ε = -1)) par hpar (xs := nC2) (os := nC1) rfl rfl
          (by decide) (by decide) h2 h1 h4 h5 h0 hS2 hS1 hS4 hS5 hS0 hk1
        refine RunsIn.mono hm (fun _ h => h) (le_of_eq ?_)
        rw [show b + bitLen c2 + bitLen c1 = b + bitLen c1 + bitLen c2 by omega]
      · exact r_mainPosG S (decide (ε = -1)) par hpar (xs := nC1) (os := nC2) rfl rfl
          (by decide) (by decide) h1 h2 h4 h5 h0 hS1 hS2 hS4 hS5 hS0 hk1
    · have hk0 : k1 = 0 := by
        rw [hhead] at h
        simpa using h
      subst hk0
      rw [lineOff_k1_zero, natSyms_zero, List.nil_append]
      have e : (ofS S).set .Dst (S (loc .Dst)) = ofS S := Sc.set_get _ .Dst
      rw [e]
      refine RunsIn.mono (r_load S (ofS S)) (fun _ h => h) ?_
      omega
  rw [stk_ofS, stk_ofS_dst] at key
  exact RunsIn.iff_runs.mp (RunsIn.mono key (fun _ h => h) (by omega))

end SubNLogN.Machine.AppC.C7LinesOffAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-- **Lemma A.9 offset leaf** (`AppC/C7LinesAddr.lean`, `lineOff`): for `ε = ±1` and `par ≤ 1` the
push offset `lineOff ε par xF` of a packed line has an offset routine in the sense of
`K4OffsetCtlParStmt` (named stacks `b, c1, c2, dst, k1, k2`; restored scratch), with
`J = 2` and cost constant `1000`. Kernel: `AppC.C7LinesOffAux.offMain`. -/
theorem c7LinesOff_holds : ∃ J, ∀ (ε : ℤ) (par : ℕ) (xF : Bool), (ε = 1 ∨ ε = -1) →
    par ≤ 1 → K4OffsetCtlParStmt (AppC.C7LinesAux.lineOff ε par xF) J := by
  refine ⟨2, fun ε par xF hε hpar => ?_⟩
  refine ⟨1000, fun _ => ⟨Fin 12, inferInstance, inferInstance, NatArith.Reg,
    AppC.C7LinesOffAux.offMain (decide (ε = -1)) xF par, inferInstance, inferInstance,
    AppC.C7LinesOffAux.closed_offMain _ _ _, ?_⟩⟩
  intro k1 k2 b c1 c2 r0 r1 r2 r4 r5 S h0 h1 h2 h4 h5 hS0 hS1 hS2 hS4 hS5
  exact AppC.C7LinesOffAux.r_offMain S hε hpar xF k1 k2 b c1 c2 r0 r1 r2 r4 r5 h0 h1 h2 h4 h5
    hS0 hS1 hS2 hS4 hS5

end SubNLogN.Machine
