import SubNLogN.Machine.Pipe.ReadParamsPhases

/-!
# Read-parameters kernel, part 4: the program and `readParams_holds_of`

* `par_syms`, `mpar_syms`: the bridge header `hdrSyms (fnewPar fnewSched p0 K0 p_in).hdr` and
  the middle header `hdrSyms (midList p0 K0)` as the concatenations the output phases push;
* cost bounds `mkDk_cost_le`, `mkLM_cost_le`, `sqB_le`;
* the program `rpProg` (closed: `closed_rpProg`) and its run `rp_main`
  (exact final state `rpFinal`, cost `≤ 2^30 · (b + K0 + p_in + 16)^6`);
* **`SubNLogN.Machine.Pipe.readParams_holds_of`**: `ReadParamsStmt fnewSched md readParamsCost`
  for every `md` with `md.mhdr p0 K0 p_in = midList p0 K0` (constant `C = 2^30`).
-/

namespace SubNLogN.Machine.Pipe.ReadParamsAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Machine.Pipe.GuardAux

/-! ## Header identities -/

section HdrIds

open SubNLogN.Math.Cost SubNLogN.Math.Bridge

theorem hdrSyms_cons2 (x y : ℕ) (l : List ℕ) :
    hdrSyms (x :: y :: l) = hdrSyms [x] ++ hdrSyms (y :: l) := by
  simp [hdrSyms]

theorem schedP_eq (p0 K0 : ℕ) :
    schedP p0 K0 = 2 * p0 + 12 * K0 + 32 * bitLen (p0 + K0 + 1) + 256 := by
  unfold schedP
  rw [clog_eq_bitLen _ (by omega), show p0 + K0 + 2 - 1 = p0 + K0 + 1 by omega]

theorem schedOmega_eq (p0 K0 : ℕ) :
    schedOmega p0 K0 (fnewD row46 K0 + 1) =
      max (bitLen (dK row46 K0 - 1)) 1 + (p0 + K0 + 20) := by
  unfold schedOmega SubNLogN.Math.Common.lg
  rw [clog_eq_bitLen _ (by omega), show fnewD row46 K0 + 1 - 1 = dK row46 K0 - 1 from rfl]
  omega

theorem par_syms (b K0 pin p0 pp dk l m : ℕ) (hp0 : p0 = 2 * b + 2 * K0 + 6)
    (hpp : pp = 2 * p0 + 12 * K0 + 32 * bitLen (p0 + K0 + 1) + 256)
    (hdk : dk = dK row46 K0) (hl : l = lK row46 K0) (hm : m = dk * l - K0) (T : List Sym) :
    hdrSyms (fnewPar fnewSched (IntMul.rootPrecision b K0) K0 pin).hdr ++ T =
      hdrSyms [p0] ++ (hdrSyms [pp] ++ (hdrSyms [max (bitLen (dk - 1)) 1 + (p0 + K0 + 20)] ++
        (hdrSyms [pp + 2 * K0 + 16] ++ (hdrSyms [pp + 2 * K0 + 16] ++
          (hdrSyms [2 * p0 + K0 + 8] ++ (hdrSyms [pin + 2] ++ (hdrSyms [p0 + pin + 2] ++
            (hdrSyms [dk - 1 + 1] ++ (hdrSyms (List.replicate m (2 ^ (l - 1))) ++
              (hdrSyms (List.replicate (dk - 1 - m) (2 ^ l)) ++
                (hdrSyms [2 ^ l] ++ T))))))))))) := by
  subst hp0 hpp hdk hl hm
  show hdrSyms ([2 * b + 2 * K0 + 6, schedP (2 * b + 2 * K0 + 6) K0,
      schedOmega (2 * b + 2 * K0 + 6) K0 (fnewD row46 K0 + 1),
      schedP (2 * b + 2 * K0 + 6) K0 + 2 * K0 + 16, schedP (2 * b + 2 * K0 + 6) K0 + 2 * K0 + 16,
      2 * (2 * b + 2 * K0 + 6) + K0 + 8, pin + 2, 2 * b + 2 * K0 + 6 + pin + 2,
      fnewD row46 K0 + 1] ++ List.ofFn (fnewShape row46 K0)) ++ T = _
  rw [schedP_eq, schedOmega_eq, ofFn_fnewShape, ofFn_fnewA]
  simp only [List.map_append, List.map_replicate, hdrSyms_append, hdrSyms_cons2,
    List.append_assoc, fnewD, fnewL]

theorem mpar_syms (K0 p0 pp dk l m : ℕ)
    (hpp : pp = 2 * p0 + 12 * K0 + 32 * bitLen (p0 + K0 + 1) + 256)
    (hdk : dk = dK row46 K0) (hl : l = lK row46 K0) (hm : m = dk * l - K0) (T : List Sym) :
    hdrSyms ([schedP p0 K0 + 2, fnewD row46 K0, fnewL row46 K0, KK row46 K0,
      schedP p0 K0 + 2 * K0 + 16] ++ List.ofFn (fnewA row46 K0)) ++ T =
      hdrSyms [pp + 2] ++ (hdrSyms [dk - 1] ++ (hdrSyms [l] ++
        (hdrSyms [floorRatPow dk 1 (2 ^ 50)] ++ (hdrSyms [pp + 2 * K0 + 16] ++
          (hdrSyms (List.replicate m (l - 1)) ++ (hdrSyms (List.replicate (dk - 1 - m) l) ++
            T)))))) := by
  subst hpp hdk hl hm
  rw [schedP_eq, ofFn_fnewA]
  simp only [hdrSyms_append, hdrSyms_cons2, List.append_assoc, fnewD, fnewL, KK46]

end HdrIds

/-! ## Cost bounds -/

theorem mkDk_cost_le (K0 X : ℕ) (hK : K0 ≤ X) (h16 : 16 ≤ X) :
    (SubNLogN.Math.Cost.floorRatPow K0 1 15 + 1) *
      (rootB 15 (SubNLogN.Math.Cost.floorRatPow K0 1 15) K0 + 2) ≤ 2 ^ 27 * X ^ 3 := by
  have hd : SubNLogN.Math.Cost.floorRatPow K0 1 15 ≤ X := le_trans (frp_le K0 15 (by norm_num)) hK
  have hP : (SubNLogN.Math.Cost.floorRatPow K0 1 15 + 1) ^ 15 ≤ 2 ^ 15 * X + 1 :=
    le_trans (dK46_pow K0) (Nat.add_le_add_right (Nat.mul_le_mul_left _ hK) 1)
  unfold rootB
  calc (SubNLogN.Math.Cost.floorRatPow K0 1 15 + 1) * ((24 * 15 + 30) *
        ((SubNLogN.Math.Cost.floorRatPow K0 1 15 + 1) ^ 15 + 1) *
        (SubNLogN.Math.Cost.floorRatPow K0 1 15 + 2) + 15 * K0 +
        6 * (SubNLogN.Math.Cost.floorRatPow K0 1 15 + 1) ^ 15 + 12 + 2)
      ≤ (X + 1) * ((24 * 15 + 30) * ((2 ^ 15 * X + 1) + 1) * (X + 2) + 15 * X +
        6 * (2 ^ 15 * X + 1) + 12 + 2) := by gcongr
    _ ≤ 2 ^ 27 * X ^ 3 := by
      have h1 := Nat.mul_le_mul_left X h16
      have h2 := Nat.mul_le_mul_left (X * X) h16
      nlinarith

theorem mkLM_cost_le (K0 dk l X : ℕ) (hK : K0 ≤ X) (hdk : dk ≤ X) (hl : l ≤ X) (h16 : 16 ≤ X) :
    (l + 1) * (divB l dk K0 + 2) + 30 * (l + 1) * (dk + 1) + 20 * K0 + 40 ≤ 1000 * X ^ 3 := by
  unfold divB
  calc (l + 1) * (25 * (l + 1) * (dk + 1) + 15 * K0 + 6 * (dk * l) + 48 + 2) +
        30 * (l + 1) * (dk + 1) + 20 * K0 + 40
      ≤ (X + 1) * (25 * (X + 1) * (X + 1) + 15 * X + 6 * (X * X) + 48 + 2) +
        30 * (X + 1) * (X + 1) + 20 * X + 40 := by gcongr
    _ ≤ 1000 * X ^ 3 := by
      have h1 := Nat.mul_le_mul_left X h16
      have h2 := Nat.mul_le_mul_left (X * X) h16
      nlinarith

theorem sqB_le (X : ℕ) (h16 : 16 ≤ X) : sqB X ≤ 1000 * X ^ 4 := by
  unfold sqB rootB
  have h1 := Nat.mul_le_mul_left X h16
  have h2 := Nat.mul_le_mul_left (X * X) h16
  have h3 := Nat.mul_le_mul_left (X * X * X) h16
  nlinarith

/-! ## The program -/

/-- **The read-parameters program**: read `b`, `K0`, `p_in`; compute `p0`, `P`, `dK`, `ℓ`,
`m = dK·ℓ - K0` in unary; push the width fields on `win`, `wout`, the middle header on `mpar`,
the bridge header on `par` (each list pushed last field first); clear the registers. -/
def rpProg : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq readProg mkP0) mkPP) mkDk)
    mkLM) outWW) outMparA) outMparB) outParA) outParB) outParC) cleanProg

theorem fb_pushMs (a : RE) (d : ℕ) : ∀ n, (pushMs a n).FreeBelow d
  | 0 => by simp [pushMs, skip, Prog.FreeBelow]
  | n + 1 => by simp [pushMs, pushC, Prog.FreeBelow, fb_pushMs a d n]

theorem fb_cpN (a b t : RE) (d : ℕ) : ∀ n, (cpN a b t n).FreeBelow d
  | 0 => by simp [cpN, skip, Prog.FreeBelow]
  | n + 1 => by
    simp [cpN, copyAll, moveDup, moveDupBody, moveAll, moveAllBody, peekR, popR, pushR,
      Prog.FreeBelow, fb_cpN a b t d n]

theorem fb_mulU (d : ℕ) : mulU.FreeBelow d := by
  simp [mulU, mulBody, copyAll, moveDup, moveDupBody, moveAll, moveAllBody, peekR, popR, pushR,
    pushC, Prog.FreeBelow]

theorem fb_powU (d : ℕ) : ∀ e, (powU e).FreeBelow d
  | 0 => by simp [powU, pushC, Prog.FreeBelow]
  | e + 1 => by
    simp [powU, powStep, clearM, clearBody, moveAll, moveAllBody, copyAll, moveDup, moveDupBody,
      peekR, popR, pushR, Prog.FreeBelow, fb_powU d e, fb_mulU d]

theorem fb_leTest (d : ℕ) : leTest.FreeBelow d := by
  simp [leTest, condAB, lockBody, clearM, clearBody, peekR, popR, skip, Prog.FreeBelow]

theorem fb_testRoot (e d : ℕ) : (testRoot e).FreeBelow d := by
  simp [testRoot, rootPre, copyAll, moveDup, moveDupBody, moveAll, moveAllBody, clearM, clearBody,
    peekR, popR, pushR, pushC, Prog.FreeBelow, fb_powU, fb_leTest]

theorem fb_iterSqrt (d : ℕ) : ∀ n, (iterSqrt n).FreeBelow d
  | 0 => by simp [iterSqrt, skip, Prog.FreeBelow]
  | n + 1 => by
    simp [iterSqrt, search, clearM, clearBody, moveAll, moveAllBody, peekR, popR, pushR, pushC,
      Prog.FreeBelow, fb_iterSqrt d n, fb_testRoot 2 d]

theorem closed_rpProg : rpProg.Closed := by
  simp [Prog.Closed, rpProg, readProg, fieldTo, movTop, horner, hornerBody, moveDbl, moveDblBody,
    moveBlock, moveBits, moveBitsBody, restoreR, mkP0, linPrep, mkPP, bitLenU, toBin, binBody,
    halve, halveBody, emitBit, countO, countBody, mkDk, mkLM, search, testDiv, divPre, subU,
    subBody, outWW, outLin, pushNat, outMparA, repA, repB, rep, repBody, outMparB, prepKK, prepD,
    outParA, pushPow2, p2Body, outParB, prepd, outParC, prepW, maxOne, cleanProg, copyAll,
    moveDup, moveDupBody, moveAll, moveAllBody, clearM, clearBody, peekR, popR, pushR, pushC,
    skip, Prog.FreeBelow, fb_pushMs, fb_cpN, fb_mulU, fb_testRoot, fb_iterSqrt, fb_leTest]

theorem regs_zero : regs 0 0 0 0 0 0 0 0 = fun _ => 0 := by
  funext x
  cases x <;> rfl

/-- The final named-stack contents (the post-state of `ReadParamsStmt` for middle header `mh`). -/
def rpFinal (S : RK → List Sym) (b K0 pin : ℕ) (mh : List ℕ) : RK → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (.inl .par)
    (hdrSyms (fnewPar fnewSched (IntMul.rootPrecision b K0) K0 pin).hdr ++ S (.inl .par)))
    (.inl .mpar) (hdrSyms mh ++ S (.inl .mpar)))
    (.inl .win) (hdrSyms [fnewSched.wIn (IntMul.rootPrecision b K0) K0 pin] ++ S (.inl .win)))
    (.inl .wout) (hdrSyms [fnewSched.wOut (IntMul.rootPrecision b K0) K0 pin] ++ S (.inl .wout))

open SubNLogN.Math.Bridge in
/-- The Walsh middle's header at `(p0, K0)` (`walshMidData … .mhdr p0 K0 p_in`). -/
def midList (p0 K0 : ℕ) : List ℕ :=
  [schedP p0 K0 + 2, fnewD Math.Cost.row46 K0, fnewL Math.Cost.row46 K0,
    Math.Cost.KK Math.Cost.row46 K0, schedP p0 K0 + 2 * K0 + 16] ++
    List.ofFn (fnewA Math.Cost.row46 K0)

/-! ## Main evaluation -/

section Main

open SubNLogN.Math.Bridge SubNLogN.Math.Cost

theorem rp_main (b K0 pin : ℕ) (R0 R1 : List Sym) (S : RK → List Sym) (hcl : KClean S)
    (hC0 : S (.inl .C0) = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: R0))
    (hC1 : S (.inl .C1) = natSyms pin ++ Sym.mark :: R1) :
    MS rpProg S (regs 0 0 0 0 0 0 0 0)
      (rpFinal S b K0 pin (midList (IntMul.rootPrecision b K0) K0)) (regs 0 0 0 0 0 0 0 0)
      (2 ^ 30 * (b + K0 + pin + 16) ^ 6) := by
  obtain ⟨X, hX⟩ : ∃ X, X = b + K0 + pin + 16 := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p0, p0 = 2 * b + 2 * K0 + 6 := ⟨_, rfl⟩
  obtain ⟨pp, hpp⟩ : ∃ pp, pp = 2 * p0 + 12 * K0 + 32 * bitLen (p0 + K0 + 1) + 256 :=
    ⟨_, rfl⟩
  obtain ⟨dk, hdk⟩ : ∃ dk, dk = floorRatPow K0 1 15 := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = (K0 + dk - 1) / dk := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = dk * l - K0 := ⟨_, rfl⟩
  have hdk' : dk = dK row46 K0 := hdk
  have hl' : l = lK row46 K0 := by rw [hl, hdk']; rfl
  have h16 : 16 ≤ X := by omega
  have hK : K0 ≤ X := by omega
  have hi : pin ≤ X := by omega
  have hp0X : p0 ≤ 2 * X := by omega
  have hbl := bitLen_le (p0 + K0 + 1)
  have hppX : pp ≤ 128 * X := by omega
  have hdkK : dk ≤ K0 := by rw [hdk']; exact dK46_le K0
  have hdkX : dk ≤ X := by omega
  have hlK : l ≤ K0 := by rw [hl']; exact lK46_le K0
  have hlX : l ≤ X := by omega
  have hmD : m ≤ dk - 1 := by rw [hm, hl', hdk']; exact fnewM_le K0
  have hmX : m ≤ X := by omega
  have hd0 : dk = 0 → K0 = 0 := by rw [hdk']; exact dK46_zero
  have hO : S (.inr .O) = [] := hcl _
  have h1 := (read_ms b K0 pin R0 R1 S (regs 0 0 0 0 0 0 0 0) hC0 hC1 (hcl _) (hcl _) rfl rfl rfl
    rfl).of_eq rfl (show _ = regs b K0 pin 0 0 0 0 0 by funext x; cases x <;> simp [regs])
  have h2 := (mkP0_ms S b K0 pin).of_eq rfl (show _ = regs 0 K0 pin p0 0 0 0 0 by rw [hp0])
  have h3 := (mkPP_ms S hO K0 pin p0).of_eq rfl (show _ = regs 0 K0 pin p0 pp 0 0 0 by rw [hpp])
  have h4 := (mkDk_ms S K0 pin p0 pp).of_eq rfl
    (show _ = regs 0 K0 pin p0 pp dk 0 0 by rw [hdk])
  have h5 := (mkLM_ms S K0 pin p0 pp dk hd0).of_eq rfl
    (show _ = regs 0 K0 pin p0 pp dk l m by rw [hm, hl])
  have h6 := outWW_ms S hO K0 pin p0 pp dk l m X hK hi hp0X h16
  have h := ((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq
    (outMparA_ms _ (by simp [hO]) K0 pin p0 pp dk l m X hdkX hlX hmX h16)).seq
    (outMparB_ms _ (by simp [hO]) K0 pin p0 pp dk l m X hK hppX hdkX hlX h16)).seq
    (outParA_ms _ (by simp [hO]) K0 pin p0 pp dk l m X hdkX hlX hmX h16)).seq
    (outParB_ms _ (by simp [hO]) K0 pin p0 pp dk l m X hK hi hp0X hdkX h16)).seq
    (outParC_ms _ (by simp [hO]) K0 pin p0 pp dk l m X hK hp0X hppX hdkX h16)).seq
    (clean_ms _ K0 pin p0 pp dk l m)
  refine (h.mono ?_).of_eq ?_ rfl
  · -- the cost
    have hDk := mkDk_cost_le K0 X hK h16
    rw [← hdk] at hDk
    have hLM := mkLM_cost_le K0 dk l X hK hdkX hlX h16
    have hsq := sqB_le X h16
    have hfb := fcost_le b
    have hfK := fcost_le K0
    have hfi := fcost_le pin
    have hb1 := bitLen_le b
    have hb2 := bitLen_le K0
    have hb3 := bitLen_le pin
    have hX1 : 1 ≤ X := by omega
    have e2 : X ^ 2 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    have e3 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    have e4 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    have e1 : X ≤ X ^ 6 := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
    rw [← hdk, ← hl, ← hX]
    linarith
  · -- the final stacks
    have hpar := par_syms b K0 pin p0 pp dk l m hp0 hpp hdk' hl' hm (S (.inl .par))
    have hmpar := mpar_syms K0 p0 pp dk l m hpp hdk' hl' hm (S (.inl .mpar))
    have hwin : fnewSched.wIn (IntMul.rootPrecision b K0) K0 pin = p0 + pin + 2 := by
      rw [hp0]; rfl
    have hwout : fnewSched.wOut (IntMul.rootPrecision b K0) K0 pin = 2 * p0 + K0 + 8 := by
      rw [hp0]; rfl
    have hmid : midList (IntMul.rootPrecision b K0) K0 = midList p0 K0 := by rw [hp0]; rfl
    unfold rpFinal
    rw [hpar, hmid]
    unfold midList
    rw [hmpar, hwin, hwout]
    funext x
    rcases x with a | e
    · cases a <;> simp
    · simp

end Main

end SubNLogN.Machine.Pipe.ReadParamsAux

namespace SubNLogN.Machine.Pipe

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine ReadParamsAux

/-- **The read-parameters kernel (`readParams_holds_of`).** For every middle data `md` whose
header is the Walsh middle's header `midList p0 K0`, `ReadParamsStmt fnewSched md readParamsCost`
holds with cost constant `C = 2^30`, scratch `RE`, register `Option Sym`, program `rpProg`. -/
theorem readParams_holds_of (md : MidData) (hmd : ∀ p0 K0 pin, md.mhdr p0 K0 pin = midList p0 K0) :
    ReadParamsStmt fnewSched md readParamsCost := by
  refine ⟨2 ^ 30, fun _ => ⟨RE, inferInstance, inferInstance, Option Sym, rpProg, inferInstance,
    ⟨none⟩, closed_rpProg, ?_⟩⟩
  intro b K0 k1 k2 pin r0 r1 S hcl hC0 hC1
  have hC0' : S (.inl .C0) = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark ::
      (hdrSyms [k1, k2] ++ r0)) := by
    rw [hC0]; simp [hdrSyms]
  have hC1' : S (.inl .C1) = natSyms pin ++ Sym.mark :: r1 := by
    rw [hC1]; simp [hdrSyms]
  have h := rp_main b K0 pin _ r1 S hcl hC0' hC1'
  have hfin : KClean (rpFinal S b K0 pin (midList (IntMul.rootPrecision b K0) K0)) := by
    intro e
    simp [rpFinal]
    exact hcl e
  refine Runs.of_eval fun v => ?_
  obtain ⟨r, t, ht, e⟩ := h v
  rw [regs_zero, mkS_clean S hcl, mkS_clean _ hfin, ← hmd (IntMul.rootPrecision b K0) K0 pin] at e
  exact ⟨r, t, e, trivial, ht⟩

end SubNLogN.Machine.Pipe
