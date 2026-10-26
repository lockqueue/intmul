/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseEntry

/-!
# K4-TW (`Machine/FFT/PhaseTable.lean`): the phase-table builder (Lemma 6.1 on the machine)

**Scope (honest summary).** The builder program `ptProg I` and its host rule `HT.ptProg`, all
proved (no `sorry`), given an instance bundle `I : PI` with `I.Spec C` (`PhaseProg.lean`).
The contract statement `PhaseTableMachineStmt` is concluded in `Machine/FFT/PhaseHolds.lean`.

## Design (Lemma 6.1, `lem:phase-table`, Section 6.1,
`sec:direct-fft-phases`)
* Stacks (`PL = Loc 3 32`): `sH` the header `midHdr q ℓ K w a` (restored), `sT` the table stack;
  scratch: constants `vq, vl, vw` (header fields), `vq6 = q+6`, `vq3 = q+3`, `vq11 = q+11`,
  `vP = 2^q`, `vPw = 2^w`, `vden = 2·2^ℓ`; the loop counter `ctr`; the header park `pk`;
  temporaries `tA, tB, tC, tR, tU, x1, x2, fF, uU, wc`. Every scratch stack starts and ends empty.
* `hdrRead`: copy `q`, `ℓ`, `w` out of the header; the fields `q, D, ℓ, K` are parked on `pk` and
  put back, so the cost is `O(|midHdr|)` (the fields `D`, `K` are skipped, never interpreted).
* `setup`: the constants. `pcd ctr body`: count down `j = 2r-1, …, 0` (`r = 2^ℓ`); `body` pushes
  entry `j` on `sT`, so `sT` receives `entry 0 ++ … ++ entry (2r-1)` (`sfx`), i.e. exactly
  `tabSyms w q ℓ (phaseTable q ℓ)` (`tabSyms_phaseTable`).
* Entry `j` (`valProg`, `emitEntry`, `PhaseEntry.lean`): the exact numerators
  `phaseTableNum q ℓ j` (root test `j·2 = ⌊j·2/2^ℓ⌋·2^ℓ`; roots `±2^q`, `±i·2^q`; otherwise W7's
  `stdChar (q+6) j (2·2^ℓ)` then `tdiv (a·(2^{q+3}-1)) 2^{q+11}` per coordinate), then the two
  `w`-bit two's-complement fields and `sep`.
* Cost: `O(|midHdr| + w)` outside the loop; per entry `O((w+1)^4)` (`stdChar` is quartic,
  `C(q + ℓ + 9)^4`); `2r` entries.
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh

section Programs

variable (I : PI)

/-- Move a header field (`natSyms f ++ mark`) from `sH` to the park `pk` (`mark` on top). -/
def mvField : PP I :=
  (pcp I sH pk).seq ((pdr I sH).seq ((WP.W7k2.popS sH).seq (WP.W7k2.pushS pk Sym.mark)))

/-- Move a parked field back from `pk` to `sH`. -/
def rsField : PP I :=
  (WP.W7k2.popS pk).seq ((WP.W7k2.pushS sH Sym.mark).seq ((pcp I pk sH).seq (pdr I pk)))

/-- Copy `q`, `ℓ`, `w` out of the header, parking the fields `q, D, ℓ, K` on `pk`. -/
def hdrIn : PP I :=
  (pcp I sH vq).seq ((mvField I).seq ((mvField I).seq ((pcp I sH vl).seq ((mvField I).seq
    ((mvField I).seq (pcp I sH vw))))))

/-- Put the parked fields back. -/
def hdrOut : PP I := (rsField I).seq ((rsField I).seq ((rsField I).seq (rsField I)))

/-- Copy `q`, `ℓ`, `w` out of the header (fields `q, D, ℓ, K` parked and put back). -/
def hdrRead : PP I := (hdrIn I).seq (hdrOut I)

/-- The constants `q+6, q+3, q+11, 2^q, 2^w, 2·2^ℓ`, and the counter `2·2^ℓ`. -/
def setup : PP I :=
  (paddC I vq 6 tA vq6).seq ((paddC I vq 3 tA vq3).seq ((paddC I vq 11 tA vq11).seq
    ((ppow2 I vq vP).seq ((ppow2 I vw vPw).seq ((ppow2 I vl vden).seq ((ps1 I vden).seq
      (pcp I vden ctr)))))))

/-- Drop the counter (now `0`) and the constants. -/
def cleanup : PP I :=
  (pdr I ctr).seq ((pdr I vden).seq ((pdr I vPw).seq ((pdr I vP).seq ((pdr I vq11).seq
    ((pdr I vq3).seq ((pdr I vq6).seq ((pdr I vw).seq ((pdr I vl).seq (pdr I vq)))))))))

/-- **The phase-table builder.** -/
def ptProg : PP I := (hdrRead I).seq ((setup I).seq ((pcd I ctr (body I)).seq (cleanup I)))

theorem hdrRead_closed : (hdrRead I).Closed := by
  unfold hdrRead hdrIn hdrOut mvField rsField pcp pdr
  repeat (first | exact callI_closed _ _ _ _ | exact trivial | refine ⟨?_, ?_⟩)

theorem setup_closed : (setup I).Closed := by
  unfold setup paddC ppow2 pcp pad pdr psv ps1 pushNat
  repeat (first | exact callI_closed _ _ _ _ | exact pushBits_closed _ _ | exact trivial |
    refine ⟨?_, ?_⟩)

theorem cleanup_closed : (cleanup I).Closed := by
  unfold cleanup pdr
  repeat (first | exact callI_closed _ _ _ _ | exact trivial | refine ⟨?_, ?_⟩)

theorem ptProg_closed : (ptProg I).Closed :=
  ⟨hdrRead_closed I, ⟨setup_closed I, ⟨cdLoop_closed _ _ _ _ _ _ _ (body_closed I),
    cleanup_closed I⟩⟩⟩

end Programs


/-! ## Host rules -/

section Rules

variable {I : PI} {C : ℕ}

theorem HT.mvField (hI : I.Spec C) (B : PL → List Sym) (f : ℕ) (tl : List Sym)
    (hB : B sH = natSyms f ++ Sym.mark :: tl) :
    HT [] B (mvField I)
      (Function.update (Function.update B sH tl) pk (Sym.mark :: (natSyms f ++ B pk)))
      (2 * (C * (bitLen f + 1)) + 2) := by
  refine (HT.seq (HT.pcp hI sH pk (by decide) B f (Sym.mark :: tl) (termOK_mark _) hB) <|
    HT.seq (HT.pdr hI sH _ f (Sym.mark :: tl) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hB])) <|
    HT.seq (HT.popS sH _ Sym.mark tl (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) []) <|
    HT.pushS pk Sym.mark _ []).of_eq ?_ (le_of_eq (by ring))
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.rsField (hI : I.Spec C) (B : PL → List Sym) (f : ℕ) (r : List Sym) (hr : TermOK r)
    (hB : B pk = Sym.mark :: (natSyms f ++ r)) :
    HT [] B (rsField I)
      (Function.update (Function.update B pk r) sH (natSyms f ++ Sym.mark :: B sH))
      (2 * (C * (bitLen f + 1)) + 2) := by
  refine (HT.seq (HT.popS pk B Sym.mark _ hB []) <|
    HT.seq (HT.pushS sH Sym.mark _ []) <|
    HT.seq (HT.pcp hI pk sH (by decide) _ f r hr (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.pdr hI pk _ f r hr (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).of_eq ?_ (le_of_eq (by ring))
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

/-- Cost bound of `hdrRead`. -/
def costHR (C q D ℓ K w : ℕ) : ℕ :=
  5 * (C * (bitLen q + bitLen D + bitLen ℓ + bitLen K + bitLen w + 5)) + 16

theorem HT.hdrIn (hI : I.Spec C) (B : PL → List Sym) (q D ℓ K w : ℕ) (tl : List Sym)
    (hB : B sH = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl))))) :
    HT [] B (hdrIn I)
      (Function.update (Function.update (Function.update (Function.update (Function.update B sH
        (natSyms w ++ Sym.mark :: tl)) vq (natSyms q ++ B vq)) vl (natSyms ℓ ++ B vl)) vw
        (natSyms w ++ B vw)) pk (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms D ++ Sym.mark :: (natSyms q ++ B pk))))))
      (C * (bitLen q + 1) + (2 * (C * (bitLen q + 1)) + 2 + (2 * (C * (bitLen D + 1)) + 2 +
        (C * (bitLen ℓ + 1) + (2 * (C * (bitLen ℓ + 1)) + 2 + (2 * (C * (bitLen K + 1)) + 2 +
        C * (bitLen w + 1))))))) := by
  refine (HT.seq (HT.pcp hI sH vq (by decide) B q _ (termOK_mark _) hB) <|
    HT.seq (HT.mvField hI _ q (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl)))) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hB])) <|
    HT.seq (HT.mvField hI _ D (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl))) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.pcp hI sH vl (by decide) _ ℓ
      (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl))) (termOK_mark _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.mvField hI _ ℓ (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl)) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.mvField hI _ K (natSyms w ++ Sym.mark :: tl) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.pcp hI sH vw (by decide) _ w (Sym.mark :: tl) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).of_eq ?_ le_rfl
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.hdrOut (hI : I.Spec C) (B : PL → List Sym) (q D ℓ K : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B pk = Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms D ++ Sym.mark :: (natSyms q ++ r))))) :
    HT [] B (hdrOut I)
      (Function.update (Function.update B pk r) sH (natSyms q ++ Sym.mark :: (natSyms D ++
        Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: B sH)))))
      (2 * (C * (bitLen K + 1)) + 2 + (2 * (C * (bitLen ℓ + 1)) + 2 + (2 * (C * (bitLen D + 1)) +
        2 + (2 * (C * (bitLen q + 1)) + 2)))) := by
  refine (HT.seq (HT.rsField hI B K (Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms D ++
      Sym.mark :: (natSyms q ++ r)))) (termOK_mark _) hB) <|
    HT.seq (HT.rsField hI _ ℓ (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms q ++ r)))
      (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.rsField hI _ D (Sym.mark :: (natSyms q ++ r)) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.rsField hI _ q r hr (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).of_eq ?_ le_rfl
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.hdrRead (hI : I.Spec C) (B : PL → List Sym) (q D ℓ K w : ℕ) (tl : List Sym)
    (hB : B sH = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl)))))
    (hpk : TermOK (B pk)) :
    HT [] B (hdrRead I)
      (Function.update (Function.update (Function.update B vq (natSyms q ++ B vq)) vl
        (natSyms ℓ ++ B vl)) vw (natSyms w ++ B vw)) (costHR C q D ℓ K w) := by
  refine (HT.seq (HT.hdrIn hI B q D ℓ K w tl hB) (HT.hdrOut hI _ q D ℓ K (B pk) hpk (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]))).of_eq
    ?_ ?_
  · simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne, hB]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · unfold costHR
    ring_nf
    omega

/-- Cost bound of `setup`. -/
def costSU (C w : ℕ) : ℕ := 40 * (C * (w + 1)) + 40

theorem HT.setup (hI : I.Spec C) (B : PL → List Sym) (q ℓ w : ℕ) (rq rl rw : List Sym)
    (hrq : TermOK rq) (hrl : TermOK rl) (hrw : TermOK rw) (hql : ℓ < q) (hqw : q + 2 ≤ w)
    (hvq : B vq = natSyms q ++ rq) (hvl : B vl = natSyms ℓ ++ rl) (hvw : B vw = natSyms w ++ rw)
    (htA : TermOK (B tA)) (_h6 : TermOK (B vq6)) (_h3 : TermOK (B vq3))
    (_h11 : TermOK (B vq11))
    (hP : TermOK (B vP)) (hPw : TermOK (B vPw)) (hd : TermOK (B vden)) :
    HT [] B (setup I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update B vq6 (natSyms (q + 6) ++ B vq6)) vq3
        (natSyms (q + 3) ++ B vq3)) vq11 (natSyms (q + 11) ++ B vq11)) vP
        (natSyms (2 ^ q) ++ B vP)) vPw (natSyms (2 ^ w) ++ B vPw)) vden
        (natSyms (2 * 2 ^ ℓ) ++ B vden)) ctr (natSyms (2 * 2 ^ ℓ) ++ B ctr))
      (costSU C w) := by
  have e2 : 2 ^ ℓ * 2 ^ 1 = 2 * 2 ^ ℓ := by ring
  have b6 : bitLen 6 ≤ 3 := bitLen_le_of_lt (by norm_num)
  have b3 : bitLen 3 ≤ 2 := bitLen_le_of_lt (by norm_num)
  have b11 : bitLen 11 ≤ 4 := bitLen_le_of_lt (by norm_num)
  have bq : bitLen q ≤ q := bitLen_le_self q
  have bw : bitLen w ≤ w := bitLen_le_self w
  have bl : bitLen ℓ ≤ ℓ := bitLen_le_self ℓ
  have bd : bitLen (2 ^ ℓ * 2 ^ 1) ≤ ℓ + 2 := by
    rw [e2, show 2 * 2 ^ ℓ = 2 ^ (ℓ + 1) by ring, bitLen_two_pow]; try omega
  refine (HT.seq (HT.paddC hI vq 6 tA vq6 (by decide) B q rq hrq hvq htA) <|
    HT.seq (HT.paddC hI vq 3 tA vq3 (by decide) _ q rq hrq (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvq]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htA)
      ) <|
    HT.seq (HT.paddC hI vq 11 tA vq11 (by decide) _ q rq hrq (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvq]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact htA)
      ) <|
    HT.seq (HT.ppow2 hI vq vP (by decide) _ q rq hrq (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvq]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hP)
      ) <|
    HT.seq (HT.ppow2 hI vw vPw (by decide) _ w rw hrw (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hPw)
      ) <|
    HT.seq (HT.ppow2 hI vl vden (by decide) _ ℓ rl hrl (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvl]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hd)
      ) <|
    HT.seq (HT.ps1 hI vden _ (2 ^ ℓ) (B vden) hd (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.pcp hI vden ctr (by decide) _ (2 ^ ℓ * 2 ^ 1) (B vden) hd (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])).of_eq ?_ ?_
  · rw [e2]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · have hW : w + 1 ≤ C * (w + 1) + (w + 1) := by omega
    have c1 := cmul_le C (bitLen q + bitLen 6 + 1) 2 (w + 1) (by omega)
    have c2 := cmul_le C (bitLen 6 + 1) 2 (w + 1) (by omega)
    have c3 := cmul_le C (bitLen q + bitLen 3 + 1) 2 (w + 1) (by omega)
    have c4 := cmul_le C (bitLen 3 + 1) 2 (w + 1) (by omega)
    have c5 := cmul_le C (bitLen q + bitLen 11 + 1) 2 (w + 1) (by omega)
    have c6 := cmul_le C (bitLen 11 + 1) 2 (w + 1) (by omega)
    have c7 := cmul_le C (q + bitLen q + 1) 2 (w + 1) (by omega)
    have c8 := cmul_le C (w + bitLen w + 1) 2 (w + 1) (by omega)
    have c9 := cmul_le C (ℓ + bitLen ℓ + 1) 2 (w + 1) (by omega)
    have c10 := cmul_le C (1 + 1) 1 (w + 1) (by omega)
    have c11 := cmul_le C (bitLen (2 ^ ℓ * 2 ^ 1) + 1) 1 (w + 1) (by omega)
    unfold costSU
    omega

end Rules


section Rules2

variable {I : PI} {C : ℕ}

/-- Cost bound of `cleanup`. -/
def costCL (C w : ℕ) : ℕ := 50 * (C * (w + 1))

theorem HT.cleanup (hI : I.Spec C) (B : PL → List Sym) (q ℓ w : ℕ)
    (r0 rd rp rP r11 r3 r6 rw rl rq : List Sym) (t0 : TermOK r0) (td : TermOK rd)
    (tp : TermOK rp) (tP : TermOK rP) (t11 : TermOK r11) (t3 : TermOK r3) (t6 : TermOK r6)
    (tw : TermOK rw) (tl : TermOK rl) (tq : TermOK rq) (hql : ℓ < q) (hqw : q + 2 ≤ w)
    (h0 : B ctr = natSyms 0 ++ r0) (hd : B vden = natSyms (2 * 2 ^ ℓ) ++ rd)
    (hp : B vPw = natSyms (2 ^ w) ++ rp) (hP : B vP = natSyms (2 ^ q) ++ rP)
    (h11 : B vq11 = natSyms (q + 11) ++ r11) (h3 : B vq3 = natSyms (q + 3) ++ r3)
    (h6 : B vq6 = natSyms (q + 6) ++ r6) (hw : B vw = natSyms w ++ rw)
    (hl : B vl = natSyms ℓ ++ rl) (hq : B vq = natSyms q ++ rq) :
    HT [] B (cleanup I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update B
        ctr r0) vden rd) vPw rp) vP rP) vq11 r11) vq3 r3) vq6 r6) vw rw) vl rl) vq rq)
      (costCL C w) := by
  refine (HT.seq (HT.pdr hI ctr B 0 r0 t0 h0) <|
    HT.seq (HT.pdr hI vden _ (2 * 2 ^ ℓ) rd td (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hd])) <|
    HT.seq (HT.pdr hI vPw _ (2 ^ w) rp tp (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hp])) <|
    HT.seq (HT.pdr hI vP _ (2 ^ q) rP tP (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hP])) <|
    HT.seq (HT.pdr hI vq11 _ (q + 11) r11 t11 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h11])) <|
    HT.seq (HT.pdr hI vq3 _ (q + 3) r3 t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h3])) <|
    HT.seq (HT.pdr hI vq6 _ (q + 6) r6 t6 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h6])) <|
    HT.seq (HT.pdr hI vw _ w rw tw (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hw])) <|
    HT.seq (HT.pdr hI vl _ ℓ rl tl (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hl])) <|
    HT.pdr hI vq _ q rq tq (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hq])).of_eq rfl ?_
  have bd : bitLen (2 * 2 ^ ℓ) = ℓ + 2 := by
    rw [show 2 * 2 ^ ℓ = 2 ^ (ℓ + 1) by ring, bitLen_two_pow]
  have bw2 : bitLen (2 ^ w) = w + 1 := bitLen_two_pow w
  have bq2 : bitLen (2 ^ q) = q + 1 := bitLen_two_pow q
  have b0 : bitLen 0 = 0 := bitLen_zero
  have b11 : bitLen (q + 11) ≤ q + 11 := bitLen_le_self _
  have b3 : bitLen (q + 3) ≤ q + 3 := bitLen_le_self _
  have b6 : bitLen (q + 6) ≤ q + 6 := bitLen_le_self _
  have bw : bitLen w ≤ w := bitLen_le_self _
  have bl : bitLen ℓ ≤ ℓ := bitLen_le_self _
  have bq : bitLen q ≤ q := bitLen_le_self _
  have c1 := cmul_le C (bitLen 0 + 1) 1 (w + 1) (by omega)
  have c2 := cmul_le C (bitLen (2 * 2 ^ ℓ) + 1) 1 (w + 1) (by omega)
  have c3 := cmul_le C (bitLen (2 ^ w) + 1) 2 (w + 1) (by omega)
  have c4 := cmul_le C (bitLen (2 ^ q) + 1) 1 (w + 1) (by omega)
  have c5 := cmul_le C (bitLen (q + 11) + 1) 11 (w + 1) (by omega)
  have c6 := cmul_le C (bitLen (q + 3) + 1) 11 (w + 1) (by omega)
  have c7 := cmul_le C (bitLen (q + 6) + 1) 11 (w + 1) (by omega)
  have c8 := cmul_le C (bitLen w + 1) 1 (w + 1) (by omega)
  have c9 := cmul_le C (bitLen ℓ + 1) 1 (w + 1) (by omega)
  have c10 := cmul_le C (bitLen q + 1) 1 (w + 1) (by omega)
  unfold costCL
  omega

theorem HT.emitEntry (hI : I.Spec C) (B : PL → List Sym) (w : ℕ) (re im : ℤ)
    (r1 r2 rw rp : List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2) (hrw : TermOK rw)
    (hrp : TermOK rp) (hx1 : B x1 = intSyms re ++ r1) (hx2 : B x2 = intSyms im ++ r2)
    (hvw : B vw = natSyms w ++ rw) (hvPw : B vPw = natSyms (2 ^ w) ++ rp)
    (huU : TermOK (B uU)) (hwc : TermOK (B wc)) (hfF : TermOK (B fF))
    (hre : re.natAbs < 2 ^ w) (him : im.natAbs < 2 ^ w) :
    HT [] B (emitEntry I)
      (Function.update (Function.update (Function.update B x1 r1) x2 r2) sT
        ((twosBits w re).map Sym.bit ++ ((twosBits w im).map Sym.bit ++ Sym.sep :: B sT)))
      (1 + (costEI C w + costEI C w)) := by
  refine (HT.seq (HT.pushS sT Sym.sep B []) <|
    HT.seq (HT.emitInt hI x2 (Or.inr rfl) _ w im r2 rw rp hr2 hrw hrp (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hx2])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvPw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact huU)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hwc) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hfF) him) <|
    HT.emitInt hI x1 (Or.inl rfl) _ w re r1 rw rp hr1 hrw hrp (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hx1])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvPw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact huU)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hwc) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hfF) hre).of_eq ?_ le_rfl
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

theorem HT.body (hI : I.Spec C) (B : PL → List Sym) (q ℓ w j : ℕ)
    (rc rl r6 rd r3 r11 rP rw rp : List Sym) (hrc : TermOK rc) (hrl : TermOK rl)
    (hr6 : TermOK r6) (hrd : TermOK rd) (hr3 : TermOK r3) (hr11 : TermOK r11) (hrP : TermOK rP)
    (hrw : TermOK rw) (hrp : TermOK rp) (hq : ℓ < q) (hw : q + 2 ≤ w) (hj : j < 2 * 2 ^ ℓ)
    (hctr : B ctr = natSyms j ++ rc) (hvl : B vl = natSyms ℓ ++ rl)
    (hv6 : B vq6 = natSyms (q + 6) ++ r6) (hvd : B vden = natSyms (2 * 2 ^ ℓ) ++ rd)
    (hv3 : B vq3 = natSyms (q + 3) ++ r3) (hv11 : B vq11 = natSyms (q + 11) ++ r11)
    (hvP : B vP = natSyms (2 ^ q) ++ rP) (hvw : B vw = natSyms w ++ rw)
    (hvPw : B vPw = natSyms (2 ^ w) ++ rp) (htA : TermOK (B tA)) (htB : TermOK (B tB))
    (htC : TermOK (B tC)) (htR : TermOK (B tR)) (htU : TermOK (B tU)) (hx1 : TermOK (B x1))
    (hx2 : TermOK (B x2)) (hfF : TermOK (B fF)) (huU : TermOK (B uU)) (hwc : TermOK (B wc)) :
    HT [] B (body I) (Function.update B sT (entrySyms w q ℓ j ++ B sT))
      (costVP C w + (1 + (costEI C w + costEI C w))) := by
  have hb := ptn_natAbs_lt q ℓ j hj
  have hqw : 2 ^ (q + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  refine (HT.seq (HT.valProg hI B q ℓ w j rc rl r6 rd r3 r11 rP hrc hrl hr6 hrd hr3 hr11 hrP hq hw
      hj hctr hvl hv6 hvd hv3 hv11 hvP htA htB htC htR htU hx1 hx2)
    (HT.emitEntry hI _ w (phaseTableNum q ℓ j).1 (phaseTableNum q ℓ j).2 (B x1) (B x2) rw rp hx1
      hx2 hrw hrp (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvw])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hvPw]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact huU) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hwc)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact hfF) (lt_of_lt_of_le hb.1 hqw) (lt_of_lt_of_le hb.2 hqw))).of_eq ?_ le_rfl
  unfold entrySyms
  simp only [List.map_append]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Rules2


/-! ## The whole builder -/

section Top

variable {I : PI} {C : ℕ}

/-- The loop state with counter `i`: constants set, entries `i, …, 2r-1` on `sT`. -/
def ptSt (S : PL → List Sym) (q ℓ w i : ℕ) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S vq (natSyms q ++ S vq)) vl (natSyms ℓ ++ S vl)) vw (natSyms w ++ S vw))
    vq6 (natSyms (q + 6) ++ S vq6)) vq3 (natSyms (q + 3) ++ S vq3)) vq11
    (natSyms (q + 11) ++ S vq11)) vP (natSyms (2 ^ q) ++ S vP)) vPw (natSyms (2 ^ w) ++ S vPw))
    vden (natSyms (2 * 2 ^ ℓ) ++ S vden)) ctr (natSyms i ++ S ctr)) sT
    (sfx (entrySyms w q ℓ) i (2 * 2 ^ ℓ) ++ S sT)

/-- Cost of one loop iteration's body. -/
def costBody (C w : ℕ) : ℕ := costVP C w + (1 + (costEI C w + costEI C w))

/-- The exact cost expression of the builder. -/
def costPT (C q D ℓ K w : ℕ) : ℕ :=
  costHR C q D ℓ K w + (costSU C w + ((C + loopCost (fun i => C * (bitLen (i + 1) + 1) +
    costBody C w + C) (2 * 2 ^ ℓ)) + costCL C w))

theorem HT.ptProg (hI : I.Spec C) (S : PL → List Sym) (hcl : ∀ e : Fin 32, S (.inr e) = [])
    (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym) (hsh : MidShapeOK q ℓ K w a)
    (hS1 : S sH = midHdr q ℓ K w a ++ hrest) :
    HT [] S (ptProg I) (Function.update S sT (tabSyms w q ℓ (phaseTable q ℓ) ++ S sT))
      (costPT C q D ℓ K w) := by
  obtain ⟨-, -, -, hlq, -, -, -, hw⟩ := hsh
  have t : ∀ e : Fin 32, TermOK (S (.inr e)) := fun e => by rw [hcl e]; exact TermOK.nil
  have hH : S sH = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (TMFw.Contracts.W9.hdrSyms
        (List.ofFn a) ++ hrest))))) := by
    rw [hS1, midHdr_eq]; simp only [List.cons_append, List.append_assoc]
  refine HT.seq (HT.hdrRead hI S q D ℓ K w _ hH (t 10)) ?_
  refine HT.seq ((HT.setup hI _ q ℓ w (S vq) (S vl) (S vw) (t 0) (t 1) (t 2) hlq hw
    (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])
    (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 11) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 3) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 4)
    (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 5) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 6) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 7)
    (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t 8)).of_eq (B₂ := ptSt S q ℓ w (2 * 2 ^ ℓ)) ?_ le_rfl) ?_
  · rw [ptSt, sfx_self, List.nil_append]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  refine HT.seq (HT.pcd hI ctr (S ctr) (t 9) (ptSt S q ℓ w) (fun i => by
      rw [ptSt]; simp (config := { failIfUnchanged := false }) (disch := decide) only
        [Function.update_self, Function.update_of_ne]) (Phase.body I) (fun _ => costBody C w)
      (2 * 2 ^ ℓ) (fun i hi => ?_)) ?_
  · refine (HT.body hI _ q ℓ w i (S ctr) (S vl) (S vq6) (S vden) (S vq3) (S vq11) (S vP) (S vw)
      (S vPw) (t 9) (t 1) (t 3) (t 8) (t 4) (t 5) (t 6) (t 2) (t 7) hlq hw hi
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 11) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 12)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 13) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 14)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 15) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 16)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 17) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 18)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 19) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]; exact t 20)).of_eq ?_ le_rfl
    rw [ptSt, ptSt, sfx_succ _ hi]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]
  · refine (HT.cleanup hI _ q ℓ w (S ctr) (S vden) (S vPw) (S vP) (S vq11) (S vq3) (S vq6)
      (S vw) (S vl) (S vq) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0) hlq hw
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, ptSt])).of_eq ?_ le_rfl
    rw [ptSt, tabSyms_phaseTable, natSyms_zero', List.nil_append]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [pupd_swap, Function.update_idem, pupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Top

end SubNLogN.Machine.FFT.Phase
