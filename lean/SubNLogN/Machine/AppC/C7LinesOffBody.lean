/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesOffKit

/-!
# Lemma A.9 offset routine: one scan position (`Machine/AppC/C7LinesOffBody.lean`)

`body neg par` processes scan position `p`. The selection tree `tree` tests: distance counter
zero? `2 k1 ≤ b - p + k2`? `x_p = 1`? `o_p = par`? It emits the output bit
`outBit neg (sBit k1 k2 b par x o) p`. Then `advance` pops the bits `x_p` and `o_p`, updates the
distance counter, and decrements `W = b - p + k2`. `r_body` takes the field contents `cAt … p` to
`cAt … (p + 1)`; the counter field is untouched. Everything here is fully proved. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7LinesOffAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith
  SubNLogN.Machine.Calculus SubNLogN.Math.Networks

theorem ordOf_eq_gt_iff (a b : ℕ) : ordOf a b = .gt ↔ b < a := by
  unfold ordOf
  split_ifs with h1 h2 <;> simp <;> omega

theorem seenB_succ (g : ℕ → Bool) (p : ℕ) : seenB g (p + 1) = (seenB g p || g p) := by
  simp [seenB, List.range_succ, List.any_append]

/-- The indicator bit as the conjunction of the four tests of `tree`. -/
theorem tree_s_eq {k1 k2 b par x o p : ℕ} (hpar : par ≤ 1) :
    sBit k1 k2 b par x o p = decide (distR k1 k2 p = 0 ∧ k1 + k1 ≤ b - p + k2 ∧
      x / 2 ^ p % 2 = 1 ∧ (o / 2 ^ p % 2 = 1 ↔ par = 1)) := by
  unfold sBit selB bitAt
  rw [← Bool.decide_and, decide_eq_decide]
  have hm := Nat.mod_lt (o / 2 ^ p) (by norm_num : 0 < 2)
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, by omega, h3, ?_⟩
    constructor
    · intro h
      omega
    · intro h
      omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, by omega⟩, h3, ?_⟩
    by_cases h : o / 2 ^ p % 2 = 1
    · have := h4.mp h
      omega
    · have : ¬ par = 1 := fun hp => h (h4.mpr hp)
      omega

/-- Selection and bit tests of the current position; every leaf emits the output bit. -/
def tree (neg : Bool) (par : ℕ) : OProg :=
  .seq (peekW (loc .D)) (.ite (fun r => optIsBit r.1) (emit neg false)
    (.seq (cmpN (loc .E2) (loc .W) sT1 sT2)
      (.ite (fun r => (fun o => decide (o = Ordering.gt)) r.2.2.2.2) (emit neg false)
        (.seq (peekW (loc .X))
          (.ite (fun r => (fun o => decide (o = some (Sym.bit true))) r.1)
            (.seq (peekW (loc .O))
              (.ite (fun r => (fun o => decide ((o = some (Sym.bit true)) ↔ par = 1)) r.1)
                (emit neg true) (emit neg false)))
            (emit neg false))))))

theorem closed_tree (neg : Bool) (par : ℕ) : (tree neg par).Closed :=
  ⟨closed_peekW _, closed_emit _ _, closed_cmpN_gen _ _ _ _, closed_emit _ _, closed_peekW _,
    ⟨closed_peekW _, closed_emit _ _, closed_emit _ _⟩, closed_emit _ _⟩

theorem r_tree (S : Stk → List Sym) (neg : Bool) (par : ℕ) (seen : Bool) (c : Sc)
    (d e w mx mo : ℕ) (jD jE jW jX jO jF : List Sym)
    (hD : c.D = natSyms d ++ Sym.mark :: jD) (hE : c.E2 = natSyms e ++ Sym.mark :: jE)
    (hW : c.W = natSyms w ++ Sym.mark :: jW) (hX : c.X = natSyms mx ++ Sym.mark :: jX)
    (hO : c.O = natSyms mo ++ Sym.mark :: jO)
    (hF : c.F = natSyms (neg && seen).toNat ++ Sym.mark :: jF)
    (s : Bool) (hs : s = decide (d = 0 ∧ e ≤ w ∧ mx % 2 = 1 ∧ (mo % 2 = 1 ↔ par = 1))) :
    RunsIn [] (tree neg par) (stk S c)
      (stk S ((c.set .Out (Sym.bit (if neg && seen then !s else s) :: c.Out)).set .F
        (natSyms (neg && (seen || s)).toNat ++ Sym.mark :: jF))) (fun _ => True)
      (12 * bitLen e + 26) := by
  have hDh : (stk S c (loc .D)).head? = (natSyms d ++ Sym.mark :: jD).head? := by
    rw [stk_loc]
    exact congrArg List.head? hD
  have hXh : (stk S c (loc .X)).head? = (natSyms mx ++ Sym.mark :: jX).head? := by
    rw [stk_loc]
    exact congrArg List.head? hX
  have hOh : (stk S c (loc .O)).head? = (natSyms mo ++ Sym.mark :: jO).head? := by
    rw [stk_loc]
    exact congrArg List.head? hO
  have hnd : [loc .E2, loc .W, sT1, sT2].Nodup := by decide
  unfold tree
  refine RunsIn.mono (r_ite_peek S optIsBit (T := 12 * bitLen e + 24) (fun h => ?_)
    (fun h => ?_)) (fun _ h => h) (by omega)
  · have hd : d ≠ 0 := by
      rw [hDh, optIsBit_head_natSyms _ _ (termOK_mark jD)] at h
      simpa using h
    have hs0 : s = false := by
      rw [hs, decide_eq_false_iff_not]
      rintro ⟨h1, -⟩
      exact hd h1
    subst hs0
    exact RunsIn.mono (r_emit S neg false seen c jF hF) (fun _ h => h) (by omega)
  · have hd : d = 0 := by
      rw [hDh, optIsBit_head_natSyms _ _ (termOK_mark jD)] at h
      simpa using h
    refine RunsIn.mono (r_ite_cmp S hnd (termOK_mark jE) (termOK_mark jW) hE hW
      (fun o => decide (o = Ordering.gt)) (T := 8) (fun h2 => ?_) (fun h2 => ?_))
      (fun _ h => h) (by omega)
    · have hew : w < e := by
        simp only [decide_eq_true_eq] at h2
        exact (ordOf_eq_gt_iff e w).mp h2
      have hs0 : s = false := by
        rw [hs, decide_eq_false_iff_not]
        rintro ⟨-, h1, -⟩
        omega
      subst hs0
      exact RunsIn.mono (r_emit S neg false seen c jF hF) (fun _ h => h) (by omega)
    · have hew : e ≤ w := by
        simp only [decide_eq_false_iff_not] at h2
        have := mt (ordOf_eq_gt_iff e w).mpr h2
        omega
      refine RunsIn.mono (r_ite_peek S (fun o => decide (o = some (Sym.bit true))) (T := 6)
        (fun h3 => ?_) (fun h3 => ?_)) (fun _ h => h) (by omega)
      · have hx : mx % 2 = 1 := by
          rw [hXh] at h3
          simp only [decide_eq_true_eq] at h3
          exact (head_eq_bit_true _ _ (termOK_mark jX)).mp h3
        refine RunsIn.mono (r_ite_peek S
          (fun o => decide ((o = some (Sym.bit true)) ↔ par = 1)) (T := 4) (fun h4 => ?_)
          (fun h4 => ?_)) (fun _ h => h) (by omega)
        · have ho : (mo % 2 = 1 ↔ par = 1) := by
            rw [hOh] at h4
            simp only [decide_eq_true_eq] at h4
            rw [head_eq_bit_true _ _ (termOK_mark jO)] at h4
            exact h4
          have hs0 : s = true := by
            rw [hs, decide_eq_true_eq]
            exact ⟨hd, hew, hx, ho⟩
          subst hs0
          exact r_emit S neg true seen c jF hF
        · have ho : ¬ (mo % 2 = 1 ↔ par = 1) := by
            rw [hOh] at h4
            simp only [decide_eq_false_iff_not] at h4
            rw [head_eq_bit_true _ _ (termOK_mark jO)] at h4
            exact h4
          have hs0 : s = false := by
            rw [hs, decide_eq_false_iff_not]
            rintro ⟨-, -, -, h1⟩
            exact ho h1
          subst hs0
          exact r_emit S neg false seen c jF hF
      · have hx : ¬ mx % 2 = 1 := by
          rw [hXh] at h3
          simp only [decide_eq_false_iff_not] at h3
          exact fun h => h3 ((head_eq_bit_true _ _ (termOK_mark jX)).mpr h)
        have hs0 : s = false := by
          rw [hs, decide_eq_false_iff_not]
          rintro ⟨-, -, h1, -⟩
          exact hx h1
        subst hs0
        exact RunsIn.mono (r_emit S neg false seen c jF hF) (fun _ h => h) (by omega)

/-- Update the distance counter: reload `k1 - 1` after a zero, else decrement. -/
def updD : OProg :=
  .seq (peekW (loc .D)) (.ite (fun r => optIsBit r.1) ((dec (loc .D) sT1).liftRegs lW)
    (copyN (loc .KM) (loc .D) sT1))

theorem closed_updD : updD.Closed :=
  ⟨closed_peekW _, WP.W9comp.closed_liftRegs lW (FramePassRAux.closed_dec _ _),
    closed_copyN _ _ _⟩

/-- Advance the scan by one position. -/
def advance : OProg :=
  .seq (readBit (loc .X)) (.seq (readBit (loc .O)) (.seq updD ((dec (loc .W) sT1).liftRegs lW)))

theorem closed_advance : advance.Closed :=
  ⟨closed_readBit _, closed_readBit _, closed_updD,
    WP.W9comp.closed_liftRegs lW (FramePassRAux.closed_dec _ _)⟩

theorem r_updD (S : Stk → List Sym) (c : Sc) (d km : ℕ) (jD jKM : List Sym)
    (hD : c.D = natSyms d ++ Sym.mark :: jD) (hKM : c.KM = natSyms km ++ Sym.mark :: jKM) :
    RunsIn [] updD (stk S c)
      (stk S (c.set .D (natSyms (if d = 0 then km else d - 1) ++ Sym.mark :: jD)))
      (fun _ => True) (6 * bitLen d + 7 * bitLen km + 17) := by
  have hb : optIsBit (stk S c (loc .D)).head? = decide (d ≠ 0) := by
    rw [stk_loc]
    show optIsBit c.D.head? = _
    rw [hD, optIsBit_head_natSyms _ _ (termOK_mark jD)]
  refine RunsIn.mono (r_ite_peek S optIsBit (T := 6 * bitLen d + 7 * bitLen km + 15)
    (fun h => ?_) (fun h => ?_)) (fun _ h => h) (by omega)
  · have hd : d ≠ 0 := by
      rw [hb] at h
      simpa using h
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h1 := r_dec S c .D d' (Sym.mark :: jD) (termOK_mark jD) hD
    rw [if_neg hd, Nat.add_sub_cancel]
    refine RunsIn.mono h1 (fun _ h => h) ?_
    have := zerosLead_le_length (encodeNat (d' + 1))
    simp only [bitLen]
    omega
  · have hd : d = 0 := by
      rw [hb] at h
      simpa using h
    subst hd
    rw [if_pos rfl]
    have e : c.get .D = Sym.mark :: jD := by
      show c.D = _
      rw [hD, natSyms_zero, List.nil_append]
    have h1 := r_copyN S (src := loc .KM) (f := .D) (by decide) (by decide) c km
      (Sym.mark :: jKM) (termOK_mark jKM) (by rw [stk_loc]; exact hKM)
    rw [e] at h1
    exact RunsIn.mono h1 (fun _ h => h) (by omega)

theorem r_advance (S : Stk → List Sym) (c : Sc) (mx mo d km w : ℕ)
    (jX jO jD jKM jW : List Sym) (hw : 1 ≤ w) (hX : c.X = natSyms mx ++ Sym.mark :: jX)
    (hO : c.O = natSyms mo ++ Sym.mark :: jO) (hD : c.D = natSyms d ++ Sym.mark :: jD)
    (hKM : c.KM = natSyms km ++ Sym.mark :: jKM) (hW : c.W = natSyms w ++ Sym.mark :: jW) :
    RunsIn [] advance (stk S c)
      (stk S ((((c.set .X (natSyms (mx / 2) ++ Sym.mark :: jX)).set .O
        (natSyms (mo / 2) ++ Sym.mark :: jO)).set .D
        (natSyms (if d = 0 then km else d - 1) ++ Sym.mark :: jD)).set .W
        (natSyms (w - 1) ++ Sym.mark :: jW))) (fun _ => True)
      (6 * bitLen d + 7 * bitLen km + 6 * bitLen w + 31) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h := RunsIn.seq (r_readBit S c .X mx (Sym.mark :: jX) (termOK_mark jX) hX)
    (RunsIn.seq (r_readBit S _ .O mo (Sym.mark :: jO) (termOK_mark jO) (by exact hO))
      (RunsIn.seq (r_updD S _ d km jD jKM (by exact hD) (by exact hKM))
        (r_dec S _ .W w' (Sym.mark :: jW) (termOK_mark jW) (by exact hW))))
  refine RunsIn.mono h (fun _ h => h) ?_
  have := zerosLead_le_length (encodeNat (w' + 1))
  simp only [bitLen]
  omega

/-- One scan position. -/
def body (neg : Bool) (par : ℕ) : OProg := .seq (tree neg par) advance

theorem closed_body (neg : Bool) (par : ℕ) : (body neg par).Closed :=
  ⟨closed_tree neg par, closed_advance⟩

/-- Field contents after the first `p` positions of the scan (counter field: its floor only). -/
def cAt (S : Stk → List Sym) (neg : Bool) (k1 k2 b par x o p : ℕ) : Sc :=
  ⟨natSyms (x / 2 ^ p) ++ Sym.mark :: S (loc .X),
    natSyms (o / 2 ^ p) ++ Sym.mark :: S (loc .O),
    natSyms (distR k1 k2 p) ++ Sym.mark :: S (loc .D),
    natSyms (k1 - 1) ++ Sym.mark :: S (loc .KM),
    natSyms (k1 + k1) ++ Sym.mark :: S (loc .E2),
    natSyms (b - p + k2) ++ Sym.mark :: S (loc .W),
    Sym.mark :: S (loc .Cn),
    ((List.range p).map (outBit neg (sBit k1 k2 b par x o))).reverse.map Sym.bit ++
      Sym.mark :: S (loc .Out),
    natSyms (neg && seenB (sBit k1 k2 b par x o) p).toNat ++ Sym.mark :: S (loc .F),
    S (loc .Dst)⟩

theorem Sc.ext' {c d : Sc} (h1 : c.X = d.X) (h2 : c.O = d.O) (h3 : c.D = d.D)
    (h4 : c.KM = d.KM) (h5 : c.E2 = d.E2) (h6 : c.W = d.W) (h7 : c.Cn = d.Cn)
    (h8 : c.Out = d.Out) (h9 : c.F = d.F) (h10 : c.Dst = d.Dst) : c = d := by
  cases c
  cases d
  simp only [Sc.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- **One scan position**: from `cAt … p` to `cAt … (p + 1)` (any counter content `cn`). -/
theorem r_body (S : Stk → List Sym) (neg : Bool) (k1 k2 b par x o p : ℕ) (hpar : par ≤ 1)
    (hp : p < b) (cn : List Sym) :
    RunsIn [] (body neg par) (stk S ((cAt S neg k1 k2 b par x o p).set .Cn cn))
      (stk S ((cAt S neg k1 k2 b par x o (p + 1)).set .Cn cn)) (fun _ => True)
      (12 * bitLen (k1 + k1) + 6 * bitLen (distR k1 k2 p) + 7 * bitLen (k1 - 1) +
        6 * bitLen (b - p + k2) + 57) := by
  have ht := r_tree S neg par (seenB (sBit k1 k2 b par x o) p)
    ((cAt S neg k1 k2 b par x o p).set .Cn cn) (distR k1 k2 p) (k1 + k1) (b - p + k2)
    (x / 2 ^ p) (o / 2 ^ p) (S (loc .D)) (S (loc .E2)) (S (loc .W)) (S (loc .X)) (S (loc .O))
    (S (loc .F)) rfl rfl rfl rfl rfl rfl (sBit k1 k2 b par x o p) (tree_s_eq hpar)
  refine RunsIn.congr (RunsIn.seq ht (r_advance S _ (x / 2 ^ p) (o / 2 ^ p) (distR k1 k2 p)
    (k1 - 1) (b - p + k2) (S (loc .X)) (S (loc .O)) (S (loc .D)) (S (loc .KM)) (S (loc .W))
    (by omega) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)))
    (congrArg (stk S) (Sc.ext' ?_ ?_ ?_ rfl rfl ?_ rfl ?_ ?_ rfl)) (by omega)
  · show natSyms (x / 2 ^ p / 2) ++ Sym.mark :: S (loc .X) =
      natSyms (x / 2 ^ (p + 1)) ++ Sym.mark :: S (loc .X)
    rw [div_two_pow_succ]
  · show natSyms (o / 2 ^ p / 2) ++ Sym.mark :: S (loc .O) =
      natSyms (o / 2 ^ (p + 1)) ++ Sym.mark :: S (loc .O)
    rw [div_two_pow_succ]
  · rfl
  · show natSyms (b - p + k2 - 1) ++ Sym.mark :: S (loc .W) =
      natSyms (b - (p + 1) + k2) ++ Sym.mark :: S (loc .W)
    rw [show b - p + k2 - 1 = b - (p + 1) + k2 by omega]
  · show Sym.bit (if neg && seenB (sBit k1 k2 b par x o) p then !sBit k1 k2 b par x o p
        else sBit k1 k2 b par x o p) ::
        (((List.range p).map (outBit neg (sBit k1 k2 b par x o))).reverse.map Sym.bit ++
          Sym.mark :: S (loc .Out)) =
      ((List.range (p + 1)).map (outBit neg (sBit k1 k2 b par x o))).reverse.map Sym.bit ++
        Sym.mark :: S (loc .Out)
    rw [List.range_succ, List.map_append, List.reverse_append] <;> rfl
  · show natSyms (neg && (seenB (sBit k1 k2 b par x o) p || sBit k1 k2 b par x o p)).toNat ++
        Sym.mark :: S (loc .F) =
      natSyms (neg && seenB (sBit k1 k2 b par x o) (p + 1)).toNat ++ Sym.mark :: S (loc .F)
    rw [seenB_succ]

end SubNLogN.Machine.AppC.C7LinesOffAux
