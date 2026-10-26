/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPass1

/-!
# K5-PP pass 2 (`Bridge/PrePostPass2.lean`): the thermometer of `max ⌈log₂ |a|⌉`

Second pass of the pre-scaling scan (Theorem 4.7 (`thm:bridge-precision`): `H = 1 + ⌈log₂ C⌉`). Pass 1
left on `Y` the tagged fields of all records, last record first, each field most significant bit
first. Pass 2 pops them, pushes the plain bits back onto `Y2` (so `Y2` receives the input array in
its original format and order), and updates a **thermometer** `T` (`w` bits, most significant
position on top): for a field with value `a`, position `k` is or-ed with
`u_k = [2^k < |a|]`, computed from the tags on the fly (`p2u`: for `a < 0`, `u_k` = some bit
`j ≥ k` is `0`; for `a ≥ 0`, `u_k` = some bit `j > k` is `1`, or bit `k` is `1` and a lower bit is
`1`). The math of `u_k` is in `PrePostScanMath.lean`.

**Scope (honest summary).** Programs and proved `Eval`/`Runs` lemmas (no `sorry`):
`p2Loop_eval` (one field, exact, generic in the tag pairs and thermometer bits), `runs_p2Field`,
`runs_p2Rec`, `runs_p2Arr`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

/-- The thermometer update bit `u_k` from the class `ng`, the running flag `sn` and the tag. -/
def p2u (ng sn b f : Bool) : Bool := if ng then sn || !b else sn || (b && f)

/-- The running flag after a position. -/
def p2sn (ng sn b : Bool) : Bool := if ng then sn || !b else sn || b

/-- Output thermometer bits of one field, in processing order (most significant first). -/
def p2outs (ng : Bool) : Bool → List (Bool × Bool) → List Bool → List Bool
  | sn, (b, f) :: ps, τ :: τs => (τ || p2u ng sn b f) :: p2outs ng (p2sn ng sn b) ps τs
  | _, _, _ => []

/-- The tag pairs `(b_k, f_k)` of a field (LSB first), `f_k` = some lower bit is set. -/
def flagPairs : Bool → List Bool → List (Bool × Bool)
  | _, [] => []
  | f, b :: bs => (b, f) :: flagPairs (f || b) bs

theorem tagList_eq_map : ∀ (f : Bool) (bs : List Bool),
    tagList f bs = (flagPairs f bs).map fun p => tagOf p.1 p.2
  | _, [] => rfl
  | f, b :: bs => by simp [tagList, flagPairs, tagList_eq_map _ bs]

theorem map_fst_flagPairs : ∀ (f : Bool) (bs : List Bool), (flagPairs f bs).map Prod.fst = bs
  | _, [] => rfl
  | f, b :: bs => by simp [flagPairs, map_fst_flagPairs _ bs]

@[simp] theorem length_flagPairs : ∀ (f : Bool) (bs : List Bool), (flagPairs f bs).length = bs.length
  | _, [] => rfl
  | f, _ :: bs => by simp [flagPairs, length_flagPairs _ bs]

theorem length_p2outs (ng : Bool) : ∀ (sn : Bool) (ps : List (Bool × Bool)) (τs : List Bool),
    ps.length = τs.length → (p2outs ng sn ps τs).length = ps.length
  | _, [], [], _ => rfl
  | sn, (b, f) :: ps, τ :: τs, h => by
    simp only [p2outs, List.length_cons]
    rw [length_p2outs ng _ ps τs (by simpa using h)]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-! ## Programs -/

variable {K : Type}

/-- Pass 2, one position: pop the thermometer bit and the tag, push the updated thermometer bit on
`T2` and the plain bit on `Y2`, update `sn`. -/
def p2Body (Y Y2 T T2 : K) : PProg K :=
  .seq (.pop T fun v o => { v with o := o })
  (.seq (.pop Y fun v o => { v with q := o })
  (.seq (.push T2 fun v => .bit (bitOf v.o || p2u v.ng v.sn (tagB v.q) (tagF v.q)))
  (.seq (.push Y2 fun v => .bit (tagB v.q))
  (.seq (.load fun v => { v with sn := p2sn v.ng v.sn (tagB v.q) })
    (peekT T)))))

/-- Pass 2, the loop over the positions of one field (driven by the thermometer `T`). -/
def p2Loop (Y Y2 T T2 : K) : PProg K := .loop (fun v => isBitO v.t) (p2Body Y Y2 T T2)

/-- Pass 2, one field: the class is the bit of the first tag (the sign bit); the new thermometer
is moved back from `T2` to `T`. -/
def p2Field (Y Y2 T T2 : K) : PProg K :=
  .seq (.peek Y fun v o => { v with ng := tagB o, sn := false })
  (.seq (peekT T) (.seq (p2Loop Y Y2 T T2) ((moveBits T2 T).liftRegs lensPO)))

/-- Pass 2, one record: the record end, then the two fields (imaginary part first). -/
def p2Rec (Y Y2 T T2 : K) : PProg K :=
  .seq ((moveSym Y Y2).liftRegs lensPO) (.seq (p2Field Y Y2 T T2) (p2Field Y Y2 T T2))

/-- Pass 2, the array loop (while `Y` shows a record end). -/
def p2Arr (Y Y2 T T2 : K) : PProg K :=
  .seq (peekT Y) (.loop (fun v => isSepO v.t) (.seq (p2Rec Y Y2 T T2) (peekT Y)))

theorem closed_p2Arr (Y Y2 T T2 : K) : (p2Arr Y Y2 T T2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, p2Arr, p2Rec, p2Field, p2Loop, p2Body, peekT, moveSym, popR,
    pushR, moveBits, moveBitsBody, Prog.liftRegs]

/-! ## One field -/

section Eval

variable [DecidableEq K]

theorem p2Body_eval {Y Y2 T T2 : K} (h1 : Y ≠ Y2) (h2 : Y ≠ T) (h3 : Y ≠ T2) (h4 : Y2 ≠ T)
    (h5 : Y2 ≠ T2) (h6 : T ≠ T2) (b f τ : Bool) (LY LT : List Sym) (v : PReg) (S : K → List Sym)
    (hY : S Y = tagOf b f :: LY) (hT : S T = Sym.bit τ :: LT) :
    Eval [] (p2Body Y Y2 T T2) ⟨v, S⟩
      ⟨{ v with o := some (.bit τ), q := some (tagOf b f), sn := p2sn v.ng v.sn b, t := LT.head? },
        Function.update (Function.update (Function.update (Function.update S T LT) Y LY) T2
          (Sym.bit (τ || p2u v.ng v.sn b f) :: S T2)) Y2 (Sym.bit b :: S Y2)⟩ 6 := by
  have e := Eval.seq (Eval.pop (Γ := fun _ => Sym) [] T (fun v o => { v with o := o }) v S)
    (Eval.seq (Eval.pop (Γ := fun _ => Sym) [] Y (fun v o => { v with q := o }) _ _)
    (Eval.seq (Eval.push (Γ := fun _ => Sym) [] T2
      (fun v : PReg => Sym.bit (bitOf v.o || p2u v.ng v.sn (tagB v.q) (tagF v.q))) _ _)
    (Eval.seq (Eval.push (Γ := fun _ => Sym) [] Y2 (fun v : PReg => Sym.bit (tagB v.q)) _ _)
    (Eval.seq (Eval.load (Γ := fun _ => Sym) []
      (fun v : PReg => { v with sn := p2sn v.ng v.sn (tagB v.q) }) _ _)
      (Eval.peek (Γ := fun _ => Sym) [] T (fun v o => { v with t := o }) _ _)))))
  refine e.of_eq ?_ rfl
  have hY1 : Function.update S T LT Y = tagOf b f :: LY := by rw [Function.update_of_ne h2, hY]
  have hT2 : Function.update (Function.update S T LT) Y LY T2 = S T2 := by
    rw [Function.update_of_ne h3.symm, Function.update_of_ne h6.symm]
  have hY2 : Function.update (Function.update (Function.update S T LT) Y LY) T2
      (Sym.bit (τ || p2u v.ng v.sn b f) :: S T2) Y2 = S Y2 := by
    rw [Function.update_of_ne h5, Function.update_of_ne h1.symm, Function.update_of_ne h4]
  have hT3 : Function.update (Function.update (Function.update (Function.update S T LT) Y LY) T2
      (Sym.bit (τ || p2u v.ng v.sn b f) :: S T2)) Y2 (Sym.bit b :: S Y2) T = LT := by
    rw [Function.update_of_ne h4.symm, Function.update_of_ne h6, Function.update_of_ne h2.symm,
      Function.update_self]
  simp only [hT, List.head?_cons, List.tail_cons, hY1, bitOf_bit, tagB_tagOf, tagF_tagOf, hT2, hY2,
    hT3]

theorem p2Loop_eval {Y Y2 T T2 : K} (h1 : Y ≠ Y2) (h2 : Y ≠ T) (h3 : Y ≠ T2) (h4 : Y2 ≠ T)
    (h5 : Y2 ≠ T2) (h6 : T ≠ T2) :
    ∀ (ps : List (Bool × Bool)) (τs : List Bool), ps.length = τs.length →
      ∀ (LY DT : List Sym) (v : PReg) (S : K → List Sym), TermOK DT →
      S Y = ps.map (fun p => tagOf p.1 p.2) ++ LY → S T = τs.map Sym.bit ++ DT →
      v.t = (S T).head? →
      ∃ v' : PReg, v'.ng = v.ng ∧ Eval [] (p2Loop Y Y2 T T2) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S T DT) Y LY) T2
          ((p2outs v.ng v.sn ps τs).reverse.map Sym.bit ++ S T2)) Y2
          ((ps.map Prod.fst).reverse.map Sym.bit ++ S Y2)⟩ (7 * ps.length + 1)
  | [], [], _, LY, DT, v, S, hDT, hY, hT, hv => by
    simp only [List.map_nil, List.nil_append] at hY hT
    refine ⟨v, rfl, (Eval.loop_false ?_).of_eq ?_ rfl⟩
    · show isBitO v.t = false
      rw [hv, hT]
      exact isBitO_of_termOK hDT
    · simp only [p2outs, List.reverse_nil, List.map_nil, List.nil_append]
      rw [← hY, ← hT, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self]
  | (b, f) :: ps, τ :: τs, hlen, LY, DT, v, S, hDT, hY, hT, hv => by
    simp only [List.map_cons, List.cons_append] at hY hT
    have eb := p2Body_eval h1 h2 h3 h4 h5 h6 b f τ (ps.map (fun p => tagOf p.1 p.2) ++ LY)
      (τs.map Sym.bit ++ DT) v S hY hT
    set S6 := Function.update (Function.update (Function.update (Function.update S T
      (τs.map Sym.bit ++ DT)) Y (ps.map (fun p => tagOf p.1 p.2) ++ LY)) T2
      (Sym.bit (τ || p2u v.ng v.sn b f) :: S T2)) Y2 (Sym.bit b :: S Y2) with hS6
    have h6Y : S6 Y = ps.map (fun p => tagOf p.1 p.2) ++ LY := by
      rw [hS6, Function.update_of_ne h1, Function.update_of_ne h3, Function.update_self]
    have h6T : S6 T = τs.map Sym.bit ++ DT := by
      rw [hS6, Function.update_of_ne h4.symm, Function.update_of_ne h6, Function.update_of_ne h2.symm,
        Function.update_self]
    obtain ⟨v', hv'ng, e'⟩ := p2Loop_eval h1 h2 h3 h4 h5 h6 ps τs (by simpa using hlen) LY DT
      { v with
        o := some (.bit τ), q := some (tagOf b f), sn := p2sn v.ng v.sn b,
        t := (τs.map Sym.bit ++ DT).head? } S6 hDT h6Y h6T (by rw [h6T])
    refine ⟨v', hv'ng, (Eval.loop_true ?_ eb e').of_eq ?_ (by simp only [List.length_cons]; ring)⟩
    · show isBitO v.t = true
      rw [hv, hT]
      rfl
    · congr 1
      have hT2' : S6 T2 = Sym.bit (τ || p2u v.ng v.sn b f) :: S T2 := by
        rw [hS6, Function.update_of_ne h5.symm, Function.update_self]
      have hY2' : S6 Y2 = Sym.bit b :: S Y2 := by rw [hS6, Function.update_self]
      rw [hT2', hY2']
      funext k
      simp only [hS6, Function.update_apply, p2outs, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all

/-- The class of a field from its first tag pair (the sign bit). -/
def ngOf (ps : List (Bool × Bool)) : Bool := (ps.head?.map Prod.fst).getD false

/-- **Pass 2, one field**, as `Runs` (any register). `T2` must be empty. -/
theorem runs_p2Field {Y Y2 T T2 : K} (h1 : Y ≠ Y2) (h2 : Y ≠ T) (h3 : Y ≠ T2) (h4 : Y2 ≠ T)
    (h5 : Y2 ≠ T2) (h6 : T ≠ T2) (ps : List (Bool × Bool)) (τs : List Bool) (hne : ps ≠ [])
    (hlen : ps.length = τs.length) (LY DT : List Sym) (S : K → List Sym) (hDT : TermOK DT)
    (hY : S Y = ps.map (fun p => tagOf p.1 p.2) ++ LY) (hT : S T = τs.map Sym.bit ++ DT)
    (hT2 : S T2 = []) :
    Runs (p2Field Y Y2 T T2) S
      (Function.update (Function.update (Function.update S T
        ((p2outs (ngOf ps) false ps τs).map Sym.bit ++ DT)) Y LY) Y2
        ((ps.map Prod.fst).reverse.map Sym.bit ++ S Y2)) (fun _ => True) (10 * ps.length + 5) := by
  obtain ⟨⟨b0, f0⟩, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    rcases ps with _ | ⟨p, ps'⟩
    · exact absurd rfl hne
    · exact ⟨p, ps', rfl⟩
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (.peek Y fun v o => { v with ng := tagB o, sn := false } : PProg K) ⟨v, S⟩
      ⟨{ v with ng := b0, sn := false }, S⟩ 1 := by
    refine (Eval.peek [] Y _ v S).of_eq ?_ rfl
    rw [hY]
    simp
  have e2 := Eval.peek (Γ := fun _ => Sym) [] T (fun v o => { v with t := o })
    { v with ng := b0, sn := false } S
  obtain ⟨v3, hv3, e3⟩ := p2Loop_eval h1 h2 h3 h4 h5 h6 ((b0, f0) :: ps') τs hlen LY DT
    { { v with ng := b0, sn := false } with t := (S T).head? } S hDT hY hT rfl
  set outs := p2outs b0 false ((b0, f0) :: ps') τs with houts
  set S3 := Function.update (Function.update (Function.update (Function.update S T DT) Y LY) T2
    (outs.reverse.map Sym.bit ++ S T2)) Y2
    ((((b0, f0) :: ps').map Prod.fst).reverse.map Sym.bit ++ S Y2) with hS3
  have hS3T2 : S3 T2 = outs.reverse.map Sym.bit ++ [] := by
    rw [hS3, Function.update_of_ne h5.symm, Function.update_self, hT2]
  have e4 := moveBits_eval (ρ := []) h6.symm (lensPO.get v3) outs.reverse [] S3 TermOK.nil hS3T2
  have hS3T : S3 T = DT := by
    rw [hS3, Function.update_of_ne h4.symm, Function.update_of_ne h6, Function.update_of_ne h2.symm,
      Function.update_self]
  have e4' : Eval [] ((moveBits T2 T).liftRegs lensPO) ⟨v3, S3⟩
      ⟨{ v3 with o := none }, Function.update (Function.update (Function.update S T
        (outs.map Sym.bit ++ DT)) Y LY) Y2
        ((((b0, f0) :: ps').map Prod.fst).reverse.map Sym.bit ++ S Y2)⟩
      (3 * outs.reverse.length + 2) := by
    refine (Eval.liftRegs lensPO e4 v3 rfl).of_eq ?_ rfl
    show (⟨{ v3 with o := none }, _⟩ : St K (fun _ => Sym) PReg) = _
    congr 1
    rw [hS3T, List.reverse_reverse, List.tail_nil]
    funext k
    simp only [hS3, Function.update_apply]
    split_ifs <;> simp_all
  have hl : outs.reverse.length = ((b0, f0) :: ps').length := by
    rw [List.length_reverse, houts, length_p2outs _ _ _ _ hlen]
  rw [hl] at e4'
  exact ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4')), trivial, by omega⟩

/-! ## Records and the array -/

/-- Thermometer after one field with bits `bs` (most significant position first). -/
def p2fieldT (bs τ : List Bool) : List Bool :=
  p2outs (ngOf (flagPairs false bs).reverse) false (flagPairs false bs).reverse τ

/-- Thermometer after one record `[c]` (imaginary part first). -/
def p2recT (w : ℕ) (τ : List Bool) (c : CInt) : List Bool :=
  p2fieldT (twosBits w c.1) (p2fieldT (twosBits w c.2) τ)

theorem length_p2fieldT (bs τ : List Bool) (h : bs.length = τ.length) :
    (p2fieldT bs τ).length = τ.length := by
  unfold p2fieldT
  rw [length_p2outs _ _ _ _ (by simpa using h)]
  simpa using h

theorem length_p2recT (w : ℕ) (τ : List Bool) (c : CInt) (h : τ.length = w) :
    (p2recT w τ c).length = w := by
  have h1 : (p2fieldT (twosBits w c.2) τ).length = w := by
    rw [length_p2fieldT _ _ (by rw [length_twosBits', h])]
    exact h
  unfold p2recT
  rw [length_p2fieldT _ _ (by rw [length_twosBits', h1])]
  exact h1

theorem length_foldl_p2recT (w : ℕ) : ∀ (cs : List CInt) (τ : List Bool), τ.length = w →
    (cs.foldl (p2recT w) τ).length = w
  | [], _, h => h
  | c :: cs, τ, h => length_foldl_p2recT w cs _ (length_p2recT w τ c h)

theorem rev_tagList_eq (bs : List Bool) :
    (tagList false bs).reverse = (flagPairs false bs).reverse.map fun p => tagOf p.1 p.2 := by
  rw [tagList_eq_map, List.map_reverse]

theorem rev_map_fst (bs : List Bool) :
    ((flagPairs false bs).reverse.map Prod.fst).reverse = bs := by
  rw [List.map_reverse, List.reverse_reverse, map_fst_flagPairs]

theorem flagPairs_rev_ne_nil {bs : List Bool} (h : bs ≠ []) : (flagPairs false bs).reverse ≠ [] := by
  intro h'
  apply h
  have := congrArg List.length h'
  simp only [List.length_reverse, length_flagPairs, List.length_nil] at this
  exact List.eq_nil_of_length_eq_zero this

theorem twosBits_ne_nil {w : ℕ} (hw : 1 ≤ w) (z : ℤ) : twosBits w z ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_twosBits'] at this
  simp at this
  omega

/-- **Pass 2, one record.** -/
theorem runs_p2Rec {Y Y2 T T2 : K} (h1 : Y ≠ Y2) (h2 : Y ≠ T) (h3 : Y ≠ T2) (h4 : Y2 ≠ T)
    (h5 : Y2 ≠ T2) (h6 : T ≠ T2) {w : ℕ} (hw : 1 ≤ w) (c : CInt) (τ : List Bool)
    (hτ : τ.length = w) (LY DT : List Sym) (S : K → List Sym) (hDT : TermOK DT)
    (hY : S Y = yRec w c ++ LY) (hT : S T = τ.map Sym.bit ++ DT) (hT2 : S T2 = []) :
    Runs (p2Rec Y Y2 T T2) S
      (Function.update (Function.update (Function.update S Y LY) Y2 (recC w c ++ S Y2)) T
        ((p2recT w τ c).map Sym.bit ++ DT)) (fun _ => True) (20 * w + 12) := by
  set bs1 := twosBits w c.1 with hbs1
  set bs2 := twosBits w c.2 with hbs2
  have hY0 : S Y = Sym.sep :: ((flagPairs false bs2).reverse.map (fun p => tagOf p.1 p.2) ++
      ((flagPairs false bs1).reverse.map (fun p => tagOf p.1 p.2) ++ LY)) := by
    rw [hY, yRec, ← hbs1, ← hbs2, rev_tagList_eq, rev_tagList_eq]
    simp
  have r0 := runs_liftRegs lensPO (runs_moveSym h1 Sym.sep _ S hY0)
  set S0 := Function.update (Function.update S Y ((flagPairs false bs2).reverse.map
    (fun p => tagOf p.1 p.2) ++ ((flagPairs false bs1).reverse.map (fun p => tagOf p.1 p.2) ++ LY)))
    Y2 (Sym.sep :: S Y2) with hS0
  have r1 := runs_p2Field h1 h2 h3 h4 h5 h6 (flagPairs false bs2).reverse τ
    (flagPairs_rev_ne_nil (twosBits_ne_nil hw _)) (by simp [hbs2, length_twosBits', hτ]) _ DT S0 hDT
    (by rw [hS0, Function.update_of_ne h1, Function.update_self])
    (by rw [hS0, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, hT])
    (by rw [hS0, Function.update_of_ne h5.symm, Function.update_of_ne h3.symm, hT2])
  set S1 := Function.update (Function.update (Function.update S0 T
    ((p2fieldT bs2 τ).map Sym.bit ++ DT)) Y
    ((flagPairs false bs1).reverse.map (fun p => tagOf p.1 p.2) ++ LY)) Y2
    (((flagPairs false bs2).reverse.map Prod.fst).reverse.map Sym.bit ++ S0 Y2) with hS1
  have r2 := runs_p2Field h1 h2 h3 h4 h5 h6 (flagPairs false bs1).reverse (p2fieldT bs2 τ)
    (flagPairs_rev_ne_nil (twosBits_ne_nil hw _))
    (by rw [length_p2fieldT _ _ (by simp [hbs2, length_twosBits', hτ])]
        simp [hbs1, length_twosBits', hτ]) LY DT S1 hDT
    (by rw [hS1, Function.update_of_ne h1, Function.update_self])
    (by rw [hS1, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm,
      Function.update_self])
    (by rw [hS1, Function.update_of_ne h5.symm, Function.update_of_ne h3.symm,
      Function.update_of_ne h6.symm, hS0, Function.update_of_ne h5.symm,
      Function.update_of_ne h3.symm, hT2])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r0
    (WP.W9comp.runs_seq r1 r2)) ?_) (fun _ _ => trivial) (by simp [length_twosBits', hbs1, hbs2]; omega)
  have hrec : recC w c = bs1.map Sym.bit ++ (bs2.map Sym.bit ++ [Sym.sep]) := by
    simp [recC, hbs1, hbs2]
  funext k
  simp only [hS1, hS0, Function.update_apply, rev_map_fst, p2recT, p2fieldT, hrec, ← hbs1, ← hbs2]
  split_ifs <;> simp_all

theorem isSepO_of_nil_or_yRec {w : ℕ} (rest : List CInt) :
    isSepO ((rest.map (yRec w)).flatten).head? = !rest.isEmpty := by
  rcases rest with _ | ⟨x, rest⟩
  · rfl
  · simp [yRec]

/-- **Pass 2, the whole array.** `Y` holds exactly the tagged records; `T2` is empty. -/
theorem runs_p2Arr {Y Y2 T T2 : K} (h1 : Y ≠ Y2) (h2 : Y ≠ T) (h3 : Y ≠ T2) (h4 : Y2 ≠ T)
    (h5 : Y2 ≠ T2) (h6 : T ≠ T2) {w : ℕ} (hw : 1 ≤ w) (rs : List CInt) (τ0 : List Bool)
    (hτ0 : τ0.length = w) (DT : List Sym) (S : K → List Sym) (hDT : TermOK DT)
    (hY : S Y = (rs.map (yRec w)).flatten) (hT : S T = τ0.map Sym.bit ++ DT) (hT2 : S T2 = []) :
    Runs (p2Arr Y Y2 T T2) S
      (Function.update (Function.update (Function.update S Y []) Y2
        ((rs.reverse.map (recC w)).flatten ++ S Y2)) T
        ((rs.foldl (p2recT w) τ0).map Sym.bit ++ DT)) (fun _ => True)
      (rs.length * (20 * w + 14) + 2) := by
  let st : List CInt → List CInt → K → List Sym := fun done rest =>
    Function.update (Function.update (Function.update S Y (rest.map (yRec w)).flatten) Y2
      ((done.reverse.map (recC w)).flatten ++ S Y2)) T ((done.foldl (p2recT w) τ0).map Sym.bit ++ DT)
  have h0 : st [] rs = S := by
    simp only [st, List.reverse_nil, List.map_nil, List.flatten_nil, List.nil_append, List.foldl_nil]
    rw [← hY, ← hT, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  have hw' := runs_while (pk := peekT Y) (body := p2Rec Y Y2 T T2)
    (c := fun v => isSepO v.t) st 1 (fun _ _ _ => 20 * w + 12)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT Y (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self] at hv
      show isSepO v.t = !rest.isEmpty
      rw [hv, isSepO_of_nil_or_yRec])
    (fun done x rest => by
      have hr := runs_p2Rec h1 h2 h3 h4 h5 h6 hw x (done.foldl (p2recT w) τ0)
        (length_foldl_p2recT w done τ0 hτ0) ((rest.map (yRec w)).flatten) DT (st done (x :: rest))
        hDT (by simp [st, Function.update_of_ne h2, Function.update_of_ne h1])
        (by simp [st])
        (by simp only [st, Function.update_of_ne h6.symm, Function.update_of_ne h5.symm,
          Function.update_of_ne h3.symm]; exact hT2)
      refine WP.W9comp.runs_congr hr ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all [List.foldl_append])
    rs []
  rw [h0] at hw'
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw' ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 (20 * w + 12) (fun _ _ _ => 20 * w + 12) (fun _ _ _ => le_rfl) rs []
    nlinarith

end Eval

end SubNLogN.Machine.BridgePP
