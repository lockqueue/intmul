/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepLeaf

/-!
# K5-SOLVE (1e): element steps of the sweep kernel

One column step of each pass, as a fixed sequence of record moves/copies and leaf calls on the
temporaries `xa … xg` (all empty before and after):
* `e2`: prefix step for rows `j ≥ 1`: `y` from `dat`, `μ` from `mu`, `-â` from `na` (both
  recorded on `muO`, `naO`), `p` from `stI`; pushes `b = Quant_q(μy)` on `bS` and
  `p' = b + Quant_q(-â p)` on `stO`.
All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

theorem carrSyms_one (w : ℕ) (c : CInt) : carrSyms w [[c]] = recSyms (crecBits w [c]) := by
  simp [carrSyms, arrSyms, blk]

theorem crecBits_one_length (w : ℕ) (c : CInt) : (crecBits w [c]).length = 2 * w := by
  simp [crecBits, coefBits, twosBits_length]; ring

/-- If `a` and `a + d` fit `w ≥ 1` bits, then `d` fits `w + 1` bits. -/
theorem fitsTwos_sub_succ {w : ℕ} (hw : 1 ≤ w) {a d : ℤ} (ha : FitsTwos w a)
    (had : FitsTwos w (a + d)) : FitsTwos (w + 1) d := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := had
  have hp : (2 : ℤ) ^ (w + 1 - 1) = 2 * 2 ^ (w - 1) := by
    rw [show w + 1 - 1 = (w - 1) + 1 by omega, pow_succ]; ring
  show -(2 ^ (w + 1 - 1) : ℤ) ≤ d ∧ d < 2 ^ (w + 1 - 1)
  rw [hp]
  constructor <;> linarith

/-- Temporaries empty. -/
structure TempsEmpty (V : SwD ⊕ SwW → List Sym) : Prop where
  xa : V (.inr .xa) = []
  xb : V (.inr .xb) = []
  xc : V (.inr .xc) = []
  xd : V (.inr .xd) = []
  xf : V (.inr .xf) = []
  xg : V (.inr .xg) = []
  tmp : V (.inr .tmp) = []

/-- Counter stacks and leaf scratch of the base state. -/
structure BaseOK {LE : Type} (base : KS LE → List Sym) (wI wT q : ℕ) : Prop where
  clean : ∀ e, base (.inr (.inr e)) = []
  cwI : ∃ r, base (.inl .cwI) = natSyms wI ++ r ∧ TermOK r
  cwI2 : ∃ r, base (.inl .cwI2) = natSyms wI ++ r ∧ TermOK r
  cwI1 : ∃ r, base (.inl .cwI1) = natSyms (wI + 1) ++ r ∧ TermOK r
  cwT : ∃ r, base (.inl .cwT) = natSyms wT ++ r ∧ TermOK r
  cwP : ∃ r, base (.inl .cwP) = natSyms (wI + wT + 1) ++ r ∧ TermOK r
  cq : ∃ r, base (.inl .cq) = natSyms q ++ r ∧ TermOK r
  c0 : ∃ r, base (.inl .c0) = natSyms 0 ++ r ∧ TermOK r

section Elem

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]

/-- Leaf scratch of the sweep kernel. -/
abbrev LEs (Ecm Erh Eca : Type) : Type := Ecm ⊕ (Erh ⊕ Eca)

/-- Registers of the sweep kernel. -/
abbrev σs (Rcm Rrh Rca : Type) : Type := Option Sym × (Rcm × (Rrh × Rca))

/-- Programs of the sweep kernel. -/
abbrev PS (Ecm Erh Eca Rcm Rrh Rca : Type) : Type :=
  Prog (KS (LEs Ecm Erh Eca)) (fun _ => Sym) (σs Rcm Rrh Rca)

def lS : Lens (σs Rcm Rrh Rca) (Option Sym) := Lens.fst _ _
def lCM : Lens (σs Rcm Rrh Rca) Rcm := (Lens.snd _ _).comp (Lens.fst _ _)
def lRH : Lens (σs Rcm Rrh Rca) Rrh := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lCA : Lens (σs Rcm Rrh Rca) Rca := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

def iCM : Ecm → LEs Ecm Erh Eca := Sum.inl
def iRH : Erh → LEs Ecm Erh Eca := fun e => Sum.inr (Sum.inl e)
def iCA : Eca → LEs Ecm Erh Eca := fun e => Sum.inr (Sum.inr e)

theorem iCM_inj : Function.Injective (iCM (Ecm := Ecm) (Erh := Erh) (Eca := Eca)) :=
  Sum.inl_injective
theorem iRH_inj : Function.Injective (iRH (Ecm := Ecm) (Erh := Erh) (Eca := Eca)) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
theorem iCA_inj : Function.Injective (iCA (Ecm := Ecm) (Erh := Erh) (Eca := Eca)) :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective h)

/-- The three leaf programs. -/
structure LeafProgs (Ecm Erh Eca Rcm Rrh Rca : Type) where
  Pcm : Prog (KLoc (Fin 7) Ecm) (fun _ => Sym) Rcm
  Prh : Prog (KLoc (Fin 5) Erh) (fun _ => Sym) Rrh
  Pca : Prog (KLoc (Fin 6) Eca) (fun _ => Sym) Rca

variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

def cCM : PS Ecm Erh Eca Rcm Rrh Rca := callInj (ιtab cmTab iCM) lCM G.Pcm
def cRD : PS Ecm Erh Eca Rcm Rrh Rca := callInj (ιtab rhDTab iRH) lRH G.Prh
def cRF : PS Ecm Erh Eca Rcm Rrh Rca := callInj (ιtab rhFTab iRH) lRH G.Prh
def cCA : PS Ecm Erh Eca Rcm Rrh Rca := callInj (ιtab caTab iCA) lCA G.Pca
def MV (x y : SwD ⊕ SwW) : PS Ecm Erh Eca Rcm Rrh Rca := mv lS x y
def CP (x y : SwD ⊕ SwW) : PS Ecm Erh Eca Rcm Rrh Rca := cp lS x y

/-- Prefix step for rows `j ≥ 1`. -/
def e2 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (MV (.inl .dat) (.inr .xa)) (.seq (CP (.inl .mu) (.inr .xb))
  (.seq (MV (.inl .mu) (.inr .muO)) (.seq (cCM G) (.seq (cRD G)
  (.seq (CP (.inr .xd) (.inr .bS)) (.seq (MV (.inr .stI) (.inr .xa))
  (.seq (CP (.inl .na) (.inr .xb)) (.seq (MV (.inl .na) (.inr .naO)) (.seq (cCM G)
  (.seq (cRF G) (.seq (cCA G) (MV (.inr .xg) (.inr .stO)))))))))))))

/-! ## Single-record moves with costs in terms of the width -/

theorem runs_mv1 {LE σ : Type} [DecidableEq LE] (l : Lens σ (Option Sym)) {x y : SwD ⊕ SwW}
    (hxy : x ≠ y) (hx : x ≠ xT) (hy : y ≠ xT) (base : KS LE → List Sym)
    (V : SwD ⊕ SwW → List Sym) {w : ℕ} {c : CInt} {r : List Sym}
    (hV : V x = carrSyms w [[c]] ++ r) (hT : V xT = []) :
    Runs (mv l x y) (mk base V)
      (mk base (Function.update (Function.update V x r) y (carrSyms w [[c]] ++ V y)))
      (fun _ => True) (12 * w + 10) := by
  have h := runs_mv l hxy hx hy base V (crecBits w [c]) r (by rw [hV, carrSyms_one]) hT
  rw [crecBits_one_length, ← carrSyms_one] at h
  refine WP.W9comp.runs_mono h (fun _ _ => trivial) (by omega)

theorem runs_cp1 {LE σ : Type} [DecidableEq LE] (l : Lens σ (Option Sym)) {x y : SwD ⊕ SwW}
    (hxy : x ≠ y) (hx : x ≠ xT) (hy : y ≠ xT) (base : KS LE → List Sym)
    (V : SwD ⊕ SwW → List Sym) {w : ℕ} {c : CInt} {r : List Sym}
    (hV : V x = carrSyms w [[c]] ++ r) :
    Runs (cp l x y) (mk base V) (mk base (Function.update V y (carrSyms w [[c]] ++ V y)))
      (fun _ => True) (14 * w + 8) := by
  have h := runs_cp l hxy hx hy base V (crecBits w [c]) r (by rw [hV, carrSyms_one])
  rw [crecBits_one_length, ← carrSyms_one] at h
  refine WP.W9comp.runs_mono h (fun _ _ => trivial) (by omega)

/-- Cost of the prefix step `e2`. -/
def e2Cost (Ccm Crh Cca wI wT q : ℕ) : ℕ :=
  (12 * wI + 10) + ((14 * wT + 8) + ((12 * wT + 10) + (Ccm * cmCost wI wT +
  (Crh * rhCost (wI + wT + 1) wI q + ((14 * wI + 8) + ((12 * wI + 10) + ((14 * wT + 8) +
  ((12 * wT + 10) + (Ccm * cmCost wI wT + (Crh * rhCost (wI + wT + 1) (wI + 1) q +
  (Cca * caCost wI + (12 * wI + 10))))))))))))

/-- State after the prefix step `e2`. -/
def e2Post (V : SwD ⊕ SwW → List Sym) (wI wT : ℕ) (D Mu Na St : List Sym) (mu na : ℤ)
    (b p' : CInt) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update V (.inl .dat) D) (.inl .mu) Mu)
      (.inl .na) Na) (.inr .stI) St) (.inr .muO) (carrSyms wT [[(mu, 0)]] ++ V (.inr .muO)))
    (.inr .naO) (carrSyms wT [[(na, 0)]] ++ V (.inr .naO)))
    (.inr .stO) (carrSyms wI [[p']] ++ V (.inr .stO))) (.inr .bS) (carrSyms wI [[b]] ++ V (.inr .bS))

theorem runs_e2 {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {wI wT q : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {y p : CInt} {mu na : ℤ} {D Mu Na St : List Sym}
    (hdat : V (.inl .dat) = carrSyms wI [[y]] ++ D)
    (hmu : V (.inl .mu) = carrSyms wT [[(mu, 0)]] ++ Mu)
    (hna : V (.inl .na) = carrSyms wT [[(na, 0)]] ++ Na)
    (hst : V (.inr .stI) = carrSyms wI [[p]] ++ St)
    (fy : Fits2 wI y) (fmu : FitsTwos wT mu) (fna : FitsTwos wT na) (fp : Fits2 wI p)
    (fb : Fits2 wI (bI q mu y)) (fp' : Fits2 wI (stepI q na (bI q mu y) p)) :
    Runs (e2 G) (mk base V)
      (mk base (e2Post V wI wT D Mu Na St mu na (bI q mu y) (stepI q na (bI q mu y) p)))
      (fun _ => True) (e2Cost Ccm Crh Cca wI wT q) := by
  obtain ⟨r1, h1, t1⟩ := hB.cwI
  obtain ⟨r2, h2, t2⟩ := hB.cwI2
  obtain ⟨r3, h3, t3⟩ := hB.cwI1
  obtain ⟨r4, h4, t4⟩ := hB.cwT
  obtain ⟨r5, h5, t5⟩ := hB.cwP
  obtain ⟨r6, h6, t6⟩ := hB.cq
  obtain ⟨r7, h7, t7⟩ := hB.c0
  have hcl1 : ∀ e, base (.inr (.inr (iCM e))) = [] := fun e => hB.clean _
  have hcl2 : ∀ e, base (.inr (.inr (iRH e))) = [] := fun e => hB.clean _
  have hcl3 : ∀ e, base (.inr (.inr (iCA e))) = [] := fun e => hB.clean _
  have fr : Fits2 (wI + 1) (rI q na p) := by
    have hs := fp'
    simp only [stepI, caddC] at hs
    exact ⟨fitsTwos_sub_succ hwI fb.1 hs.1, fitsTwos_sub_succ hwI fb.2 hs.2⟩
  have fP1 := fits_cmul hwI hwT fy fmu
  have fP2 := fits_cmul hwI hwT fp fna
  unfold e2 e2Cost
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .dat) (y := .inr .xa) (by decide) (by decide)
    (by decide) base V hdat hT.tmp) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inl .mu) (y := .inr .xb) (by decide) (by decide)
    (by decide) base _ (c := (mu, 0)) (r := Mu) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hmu])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .mu) (y := .inr .muO) (by decide) (by decide)
    (by decide) base _ (c := (mu, 0)) (r := Mu) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hmu])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cm iCM_inj lCM scm hcl1 hwI hwT h1 h4 h5 h7 t1 t4 t5 t7 _
    (y := y) (m := mu) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xa])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xb]) fy fmu) ?_
  refine WP.W9comp.runs_seq (runs_rhD iRH_inj lRH srh (by omega) hwI h5 h1 h6 t5 t1 t6 _
    (p := cmulTruncC 0 y (mu, 0)) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xc]) fP1 fb) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inr .xd) (y := .inr .bS) (by decide) (by decide)
    (by decide) base _ (c := bI q mu y) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xd, bI])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inr .stI) (y := .inr .xa) (by decide) (by decide)
    (by decide) base _ (c := p) (r := St) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hst])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inl .na) (y := .inr .xb) (by decide) (by decide)
    (by decide) base _ (c := (na, 0)) (r := Na) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hna])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .na) (y := .inr .naO) (by decide) (by decide)
    (by decide) base _ (c := (na, 0)) (r := Na) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hna])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cm iCM_inj lCM scm hcl1 hwI hwT h1 h4 h5 h7 t1 t4 t5 t7 _
    (y := p) (m := na) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xa])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fp fna) ?_
  refine WP.W9comp.runs_seq (runs_rhF iRH_inj lRH srh (wI := wI) (by omega) h5 h3 h6 t5 t3 t6 _
    (p := cmulTruncC 0 p (na, 0)) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fP2 fr) ?_
  refine WP.W9comp.runs_seq (runs_ca iCA_inj lCA sca hwI h1 h3 h2 t1 t3 t2 _ (b := bI q mu y)
    (r := rI q na p) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, bI]) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, rI, hT.xf])
    fb fr fp') ?_
  refine WP.W9comp.runs_congr (runs_mv1 lS (x := .inr .xg) (y := .inr .stO) (by decide) (by decide)
    (by decide) base _ (c := stepI q na (bI q mu y) p) (r := [])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.xg, stepI]) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, hT.tmp])) ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [e2Post, Function.update_apply]
  · cases w <;> simp [e2Post, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg]

/-- First-row prefix step: `y` from `dat`, `μ` from `mu` (recorded on `muO`); pushes
`b = Quant_q(μy)` on `bS` and on `stO` (the state `p_0 = b_0`). -/
def e1 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (MV (.inl .dat) (.inr .xa)) (.seq (CP (.inl .mu) (.inr .xb))
  (.seq (MV (.inl .mu) (.inr .muO)) (.seq (cCM G) (.seq (cRD G)
  (.seq (CP (.inr .xd) (.inr .bS)) (MV (.inr .xd) (.inr .stO)))))))

/-- Cost of `e1`. -/
def e1Cost (Ccm Crh wI wT q : ℕ) : ℕ :=
  (12 * wI + 10) + ((14 * wT + 8) + ((12 * wT + 10) + (Ccm * cmCost wI wT +
  (Crh * rhCost (wI + wT + 1) wI q + ((14 * wI + 8) + (12 * wI + 10))))))

/-- State after `e1`. -/
def e1Post (V : SwD ⊕ SwW → List Sym) (wI wT : ℕ) (D Mu : List Sym) (mu : ℤ) (b : CInt) :
    SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update V
    (.inl .dat) D) (.inl .mu) Mu) (.inr .muO) (carrSyms wT [[(mu, 0)]] ++ V (.inr .muO)))
    (.inr .bS) (carrSyms wI [[b]] ++ V (.inr .bS))) (.inr .stO) (carrSyms wI [[b]] ++ V (.inr .stO))

theorem runs_e1 {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm) (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {wI wT q : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {y : CInt} {mu : ℤ} {D Mu : List Sym}
    (hdat : V (.inl .dat) = carrSyms wI [[y]] ++ D)
    (hmu : V (.inl .mu) = carrSyms wT [[(mu, 0)]] ++ Mu)
    (fy : Fits2 wI y) (fmu : FitsTwos wT mu) (fb : Fits2 wI (bI q mu y)) :
    Runs (e1 G) (mk base V) (mk base (e1Post V wI wT D Mu mu (bI q mu y)))
      (fun _ => True) (e1Cost Ccm Crh wI wT q) := by
  obtain ⟨r1, h1, t1⟩ := hB.cwI
  obtain ⟨r4, h4, t4⟩ := hB.cwT
  obtain ⟨r5, h5, t5⟩ := hB.cwP
  obtain ⟨r6, h6, t6⟩ := hB.cq
  obtain ⟨r7, h7, t7⟩ := hB.c0
  have hcl1 : ∀ e, base (.inr (.inr (iCM e))) = [] := fun e => hB.clean _
  have fP1 := fits_cmul hwI hwT fy fmu
  unfold e1 e1Cost
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .dat) (y := .inr .xa) (by decide) (by decide)
    (by decide) base V hdat hT.tmp) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inl .mu) (y := .inr .xb) (by decide) (by decide)
    (by decide) base _ (c := (mu, 0)) (r := Mu) (by simp [Function.update_apply, hmu])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .mu) (y := .inr .muO) (by decide) (by decide)
    (by decide) base _ (c := (mu, 0)) (r := Mu) (by simp [Function.update_apply, hmu])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cm iCM_inj lCM scm hcl1 hwI hwT h1 h4 h5 h7 t1 t4 t5 t7 _
    (y := y) (m := mu) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fy fmu) ?_
  refine WP.W9comp.runs_seq (runs_rhD iRH_inj lRH srh (by omega) hwI h5 h1 h6 t5 t1 t6 _
    (p := cmulTruncC 0 y (mu, 0)) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fP1 fb) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inr .xd) (y := .inr .bS) (by decide) (by decide)
    (by decide) base _ (c := bI q mu y) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, bI])) ?_
  refine WP.W9comp.runs_congr (runs_mv1 lS (x := .inr .xd) (y := .inr .stO) (by decide) (by decide)
    (by decide) base _ (c := bI q mu y) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, bI])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [e1Post, Function.update_apply]
  · cases w <;> simp [e1Post, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]

/-- Closure step: `p` from `stI`, `γ` from `gm` (recorded on `gmO`); pushes `c = Quant_q(γp)`
on `cS` and on `stO`. -/
def e3 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (MV (.inr .stI) (.inr .xa)) (.seq (CP (.inl .gm) (.inr .xb))
  (.seq (MV (.inl .gm) (.inr .gmO)) (.seq (cCM G) (.seq (cRD G)
  (.seq (CP (.inr .xd) (.inr .cS)) (MV (.inr .xd) (.inr .stO)))))))

/-- State after `e3`. -/
def e3Post (V : SwD ⊕ SwW → List Sym) (wI wT : ℕ) (St Gm : List Sym) (gm : ℤ) (c : CInt) :
    SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update V
    (.inr .stI) St) (.inl .gm) Gm) (.inr .gmO) (carrSyms wT [[(gm, 0)]] ++ V (.inr .gmO)))
    (.inr .cS) (carrSyms wI [[c]] ++ V (.inr .cS))) (.inr .stO) (carrSyms wI [[c]] ++ V (.inr .stO))

theorem runs_e3 {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm) (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {wI wT q : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {p : CInt} {gm : ℤ} {St Gm : List Sym}
    (hst : V (.inr .stI) = carrSyms wI [[p]] ++ St)
    (hgm : V (.inl .gm) = carrSyms wT [[(gm, 0)]] ++ Gm)
    (fp : Fits2 wI p) (fgm : FitsTwos wT gm) (fc : Fits2 wI (rI q gm p)) :
    Runs (e3 G) (mk base V) (mk base (e3Post V wI wT St Gm gm (rI q gm p)))
      (fun _ => True) (e1Cost Ccm Crh wI wT q) := by
  obtain ⟨r1, h1, t1⟩ := hB.cwI
  obtain ⟨r4, h4, t4⟩ := hB.cwT
  obtain ⟨r5, h5, t5⟩ := hB.cwP
  obtain ⟨r6, h6, t6⟩ := hB.cq
  obtain ⟨r7, h7, t7⟩ := hB.c0
  have hcl1 : ∀ e, base (.inr (.inr (iCM e))) = [] := fun e => hB.clean _
  have fP1 := fits_cmul hwI hwT fp fgm
  unfold e3 e1Cost
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inr .stI) (y := .inr .xa) (by decide) (by decide)
    (by decide) base V hst hT.tmp) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inl .gm) (y := .inr .xb) (by decide) (by decide)
    (by decide) base _ (c := (gm, 0)) (r := Gm) (by simp [Function.update_apply, hgm])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .gm) (y := .inr .gmO) (by decide) (by decide)
    (by decide) base _ (c := (gm, 0)) (r := Gm) (by simp [Function.update_apply, hgm])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cm iCM_inj lCM scm hcl1 hwI hwT h1 h4 h5 h7 t1 t4 t5 t7 _
    (y := p) (m := gm) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fp fgm) ?_
  refine WP.W9comp.runs_seq (runs_rhD iRH_inj lRH srh (by omega) hwI h5 h1 h6 t5 t1 t6 _
    (p := cmulTruncC 0 p (gm, 0)) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fP1 fc) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inr .xd) (y := .inr .cS) (by decide) (by decide)
    (by decide) base _ (c := rI q gm p) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, rI])) ?_
  refine WP.W9comp.runs_congr (runs_mv1 lS (x := .inr .xd) (y := .inr .stO) (by decide) (by decide)
    (by decide) base _ (c := rI q gm p) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, rI])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [e3Post, Function.update_apply]
  · cases w <;> simp [e3Post, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]

/-- Second-pass step: `b` from `bS2`, `p` from `stI`, `-â` from `na` (recorded on `naO`); pushes
`z = b + Quant_q(-â p)` on `oS` and on `stO`. -/
def e4 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (MV (.inr .bS2) (.inr .xd)) (.seq (MV (.inr .stI) (.inr .xa))
  (.seq (CP (.inl .na) (.inr .xb)) (.seq (MV (.inl .na) (.inr .naO)) (.seq (cCM G)
  (.seq (cRF G) (.seq (cCA G) (.seq (CP (.inr .xg) (.inr .oS)) (MV (.inr .xg) (.inr .stO)))))))))

/-- Cost of `e4`. -/
def e4Cost (Ccm Crh Cca wI wT q : ℕ) : ℕ :=
  (12 * wI + 10) + ((12 * wI + 10) + ((14 * wT + 8) + ((12 * wT + 10) + (Ccm * cmCost wI wT +
  (Crh * rhCost (wI + wT + 1) (wI + 1) q + (Cca * caCost wI + ((14 * wI + 8) +
  (12 * wI + 10))))))))

/-- State after `e4`. -/
def e4Post (V : SwD ⊕ SwW → List Sym) (wI wT : ℕ) (B2 St Na : List Sym) (na : ℤ) (z : CInt) :
    SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update V (.inr .bS2) B2) (.inr .stI) St) (.inl .na) Na)
    (.inr .naO) (carrSyms wT [[(na, 0)]] ++ V (.inr .naO)))
    (.inr .oS) (carrSyms wI [[z]] ++ V (.inr .oS))) (.inr .stO) (carrSyms wI [[z]] ++ V (.inr .stO))

theorem runs_e4 {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {wI wT q : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {b p : CInt} {na : ℤ} {B2 St Na : List Sym}
    (hb2 : V (.inr .bS2) = carrSyms wI [[b]] ++ B2)
    (hst : V (.inr .stI) = carrSyms wI [[p]] ++ St)
    (hna : V (.inl .na) = carrSyms wT [[(na, 0)]] ++ Na)
    (fb : Fits2 wI b) (fna : FitsTwos wT na) (fp : Fits2 wI p) (fz : Fits2 wI (stepI q na b p)) :
    Runs (e4 G) (mk base V) (mk base (e4Post V wI wT B2 St Na na (stepI q na b p)))
      (fun _ => True) (e4Cost Ccm Crh Cca wI wT q) := by
  obtain ⟨r1, h1, t1⟩ := hB.cwI
  obtain ⟨r2, h2, t2⟩ := hB.cwI2
  obtain ⟨r3, h3, t3⟩ := hB.cwI1
  obtain ⟨r4, h4, t4⟩ := hB.cwT
  obtain ⟨r5, h5, t5⟩ := hB.cwP
  obtain ⟨r6, h6, t6⟩ := hB.cq
  obtain ⟨r7, h7, t7⟩ := hB.c0
  have hcl1 : ∀ e, base (.inr (.inr (iCM e))) = [] := fun e => hB.clean _
  have fr : Fits2 (wI + 1) (rI q na p) := by
    have hs := fz
    simp only [stepI, caddC] at hs
    exact ⟨fitsTwos_sub_succ hwI fb.1 hs.1, fitsTwos_sub_succ hwI fb.2 hs.2⟩
  have fP2 := fits_cmul hwI hwT fp fna
  unfold e4 e4Cost
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inr .bS2) (y := .inr .xd) (by decide) (by decide)
    (by decide) base V hb2 hT.tmp) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inr .stI) (y := .inr .xa) (by decide) (by decide)
    (by decide) base _ (c := p) (r := St) (by simp [Function.update_apply, hst])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inl .na) (y := .inr .xb) (by decide) (by decide)
    (by decide) base _ (c := (na, 0)) (r := Na) (by simp [Function.update_apply, hna])) ?_
  refine WP.W9comp.runs_seq (runs_mv1 lS (x := .inl .na) (y := .inr .naO) (by decide) (by decide)
    (by decide) base _ (c := (na, 0)) (r := Na) (by simp [Function.update_apply, hna])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  refine WP.W9comp.runs_seq (runs_cm iCM_inj lCM scm hcl1 hwI hwT h1 h4 h5 h7 t1 t4 t5 t7 _
    (y := p) (m := na) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fp fna) ?_
  refine WP.W9comp.runs_seq (runs_rhF iRH_inj lRH srh (wI := wI) (by omega) h5 h3 h6 t5 t3 t6 _
    (p := cmulTruncC 0 p (na, 0)) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) fP2 fr) ?_
  refine WP.W9comp.runs_seq (runs_ca iCA_inj lCA sca hwI h1 h3 h2 t1 t3 t2 _ (b := b)
    (r := rI q na p) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, rI])
    fb fr fz) ?_
  refine WP.W9comp.runs_seq (runs_cp1 lS (x := .inr .xg) (y := .inr .oS) (by decide) (by decide)
    (by decide) base _ (c := stepI q na b p) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, stepI]))
    ?_
  refine WP.W9comp.runs_congr (runs_mv1 lS (x := .inr .xg) (y := .inr .stO) (by decide) (by decide)
    (by decide) base _ (c := stepI q na b p) (r := []) (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp, stepI])
    (by simp [Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp])) ?_
  congr 1
  funext x
  rcases x with d | w
  · cases d <;> simp [e4Post, Function.update_apply]
  · cases w <;> simp [e4Post, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg, hT.tmp]

end Elem

end SubNLogN.Machine.Bridge.SolveAux
