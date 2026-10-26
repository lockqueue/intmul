/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelScanDefs

/-!
# C-core phase leaf, record-wise sign selection: the select loop (`LeafPhaseMaskSelScan.lean`)

**Scope (honest summary).** Proves `MaskScanAux.selLoop_holds : PhaseMaskAux.SelLoopStmt`
(`CCore/LeafPhaseMaskSelScanDefs.lean`). No hypotheses beyond
the statement's own.

The proof runs `runs_whileT` over the pairs `v.zip vn`. The loop invariant `scanSt` is the
seven-stack state `mk7` after `i` records:
* `V`, `Vn` hold the remaining records;
* `Out` holds `selOut G S done`;
* `Tb`/`Gu` hold the drop/take of `G` at `q = (i/S) mod |G|`;
* `Sc`/`Su` hold `S - i mod S` / `i mod S` zero bits.

One iteration (`runs_body`) is the selection phase `runs_selA` followed by the counter phase
`runs_selB`, which covers the three cases: no refill, refill, and refill with a table reset.
The step cost depends on `i`; the total is bounded with the potential
`Phi i = 3·(i mod S) + 7·((i/S) mod |G|)` (`step_amort`, `whileCost_amort`).

Helpers are in the namespace `SubNLogN.Machine.CCore.MaskScanAux`.
-/

namespace SubNLogN.Machine.CCore.MaskScanAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
open SubNLogN.Machine.CCore.PhaseMaskAux

/-! ## Arithmetic of the counters -/

theorem mod_succ_lt {i S : ℕ} (hS : 0 < S) (h : i % S + 1 < S) :
    (i + 1) % S = i % S + 1 ∧ (i + 1) / S = i / S := by
  have h1 : (i + 1) % S = i % S + 1 := by
    rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt h]
  refine ⟨h1, ?_⟩
  have e1 := Nat.div_add_mod i S
  have e2 := Nat.div_add_mod (i + 1) S
  rw [h1] at e2
  apply Nat.eq_of_mul_eq_mul_left hS
  omega

theorem mod_succ_eq {i S : ℕ} (hS : 0 < S) (h : i % S + 1 = S) :
    (i + 1) % S = 0 ∧ (i + 1) / S = i / S + 1 := by
  have h1 : (i + 1) % S = 0 := by
    rw [← Nat.mod_add_mod, h, Nat.mod_self]
  refine ⟨h1, ?_⟩
  have e1 := Nat.div_add_mod i S
  have e2 := Nat.div_add_mod (i + 1) S
  rw [h1] at e2
  apply Nat.eq_of_mul_eq_mul_left hS
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## Seven-stack states -/

section States

variable {K : Type} [DecidableEq K]

theorem d7 {V Vn Out Tb Gu Sc Su : K} (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    V ≠ Vn ∧ V ≠ Out ∧ V ≠ Tb ∧ V ≠ Gu ∧ V ≠ Sc ∧ V ≠ Su ∧ Vn ≠ Out ∧ Vn ≠ Tb ∧ Vn ≠ Gu ∧
    Vn ≠ Sc ∧ Vn ≠ Su ∧ Out ≠ Tb ∧ Out ≠ Gu ∧ Out ≠ Sc ∧ Out ≠ Su ∧ Tb ≠ Gu ∧ Tb ≠ Sc ∧
    Tb ≠ Su ∧ Gu ≠ Sc ∧ Gu ≠ Su ∧ Sc ≠ Su := by
  have h0 := List.pairwise_cons.mp hd
  have h1 := List.pairwise_cons.mp h0.2
  have h2 := List.pairwise_cons.mp h1.2
  have h3 := List.pairwise_cons.mp h2.2
  have h4 := List.pairwise_cons.mp h3.2
  have h5 := List.pairwise_cons.mp h4.2
  exact ⟨h0.1 _ (by simp), h0.1 _ (by simp), h0.1 _ (by simp), h0.1 _ (by simp),
    h0.1 _ (by simp), h0.1 _ (by simp), h1.1 _ (by simp), h1.1 _ (by simp), h1.1 _ (by simp),
    h1.1 _ (by simp), h1.1 _ (by simp), h2.1 _ (by simp), h2.1 _ (by simp), h2.1 _ (by simp),
    h2.1 _ (by simp), h3.1 _ (by simp), h3.1 _ (by simp), h3.1 _ (by simp), h4.1 _ (by simp),
    h4.1 _ (by simp), h5.1 _ (by simp)⟩

/-- The state with the seven loop stacks set on top of `St`. -/
def mk7 (V Vn Out Tb Gu Sc Su : K) (St : K → List Sym) (a b c d e f g : List Sym) :
    K → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update St V a) Vn b) Out c) Tb d) Gu e) Sc f) Su g

variable {V Vn Out Tb Gu Sc Su : K} {St : K → List Sym} {a b c d e f g : List Sym}

theorem mk7_V (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g V = a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := d7 hd
  simp [mk7, Function.update_apply, h1, h2, h3, h4, h5, h6]

theorem mk7_Vn (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Vn = b := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, -⟩ := d7 hd
  simp [mk7, Function.update_apply, h7, h8, h9, h10, h11]

theorem mk7_Out (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Out = c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13, h14, h15, -⟩ := d7 hd
  simp [mk7, Function.update_apply, h12, h13, h14, h15]

theorem mk7_Tb (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Tb = d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, h18, -⟩ := d7 hd
  simp [mk7, Function.update_apply, h16, h17, h18]

theorem mk7_Gu (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Gu = e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, h20, -⟩ := d7 hd
  simp [mk7, Function.update_apply, h19, h20]

theorem mk7_Sc (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) :
    mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Sc = f := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21⟩ := d7 hd
  simp [mk7, Function.update_apply, h21]

theorem mk7_Su : mk7 V Vn Out Tb Gu Sc Su St a b c d e f g Su = g := by
  simp [mk7]

theorem mk7_upd_V (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) V x =
      mk7 V Vn Out Tb Gu Sc Su St x b c d e f g := by
  funext k
  by_cases hk : k = V
  · rw [hk, Function.update_self, mk7_V hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Vn (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Vn x =
      mk7 V Vn Out Tb Gu Sc Su St a x c d e f g := by
  funext k
  by_cases hk : k = Vn
  · rw [hk, Function.update_self, mk7_Vn hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Out (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Out x =
      mk7 V Vn Out Tb Gu Sc Su St a b x d e f g := by
  funext k
  by_cases hk : k = Out
  · rw [hk, Function.update_self, mk7_Out hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Tb (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Tb x =
      mk7 V Vn Out Tb Gu Sc Su St a b c x e f g := by
  funext k
  by_cases hk : k = Tb
  · rw [hk, Function.update_self, mk7_Tb hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Gu (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Gu x =
      mk7 V Vn Out Tb Gu Sc Su St a b c d x f g := by
  funext k
  by_cases hk : k = Gu
  · rw [hk, Function.update_self, mk7_Gu hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Sc (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Sc x =
      mk7 V Vn Out Tb Gu Sc Su St a b c d e x g := by
  funext k
  by_cases hk : k = Sc
  · rw [hk, Function.update_self, mk7_Sc hd]
  · rw [Function.update_of_ne hk]
    simp [mk7, Function.update_apply, hk]

theorem mk7_upd_Su (x : List Sym) :
    Function.update (mk7 V Vn Out Tb Gu Sc Su St a b c d e f g) Su x =
      mk7 V Vn Out Tb Gu Sc Su St a b c d e f x := by
  simp [mk7]

theorem mk7_self :
    mk7 V Vn Out Tb Gu Sc Su St (St V) (St Vn) (St Out) (St Tb) (St Gu) (St Sc) (St Su) = St := by
  simp [mk7]

end States

/-! ## Record and table helpers -/

theorem arrSyms_cons_msa (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := rfl

theorem arrSyms_nil_msa : arrSyms ([] : List (List Bool)) = [] := rfl

theorem vol_cons_msa (p : List Bool) (v : List (List Bool)) :
    (arrSyms (p :: v)).length = p.length + 1 + (arrSyms v).length := by
  simp [arrSyms_cons_msa, recSyms]
  omega

theorem take_succ_rev {G : List Bool} {q : ℕ} (hq : q < G.length) :
    (G.take (q + 1)).reverse.map Sym.bit = Sym.bit G[q] :: (G.take q).reverse.map Sym.bit := by
  have h : G.take (q + 1) = G.take q ++ [G[q]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hq]
    rfl
  rw [h, List.reverse_append]
  rfl

theorem drop_cons_map {G : List Bool} {q : ℕ} (hq : q < G.length) :
    (G.drop q).map Sym.bit = Sym.bit G[q] :: (G.drop (q + 1)).map Sym.bit := by
  rw [List.drop_eq_getElem_cons hq]
  rfl

theorem selOut_snoc (G : List Bool) (S : ℕ) (done : List (List Bool × List Bool))
    (x : List Bool × List Bool) :
    selOut G S (done ++ [x]) = Sym.sep :: ((if G.getD ((done.length / S) % G.length) false
      then x.2 else x.1).reverse.map Sym.bit ++ selOut G S done) := by
  simp [selOut, List.mapIdx_append]

theorem selOut_nil (G : List Bool) (S : ℕ) : selOut G S [] = [] := by
  simp [selOut]

/-! ## Generic glue -/

theorem runs_fix {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S' S'' : K → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hS : S' = S'')
    (hT : T ≤ T') : Runs P S S'' (fun _ => True) T' :=
  WP.W9comp.runs_mono (WP.W9comp.runs_congr h hS) (fun _ _ => trivial) hT

theorem runs_peek_f {K : Type} [DecidableEq K] (f : Option Sym → Bool) (k : K)
    (M : K → List Sym) (b : Bool) (h : f (M k).head? = b) :
    Runs (peekT k) M M (fun v => f v.t = b) 1 :=
  WP.W9comp.runs_mono (runs_peekT k M) (fun v hv => by rw [hv]; exact h) le_rfl

/-! ## The two phases of `selBody` -/

section Phases

variable {K : Type}

/-- Phase A of `selBody`: select the record by the table entry on top of `Tb`. -/
def selA (V Vn Out Tb : K) : PProg K :=
  .seq (peekT Tb) (.ite (fun v => bitOf v.t)
    (.seq (msMvRec Vn Out) (msDropRec V)) (.seq (msMvRec V Out) (msDropRec Vn)))

/-- The refill branch of phase B. -/
def selR (Tb Gu Sc Su : K) : PProg K :=
  .seq (msLift (moveBlock Su Sc))
    (.seq (msLift (moveSym Tb Gu))
      (.seq (peekT Tb) (.ite (fun v => isBitO v.t) msSkip (msLift (moveBlock Gu Tb)))))

/-- Phase B of `selBody`: advance the unary counter (and the table on a refill). -/
def selB (Tb Gu Sc Su : K) : PProg K :=
  .seq (msLift (moveSym Sc Su))
    (.seq (peekT Sc) (.ite (fun v => isBitO v.t) msSkip (selR Tb Gu Sc Su)))

theorem selBody_eq (V Vn Out Tb Gu Sc Su : K) :
    selBody V Vn Out Tb Gu Sc Su = .seq (selA V Vn Out Tb) (selB Tb Gu Sc Su) := rfl

/-- Extra cost of phase B at record `i`: `1`, or a refill (`3S + 8`) plus a possible table reset. -/
def T2c (G : List Bool) (S i : ℕ) : ℕ :=
  if i % S + 1 = S then
    3 * S + 8 + (if (i / S) % G.length + 1 = G.length then 3 * G.length + 4 else 1)
  else 1

variable [DecidableEq K] {V Vn Out Tb Gu Sc Su : K} {St : K → List Sym}

theorem runs_selA (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) (a b : List Bool)
    (AR BR C D E F Gs : List Sym) (g : Bool) (DR : List Sym) (hD : D = Sym.bit g :: DR) :
    Runs (selA V Vn Out Tb)
      (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) (recSyms b ++ BR) C D E F Gs)
      (mk7 V Vn Out Tb Gu Sc Su St AR BR
        (Sym.sep :: ((if g then b else a).reverse.map Sym.bit ++ C)) D E F Gs)
      (fun _ => True) (3 * a.length + 3 * b.length + 11) := by
  obtain ⟨-, h2, -, -, -, -, h7, -⟩ := d7 hd
  have hpk := runs_peek_f bitOf Tb
    (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) (recSyms b ++ BR) C D E F Gs) g
    (by rw [mk7_Tb hd, hD]; rfl)
  refine runs_fix (runs_seq_ite (Q := fun _ => True) (T2 := 3 * a.length + 3 * b.length + 9) hpk
    (fun hg => ?_) (fun hg => ?_)) rfl (by omega)
  · rw [if_pos hg]
    have r1 : Runs (msMvRec Vn Out)
        (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) (recSyms b ++ BR) C D E F Gs)
        (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) BR
          (Sym.sep :: (b.reverse.map Sym.bit ++ C)) D E F Gs) (fun _ => True) (3 * b.length + 6) :=
      runs_fix (runs_msMvRec h7 b BR _ (mk7_Vn hd))
        (by rw [mk7_upd_Vn hd, mk7_Out hd, mk7_upd_Out hd]) le_rfl
    have r2 : Runs (msDropRec V)
        (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) BR
          (Sym.sep :: (b.reverse.map Sym.bit ++ C)) D E F Gs)
        (mk7 V Vn Out Tb Gu Sc Su St AR BR
          (Sym.sep :: (b.reverse.map Sym.bit ++ C)) D E F Gs) (fun _ => True) (3 * a.length + 3) :=
      runs_fix (runs_msDropRec a AR _ (mk7_V hd)) (by rw [mk7_upd_V hd]) le_rfl
    exact runs_fix (WP.W9comp.runs_seq r1 r2) rfl (by omega)
  · rw [if_neg (by rw [hg]; decide)]
    have r1 : Runs (msMvRec V Out)
        (mk7 V Vn Out Tb Gu Sc Su St (recSyms a ++ AR) (recSyms b ++ BR) C D E F Gs)
        (mk7 V Vn Out Tb Gu Sc Su St AR (recSyms b ++ BR)
          (Sym.sep :: (a.reverse.map Sym.bit ++ C)) D E F Gs) (fun _ => True) (3 * a.length + 6) :=
      runs_fix (runs_msMvRec h2 a AR _ (mk7_V hd))
        (by rw [mk7_upd_V hd, mk7_Out hd, mk7_upd_Out hd]) le_rfl
    have r2 : Runs (msDropRec Vn)
        (mk7 V Vn Out Tb Gu Sc Su St AR (recSyms b ++ BR)
          (Sym.sep :: (a.reverse.map Sym.bit ++ C)) D E F Gs)
        (mk7 V Vn Out Tb Gu Sc Su St AR BR
          (Sym.sep :: (a.reverse.map Sym.bit ++ C)) D E F Gs) (fun _ => True) (3 * b.length + 3) :=
      runs_fix (runs_msDropRec b BR _ (mk7_Vn hd)) (by rw [mk7_upd_Vn hd]) le_rfl
    exact runs_fix (WP.W9comp.runs_seq r1 r2) rfl (by omega)

theorem runs_selR (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) {G : List Bool}
    (A B C : List Sym) (q n : ℕ) (hq : q < G.length) :
    Runs (selR Tb Gu Sc Su)
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop q).map Sym.bit) ((G.take q).reverse.map Sym.bit)
        [] (List.replicate n (Sym.bit false)))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((q + 1) % G.length)).map Sym.bit)
        ((G.take ((q + 1) % G.length)).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) [])
      (fun _ => True) (3 * n + 8 + (if q + 1 = G.length then 3 * G.length + 4 else 1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, -, -, -, -, h21⟩ := d7 hd
  have r1 : Runs (msLift (moveBlock Su Sc))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop q).map Sym.bit) ((G.take q).reverse.map Sym.bit)
        [] (List.replicate n (Sym.bit false)))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop q).map Sym.bit) ((G.take q).reverse.map Sym.bit)
        (List.replicate n (Sym.bit false)) [])
      (fun _ => True) (3 * n + 4) :=
    runs_fix (runs_liftRegs lensPO (runs_moveBlock (Ne.symm h21) (List.replicate n false) [] _
      TermOK.nil (by rw [mk7_Su]; simp)))
      (by rw [mk7_upd_Su, mk7_Sc hd, mk7_upd_Sc hd]; simp) (by simp)
  have r2 : Runs (msLift (moveSym Tb Gu))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop q).map Sym.bit) ((G.take q).reverse.map Sym.bit)
        (List.replicate n (Sym.bit false)) [])
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop (q + 1)).map Sym.bit)
        ((G.take (q + 1)).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) [])
      (fun _ => True) 2 :=
    runs_fix (runs_liftRegs lensPO (runs_moveSym h16 (Sym.bit G[q]) ((G.drop (q + 1)).map Sym.bit)
      _ (by rw [mk7_Tb hd, drop_cons_map hq])))
      (by rw [mk7_upd_Tb hd, mk7_Gu hd, mk7_upd_Gu hd, take_succ_rev hq]) le_rfl
  by_cases hlast : q + 1 = G.length
  · have e0 : (q + 1) % G.length = 0 := by rw [hlast, Nat.mod_self]
    rw [e0, if_pos hlast]
    have hD : (G.drop (q + 1)).map Sym.bit = [] := by rw [hlast]; simp
    have hT : (G.take (q + 1)).reverse.map Sym.bit = G.reverse.map Sym.bit ++ [] := by
      rw [hlast, List.take_length]; simp
    have r3 := runs_peek_f isBitO Tb
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop (q + 1)).map Sym.bit)
        ((G.take (q + 1)).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) []) false
      (by rw [mk7_Tb hd, hD]; rfl)
    have r4 : Runs (msLift (moveBlock Gu Tb))
        (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop (q + 1)).map Sym.bit)
          ((G.take (q + 1)).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) [])
        (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop 0).map Sym.bit)
          ((G.take 0).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) [])
        (fun _ => True) (3 * G.length + 4) :=
      runs_fix (runs_liftRegs lensPO (runs_moveBlock (Ne.symm h16) G.reverse [] _ TermOK.nil
        (by rw [mk7_Gu hd, hT])))
        (by rw [mk7_upd_Gu hd, mk7_Tb hd, mk7_upd_Tb hd, hD]; simp) (by simp)
    have r34 := runs_seq_ite (A := msSkip) (Q := fun _ => True) r3 (fun h => absurd h (by decide))
      (fun _ => r4)
    exact runs_fix (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r34)) rfl (by omega)
  · have hlt : q + 1 < G.length := by omega
    have e0 : (q + 1) % G.length = q + 1 := Nat.mod_eq_of_lt hlt
    rw [e0, if_neg hlast]
    have r3 := runs_peek_f isBitO Tb
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop (q + 1)).map Sym.bit)
        ((G.take (q + 1)).reverse.map Sym.bit) (List.replicate n (Sym.bit false)) []) true
      (by rw [mk7_Tb hd, drop_cons_map hlt]; rfl)
    have r34 := runs_seq_ite (A' := msLift (moveBlock Gu Tb)) (Q := fun _ => True) r3
      (fun _ => runs_msSkip _) (fun h => absurd h (by decide))
    exact runs_fix (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r34)) rfl (by omega)

theorem runs_selB (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) {G : List Bool}
    {S : ℕ} (hG : 0 < G.length) (hS : 0 < S) (A B C : List Sym) (i : ℕ) :
    Runs (selB Tb Gu Sc Su)
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((i / S) % G.length)).map Sym.bit)
        ((G.take ((i / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - i % S) (Sym.bit false)) (List.replicate (i % S) (Sym.bit false)))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop (((i + 1) / S) % G.length)).map Sym.bit)
        ((G.take (((i + 1) / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - (i + 1) % S) (Sym.bit false))
        (List.replicate ((i + 1) % S) (Sym.bit false)))
      (fun _ => True) (T2c G S i + 4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21⟩ := d7 hd
  have hr := Nat.mod_lt i hS
  have hq := Nat.mod_lt (i / S) hG
  have eSc : List.replicate (S - i % S) (Sym.bit false) =
      Sym.bit false :: List.replicate (S - i % S - 1) (Sym.bit false) := by
    rw [← List.replicate_succ, Nat.sub_add_cancel (by omega : 1 ≤ S - i % S)]
  have r1 : Runs (msLift (moveSym Sc Su))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((i / S) % G.length)).map Sym.bit)
        ((G.take ((i / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - i % S) (Sym.bit false)) (List.replicate (i % S) (Sym.bit false)))
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((i / S) % G.length)).map Sym.bit)
        ((G.take ((i / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - i % S - 1) (Sym.bit false))
        (List.replicate (i % S + 1) (Sym.bit false)))
      (fun _ => True) 2 :=
    runs_fix (runs_liftRegs lensPO (runs_moveSym h21 (Sym.bit false)
      (List.replicate (S - i % S - 1) (Sym.bit false)) _ (by rw [mk7_Sc hd, eSc])))
      (by rw [mk7_upd_Sc hd, mk7_Su, mk7_upd_Su, List.replicate_succ]) le_rfl
  rcases Nat.lt_or_ge (i % S + 1) S with h | h
  · obtain ⟨h1, h2⟩ := mod_succ_lt hS h
    rw [h1, h2]
    have hT2 : T2c G S i = 1 := by unfold T2c; rw [if_neg (by omega)]
    rw [hT2]
    have r2 := runs_peek_f isBitO Sc
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((i / S) % G.length)).map Sym.bit)
        ((G.take ((i / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - i % S - 1) (Sym.bit false))
        (List.replicate (i % S + 1) (Sym.bit false))) true
      (by
        rw [mk7_Sc hd, ← Nat.sub_add_cancel (by omega : 1 ≤ S - i % S - 1), List.replicate_succ]
        rfl)
    have r23 := runs_seq_ite (A' := selR Tb Gu Sc Su) (Q := fun _ => True) r2
      (fun _ => runs_msSkip _) (fun h => absurd h (by decide))
    exact runs_fix (WP.W9comp.runs_seq r1 r23) (by rw [Nat.sub_sub]) (by omega)
  · have h' : i % S + 1 = S := by omega
    obtain ⟨h1, h2⟩ := mod_succ_eq hS h'
    rw [h1, h2, ← Nat.mod_add_mod (i / S) G.length 1, Nat.sub_zero, List.replicate_zero]
    have hT2 : T2c G S i = 3 * S + 8 +
        (if (i / S) % G.length + 1 = G.length then 3 * G.length + 4 else 1) := by
      unfold T2c; rw [if_pos h']
    rw [hT2]
    have e1 : S - i % S - 1 = 0 := by omega
    rw [e1, h', List.replicate_zero] at r1
    have r2 := runs_peek_f isBitO Sc
      (mk7 V Vn Out Tb Gu Sc Su St A B C ((G.drop ((i / S) % G.length)).map Sym.bit)
        ((G.take ((i / S) % G.length)).reverse.map Sym.bit) [] (List.replicate S (Sym.bit false)))
      false (by rw [mk7_Sc hd]; rfl)
    have r3 := runs_selR (St := St) hd A B C ((i / S) % G.length) S hq
    have r23 := runs_seq_ite (A := msSkip) (Q := fun _ => True) r2 (fun h => absurd h (by decide))
      (fun _ => r3)
    exact runs_fix (WP.W9comp.runs_seq r1 r23) rfl (by omega)

end Phases

/-! ## The loop invariant -/

section Loop

variable {K : Type} [DecidableEq K] {V Vn Out Tb Gu Sc Su : K}

/-- The state of the select loop after the records `done`, with `rest` still to do. -/
noncomputable def scanSt (V Vn Out Tb Gu Sc Su : K) (G : List Bool) (S : ℕ) (rx rxn : List Sym)
    (St : K → List Sym) (done rest : List (List Bool × List Bool)) : K → List Sym :=
  mk7 V Vn Out Tb Gu Sc Su St (arrSyms (rest.map Prod.fst) ++ rx)
    (arrSyms (rest.map Prod.snd) ++ rxn) (selOut G S done)
    ((G.drop ((done.length / S) % G.length)).map Sym.bit)
    ((G.take ((done.length / S) % G.length)).reverse.map Sym.bit)
    (List.replicate (S - done.length % S) (Sym.bit false))
    (List.replicate (done.length % S) (Sym.bit false))

/-- Cost of iteration `done.length` (record `x`). -/
def costFn (G : List Bool) (S : ℕ) (done : List (List Bool × List Bool))
    (x : List Bool × List Bool) (_rest : List (List Bool × List Bool)) : ℕ :=
  3 * x.1.length + 3 * x.2.length + 15 + T2c G S done.length

theorem runs_body (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) {G : List Bool}
    {S : ℕ} (hG : 0 < G.length) (hS : 0 < S) (rx rxn : List Sym) (St : K → List Sym)
    (done : List (List Bool × List Bool)) (x : List Bool × List Bool)
    (rest : List (List Bool × List Bool)) :
    Runs (selBody V Vn Out Tb Gu Sc Su) (scanSt V Vn Out Tb Gu Sc Su G S rx rxn St done (x :: rest))
      (scanSt V Vn Out Tb Gu Sc Su G S rx rxn St (done ++ [x]) rest) (fun _ => True)
      (costFn G S done x rest) := by
  have hq := Nat.mod_lt (done.length / S) hG
  have hg : G.getD ((done.length / S) % G.length) false = G[(done.length / S) % G.length] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    rfl
  have e1 : scanSt V Vn Out Tb Gu Sc Su G S rx rxn St done (x :: rest) =
      mk7 V Vn Out Tb Gu Sc Su St (recSyms x.1 ++ (arrSyms (rest.map Prod.fst) ++ rx))
        (recSyms x.2 ++ (arrSyms (rest.map Prod.snd) ++ rxn)) (selOut G S done)
        ((G.drop ((done.length / S) % G.length)).map Sym.bit)
        ((G.take ((done.length / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - done.length % S) (Sym.bit false))
        (List.replicate (done.length % S) (Sym.bit false)) := by
    rw [scanSt, List.map_cons, List.map_cons, arrSyms_cons_msa, arrSyms_cons_msa,
      List.append_assoc, List.append_assoc]
  have e2 : scanSt V Vn Out Tb Gu Sc Su G S rx rxn St (done ++ [x]) rest =
      mk7 V Vn Out Tb Gu Sc Su St (arrSyms (rest.map Prod.fst) ++ rx)
        (arrSyms (rest.map Prod.snd) ++ rxn)
        (Sym.sep :: ((if G[(done.length / S) % G.length] then x.2 else x.1).reverse.map Sym.bit ++
          selOut G S done))
        ((G.drop (((done.length + 1) / S) % G.length)).map Sym.bit)
        ((G.take (((done.length + 1) / S) % G.length)).reverse.map Sym.bit)
        (List.replicate (S - (done.length + 1) % S) (Sym.bit false))
        (List.replicate ((done.length + 1) % S) (Sym.bit false)) := by
    rw [scanSt, selOut_snoc, hg, List.length_append, List.length_singleton]
  rw [e1, e2, selBody_eq]
  have rA := runs_selA (St := St) (Gu := Gu) (Sc := Sc) (Su := Su) hd x.1 x.2
    (arrSyms (rest.map Prod.fst) ++ rx) (arrSyms (rest.map Prod.snd) ++ rxn) (selOut G S done)
    ((G.drop ((done.length / S) % G.length)).map Sym.bit)
    ((G.take ((done.length / S) % G.length)).reverse.map Sym.bit)
    (List.replicate (S - done.length % S) (Sym.bit false))
    (List.replicate (done.length % S) (Sym.bit false)) G[(done.length / S) % G.length]
    ((G.drop ((done.length / S) % G.length + 1)).map Sym.bit) (drop_cons_map hq)
  have rB := runs_selB (St := St) (V := V) (Vn := Vn) (Out := Out) hd hG hS
    (arrSyms (rest.map Prod.fst) ++ rx) (arrSyms (rest.map Prod.snd) ++ rxn)
    (Sym.sep :: ((if G[(done.length / S) % G.length] then x.2 else x.1).reverse.map Sym.bit ++
      selOut G S done)) done.length
  exact runs_fix (WP.W9comp.runs_seq rA rB) rfl (by unfold costFn; omega)

theorem runs_hpk (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) {G : List Bool}
    {S : ℕ} {rx : List Sym} (hrx : BlkTerm rx) (rxn : List Sym) (St : K → List Sym)
    (done rest : List (List Bool × List Bool)) :
    Runs (peekT V) (scanSt V Vn Out Tb Gu Sc Su G S rx rxn St done rest)
      (scanSt V Vn Out Tb Gu Sc Su G S rx rxn St done rest)
      (fun v => isRecO v.t = !rest.isEmpty) 1 := by
  apply runs_peek_f isRecO V
  rw [scanSt, mk7_V hd]
  rcases rest with _ | ⟨⟨p, p'⟩, rest⟩
  · simp only [List.map_nil, arrSyms_nil_msa, List.nil_append, List.isEmpty_nil, Bool.not_true]
    rcases rx with _ | ⟨y, rx'⟩
    · rfl
    · obtain ⟨h1, h2⟩ := hrx y rfl
      cases y <;> simp_all [isRecO, isDataSym]
  · simp only [List.map_cons, arrSyms_cons_msa, recSyms]
    rcases p with _ | ⟨b, p⟩ <;> rfl

theorem scanSt_init (hd : List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su]) {G : List Bool}
    {S : ℕ} {v vn : List (List Bool)} {rx rxn : List Sym} {St : K → List Sym}
    (hlen : v.length = vn.length) (hV : St V = arrSyms v ++ rx) (hVn : St Vn = arrSyms vn ++ rxn)
    (hOut : St Out = []) (hTb : St Tb = G.map Sym.bit) (hGu : St Gu = [])
    (hSc : St Sc = List.replicate S (Sym.bit false)) (hSu : St Su = []) :
    scanSt V Vn Out Tb Gu Sc Su G S rx rxn St [] (v.zip vn) = St := by
  have e1 : arrSyms ((v.zip vn).map Prod.fst) ++ rx = St V := by
    rw [List.map_fst_zip (by omega), hV]
  have e2 : arrSyms ((v.zip vn).map Prod.snd) ++ rxn = St Vn := by
    rw [List.map_snd_zip (by omega), hVn]
  have e3 : selOut G S [] = St Out := by rw [selOut_nil, hOut]
  have e4 : (G.drop ((([] : List (List Bool × List Bool)).length / S) % G.length)).map Sym.bit =
      St Tb := by simp [hTb]
  have e5 : (G.take ((([] : List (List Bool × List Bool)).length / S) % G.length)).reverse.map
      Sym.bit = St Gu := by simp [hGu]
  have e6 : List.replicate (S - ([] : List (List Bool × List Bool)).length % S) (Sym.bit false) =
      St Sc := by simp [hSc]
  have e7 : List.replicate (([] : List (List Bool × List Bool)).length % S) (Sym.bit false) =
      St Su := by simp [hSu]
  rw [scanSt, e1, e2, e3, e4, e5, e6, e7, mk7_self]

theorem scanSt_final {G : List Bool} {S : ℕ} {v vn : List (List Bool)} {rx rxn : List Sym}
    {St : K → List Sym} (hlen : v.length = vn.length) :
    scanSt V Vn Out Tb Gu Sc Su G S rx rxn St (v.zip vn) [] =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update St V rx) Vn rxn) Out (selOut G S (v.zip vn)))
        Tb ((G.drop ((v.length / S) % G.length)).map Sym.bit))
        Gu ((G.take ((v.length / S) % G.length)).reverse.map Sym.bit))
        Sc (List.replicate (S - v.length % S) (Sym.bit false)))
        Su (List.replicate (v.length % S) (Sym.bit false)) := by
  have hz : (v.zip vn).length = v.length := by simp [List.length_zip, hlen]
  rw [scanSt, hz]
  rfl

end Loop

/-! ## The amortized cost -/

/-- The potential: the work saved towards the next refill and the next table reset. -/
def Phi (G : List Bool) (S i : ℕ) : ℕ := 3 * (i % S) + 7 * ((i / S) % G.length)

theorem step_amort {G : List Bool} {S : ℕ} (hG : 0 < G.length) (hS : 0 < S) (i : ℕ) :
    T2c G S i + Phi G S (i + 1) ≤ 41 + Phi G S i := by
  unfold T2c Phi
  have hr := Nat.mod_lt i hS
  rcases Nat.lt_or_ge (i % S + 1) S with h | h
  · obtain ⟨h1, h2⟩ := mod_succ_lt hS h
    rw [if_neg (by omega), h1, h2]
    omega
  · have h' : i % S + 1 = S := by omega
    obtain ⟨h1, h2⟩ := mod_succ_eq hS h'
    rw [if_pos h', h1, h2]
    have hq := Nat.mod_lt (i / S) hG
    rcases Nat.lt_or_ge ((i / S) % G.length + 1) G.length with hq' | hq'
    · obtain ⟨h3, -⟩ := mod_succ_lt hG hq'
      rw [if_neg (by omega), h3]
      omega
    · have hq'' : (i / S) % G.length + 1 = G.length := by omega
      obtain ⟨h3, -⟩ := mod_succ_eq hG hq''
      rw [if_pos hq'', h3]
      omega

theorem whileCost_amort {G : List Bool} {S : ℕ} (hG : 0 < G.length) (hS : 0 < S) :
    ∀ (rest done : List (List Bool × List Bool)),
      whileCost 1 (costFn G S) done rest + Phi G S (done.length + rest.length) ≤
        (rest.map fun x => 4 * x.1.length + 4 * x.2.length + 58).sum + 1 + Phi G S done.length
  | [], done => by simp [whileCost]
  | x :: rest, done => by
    have ih := whileCost_amort hG hS rest (done ++ [x])
    have hs := step_amort hG hS done.length
    have hl : (done ++ [x]).length = done.length + 1 := by simp
    have hl2 : done.length + (x :: rest).length = done.length + 1 + rest.length := by
      simp only [List.length_cons]; omega
    rw [hl] at ih
    rw [hl2]
    have hw : whileCost 1 (costFn G S) done (x :: rest) =
        costFn G S done x rest + 1 + 1 + whileCost 1 (costFn G S) (done ++ [x]) rest := by
      simp only [whileCost]
    have hc : costFn G S done x rest = 3 * x.1.length + 3 * x.2.length + 15 + T2c G S done.length :=
      rfl
    rw [hw, hc, List.map_cons, List.sum_cons]
    omega

theorem sum_beta : ∀ (v vn : List (List Bool)), v.length = vn.length →
    ((v.zip vn).map fun x => 4 * x.1.length + 4 * x.2.length + 58).sum =
      4 * ((arrSyms v).length + (arrSyms vn).length) + 50 * v.length
  | [], [], _ => by simp [arrSyms_nil_msa]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: v, q :: vn, h => by
    have ih := sum_beta v vn (by simpa using h)
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, vol_cons_msa, List.length_cons]
    omega

/-! ## The main theorem -/

/-- **The select loop** (`SelLoopStmt`). -/
theorem selLoop_holds : SelLoopStmt := by
  intro K _ V Vn Out Tb Gu Sc Su hd G S v vn rx rxn St hG hS hlen hrx _hrxn hV hVn hOut hTb hGu
    hSc hSu
  have hG0 : 0 < G.length := List.length_pos_iff.mpr hG
  have hrun := runs_whileT (v.zip vn) (scanSt V Vn Out Tb Gu Sc Su G S rx rxn St) 1 (costFn G S)
    (fun done rest _ => runs_hpk hd hrx rxn St done rest)
    (fun done x rest _ => runs_body hd hG0 hS rx rxn St done x rest)
  rw [scanSt_init hd hlen hV hVn hOut hTb hGu hSc hSu, scanSt_final hlen] at hrun
  refine WP.W9comp.runs_mono hrun (fun _ _ => trivial) ?_
  have ha := whileCost_amort hG0 hS (v.zip vn) []
  have hs := sum_beta v vn hlen
  have h0 : Phi G S ([] : List (List Bool × List Bool)).length = 0 := by simp [Phi]
  rw [h0, hs] at ha
  omega

end SubNLogN.Machine.CCore.MaskScanAux
