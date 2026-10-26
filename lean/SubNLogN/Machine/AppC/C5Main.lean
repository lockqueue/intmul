/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Skel

/-!
# Proposition A.7 main theorem from a kit (`AppC/C5Main.lean`)

`kit_runs`: under `NetFacts` (pure leaves) and a `Kit` (kernel leaves), every instance of the
Proposition A.7 (`prop:transfer11`) spec (`Inst.Pre`) is run by `c5Prog kit` to the interchanged
stacks within `powBudget s W c k V + 2`, by the recursion rule of the framed procedure calculus
(measure `k`). (`AppC` and `C5`/`c5` retain earlier draft numbering for stability; see Appendix A.)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
open SubNLogN.Math.Cost.Recurrence

/-- Ghost data of one instance of the Proposition A.7 spec. -/
structure Inst (K : Type) where
  k : ℕ
  N0 : ℕ
  R : ℕ
  N1 : ℕ
  G : ℕ
  B : ℕ
  w : ℕ
  v : List (List Bool)
  rest : List Sym
  S : K → List Sym

section Main

variable {q : ℕ} {W m : ℕ} {N : Net W m} {K σ : Type} [DecidableEq K] (kit : Kit q N K σ)

/-- Preconditions of an instance (Proposition A.7 shape; stack `R` is not read). -/
def Pre (x : Inst K) : Prop :=
  1 ≤ x.N0 ∧ 1 ≤ x.R ∧ 1 ≤ x.N1 ∧ 1 ≤ x.G ∧ 1 ≤ x.B ∧ W ^ x.k ∣ x.R ∧
  x.v.length = x.N0 * x.R * rowSize q m x.k x.N1 x.G x.B ∧ (∀ p ∈ x.v, p.length = x.w) ∧
  BlkTerm x.rest ∧ x.S (kit.slot .io) = arrSyms x.v ++ x.rest ∧ CtrOK kit.slot x.S x.k x.N1 x.G x.B

/-- Final stacks of an instance: the array interchanged in place, all else unchanged. -/
def post (x : Inst K) : K → List Sym :=
  Function.update x.S (kit.slot .io) (arrSyms (permByInv (swapMap q m x.k x.G x.B) x.v) ++ x.rest)

/-! ### Slots and role states -/

theorem slot_ne {x y : Slot W} (h : x ≠ y) : kit.slot x ≠ kit.slot y := fun e => h (kit.slot_inj e)

theorem roleOf_role (r : Fin W) : kit.roleOf (kit.slot (.role r)) = some r := by
  rw [kit.roleOf_slot]; rfl

theorem roleOf_none (x : Slot W) (hx : x.roleIdx = none) : kit.roleOf (kit.slot x) = none := by
  rw [kit.roleOf_slot, hx]

theorem setRoles_role (S : K → List Sym) (f : Fin W → List Sym) (r : Fin W) :
    setRoles kit.roleOf S f (kit.slot (.role r)) = f r := by
  simp only [setRoles, roleOf_role]

theorem setRoles_none (S : K → List Sym) (f : Fin W → List Sym) (key : K)
    (h : kit.roleOf key = none) : setRoles kit.roleOf S f key = S key := by
  simp only [setRoles, h]

theorem role_ne_slot (r : Fin W) (x : Slot W) (hx : x.roleIdx = none) :
    kit.slot (.role r) ≠ kit.slot x := by
  intro e
  have := roleOf_role kit r
  rw [e, roleOf_none kit x hx] at this
  simp at this

/-- The state during the schedule of a node: `io` holds the tail, `rsz` the row size, role `r`
holds `us r` above its protection mark; every other stack as in `S`. -/
def nodeSt (S : K → List Sym) (rest : List Sym) (srow : ℕ) (us : Fin W → List (List Bool)) :
    K → List Sym :=
  setRoles kit.roleOf (Function.update (Function.update S (kit.slot .io) rest) (kit.slot .rsz)
    (natSyms srow ++ Sym.mark :: S (kit.slot .rsz)))
    (fun r => arrSyms (us r) ++ Sym.mark :: S (kit.slot (.role r)))

theorem nodeSt_role (S : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us : Fin W → List (List Bool)) (r : Fin W) :
    nodeSt kit S rest srow us (kit.slot (.role r)) = arrSyms (us r) ++ Sym.mark :: S (kit.slot (.role r)) :=
  setRoles_role kit _ _ r

theorem nodeSt_io (S : K → List Sym) (rest : List Sym) (srow : ℕ) (us : Fin W → List (List Bool)) :
    nodeSt kit S rest srow us (kit.slot .io) = rest := by
  rw [nodeSt, setRoles_none kit _ _ _ (roleOf_none kit .io rfl),
    Function.update_of_ne (slot_ne kit (by simp)), Function.update_self]

theorem nodeSt_rsz (S : K → List Sym) (rest : List Sym) (srow : ℕ) (us : Fin W → List (List Bool)) :
    nodeSt kit S rest srow us (kit.slot .rsz) = natSyms srow ++ Sym.mark :: S (kit.slot .rsz) := by
  rw [nodeSt, setRoles_none kit _ _ _ (roleOf_none kit .rsz rfl), Function.update_self]

theorem nodeSt_other (S : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us : Fin W → List (List Bool)) (x : Slot W) (hx : x.roleIdx = none) (hio : x ≠ .io)
    (hrsz : x ≠ .rsz) : nodeSt kit S rest srow us (kit.slot x) = S (kit.slot x) := by
  rw [nodeSt, setRoles_none kit _ _ _ (roleOf_none kit x hx),
    Function.update_of_ne (slot_ne kit hrsz), Function.update_of_ne (slot_ne kit hio)]

theorem ctrOK_of_eq {S S' : K → List Sym} {k N1 G B : ℕ} (h : CtrOK kit.slot S k N1 G B)
    (hck : S' (kit.slot .ck) = S (kit.slot .ck)) (hN1 : S' (kit.slot .cN1) = S (kit.slot .cN1))
    (hG : S' (kit.slot .cG) = S (kit.slot .cG)) (hB : S' (kit.slot .cB) = S (kit.slot .cB)) :
    CtrOK kit.slot S' k N1 G B := by
  obtain ⟨r1, r3, r4, r5, h1, h3, h4, h5, e1, e3, e4, e5⟩ := h
  exact ⟨r1, r3, r4, r5, h1, h3, h4, h5, hck.trans e1, hN1.trans e3, hG.trans e4, hB.trans e5⟩

theorem nodeSt_ctr {S : K → List Sym} {k N1 G B : ℕ} (h : CtrOK kit.slot S k N1 G B)
    (rest : List Sym) (srow : ℕ) (us : Fin W → List (List Bool)) :
    CtrOK kit.slot (nodeSt kit S rest srow us) k N1 G B :=
  ctrOK_of_eq kit h (nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp))
    (nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp))
    (nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp))
    (nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp))

theorem nodeSt_update_role (S : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us : Fin W → List (List Bool)) (w : Fin W) (u : List (List Bool)) :
    Function.update (nodeSt kit S rest srow us) (kit.slot (.role w))
      (arrSyms u ++ Sym.mark :: S (kit.slot (.role w))) =
    nodeSt kit S rest srow (Function.update us w u) := by
  funext key
  rcases hk : kit.roleOf key with _ | r
  · have hne : key ≠ kit.slot (.role w) := by
      rintro rfl; rw [roleOf_role] at hk; simp at hk
    rw [Function.update_of_ne hne, nodeSt, nodeSt, setRoles_none kit _ _ _ hk,
      setRoles_none kit _ _ _ hk]
  · obtain rfl := kit.roleOf_eq_some key r hk
    by_cases hr : r = w
    · subst hr
      rw [Function.update_self, nodeSt_role, Function.update_self]
    · rw [Function.update_of_ne (fun e => hr (Slot.role.inj (kit.slot_inj e))), nodeSt_role,
        nodeSt_role,
        Function.update_of_ne hr]

theorem setRoles_nodeSt (S : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us us' : Fin W → List (List Bool)) :
    setRoles kit.roleOf (nodeSt kit S rest srow us)
      (fun r => arrSyms (us' r) ++ Sym.mark :: S (kit.slot (.role r))) =
    nodeSt kit S rest srow us' := by
  funext key
  rcases hk : kit.roleOf key with _ | r
  · rw [setRoles_none kit _ _ _ hk, nodeSt, nodeSt, setRoles_none kit _ _ _ hk,
      setRoles_none kit _ _ _ hk]
  · obtain rfl := kit.roleOf_eq_some key r hk
    rw [setRoles_role, nodeSt_role]


/-! ### Schedule operations -/

theorem blkTerm_mark (l : List Sym) : BlkTerm (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by decide⟩

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons (by rfl) l

/-- A stream op of the schedule on role `w`. -/
theorem stream_op_runs (x : Inst K) (hx : Pre kit x) (hk : 1 ≤ x.k) (Rt : ℕ) (hRt : 1 ≤ Rt)
    (w : Fin W) (o : N.Op) (us : Fin W → List (List Bool))
    (hus : (us w).length = Rt * rowSize q m x.k x.N1 x.G x.B) (hw : ∀ p ∈ us w, p.length = x.w)
    (srow : ℕ) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (kit.stream o (some w)) (nodeSt kit x.S x.rest srow us)
      (nodeSt kit x.S x.rest srow
        (Function.update us w (permByInv (N.streamMap o x.k x.N1 x.G x.B) (us w))))
      (fun _ => True) (kit.C * (vol (us w) + 1)) := by
  obtain ⟨_, _, hN1, hG, hB, _, _, _, _, _, hctr⟩ := hx
  have h := kit.stream_spec o (some w) x.k Rt x.N1 x.G x.B x.w (us w)
    (Sym.mark :: x.S (kit.slot (.role w))) (nodeSt kit x.S x.rest srow us) hk hRt hN1 hG hB hus hw
    (blkTerm_mark _) (nodeSt_role kit _ _ _ _ w) (nodeSt_ctr kit hctr _ _ _)
  refine RunsIn.of_runs ?_ (kit.stream_closed o (some w)) ρ
  rw [← nodeSt_update_role]
  exact h

/-- A gate of the schedule. -/
theorem gate_op_runs (x : Inst K) (g : N.Gt) (us : Fin W → List (List Bool)) (n : ℕ)
    (hus : ∀ r, (us r).length = n) (hw : ∀ r, ∀ p ∈ us r, p.length = x.w) (srow : ℕ)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (kit.gate g) (nodeSt kit x.S x.rest srow us) (nodeSt kit x.S x.rest srow (N.gateF g us))
      (fun _ => True) (kit.C * (W * (n * (x.w + 1)) + 1)) := by
  have h := kit.gate_spec g us (fun r => Sym.mark :: x.S (kit.slot (.role r))) n x.w
    (nodeSt kit x.S x.rest srow us) hus hw (fun _ => blkTerm_mark _)
    (fun r => nodeSt_role kit _ _ _ _ r)
  refine RunsIn.of_runs ?_ (kit.gate_closed g) ρ
  rw [← setRoles_nodeSt kit x.S x.rest srow us (N.gateF g us)]
  exact h

/-- `xfer` through the register lens, as a `RunsIn` fact. -/
theorem xfer_runsIn {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (u : List (List Bool)) (R : List Sym) (S : K → List Sym) (hR : isRecR R.head? = false)
    (hS : S src = arrSyms u ++ R) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ ((xfer src dst tmp).liftRegs kit.lr) S
      (Function.update (Function.update S src R) dst (arrSyms u ++ S dst)) (fun _ => True)
      (6 * vol u + 2 * u.length + 5) := by
  have h : Runs (xfer src dst tmp) S
      (Function.update (Function.update S src R) dst (arrSyms u ++ S dst)) (fun _ => True)
      (6 * vol u + 2 * u.length + 5) :=
    Runs.of_eval fun v => ⟨_, _, xfer_eval hsd hst hdt v u R S hR hS, trivial, le_rfl⟩
  exact RunsIn.of_runs_liftRegs kit.lr h (closed_xfer _ _ _) ρ

/-- `popDesc` through the register lens. -/
theorem popDesc_runsIn (d : K) (k : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = natSyms k ++ Sym.mark :: tl) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ ((popDesc d).liftRegs kit.lr) S (Function.update S d tl) (fun _ => True)
      (2 * bitLen k + 5) :=
  RunsIn.of_runs_liftRegs kit.lr (runs_popDesc k tl S hS) (closed_popDesc _) ρ


/-- The child instance of the pivot call `(i, j)` on the role array `u` from the stacks `S`. -/
def childInst (q W : ℕ) {m : ℕ} (x : Inst K) (i j : Fin m) (u : List (List Bool))
    (S : K → List Sym) : Inst K :=
  { k := x.k - 1, N0 := x.N0, R := x.R / W, N1 := cN1 q m x.k x.N1 i, G := cG q m x.k x.G i j,
    B := cB q m x.k x.B j, w := x.w, v := u, rest := x.rest, S := S }

theorem one_le_pow' {q : ℕ} (hq : 1 ≤ q) (e : ℕ) : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq

/-- **A pivot call of the schedule**: move role `w`'s array to `io`, push the child descriptor,
recurse, pop, move back. -/
theorem call_op_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s c : ℕ) (x : Inst K) (hx : Pre kit x)
    (hk : 1 ≤ x.k)
    (IH : ∀ y : Inst K, Pre kit y → y.k < x.k →
      RunsIn [bodyProg kit] (.recur 0) y.S (post kit y) (fun _ => True)
        (powBudget s W c y.k (vol y.v) + 2))
    (w : Fin W) (i j : Fin m) (us : Fin W → List (List Bool))
    (hus : (us w).length = x.N0 * (x.R / W) * rowSize q m x.k x.N1 x.G x.B)
    (hw : ∀ p ∈ us w, p.length = x.w) :
    RunsIn [bodyProg kit] (compileOp kit (.call w i j))
      (nodeSt kit x.S x.rest (rowSize q m x.k x.N1 x.G x.B) us)
      (nodeSt kit x.S x.rest (rowSize q m x.k x.N1 x.G x.B) (Function.update us w
        (permByInv (swapMap q m (x.k - 1) (cG q m x.k x.G i j) (cB q m x.k x.B j)) (us w))))
      (fun _ => True)
      (powBudget s W c (x.k - 1) (vol (us w)) +
        (kit.C + 40) * (vol (us w) + rowSize q m x.k x.N1 x.G x.B + 1)) := by
  have hq : 1 ≤ q := by omega
  obtain ⟨hN0, hR, hN1, hG, hB, hdiv, _, _, hrest, _, hctr⟩ := hx
  have hctr' := hctr
  obtain ⟨r1, r3, r4, r5, t1, t3, t4, t5, e1, e3, e4, e5⟩ := hctr'
  set srow := rowSize q m x.k x.N1 x.G x.B with hsrow
  set u := us w with hu
  set u' := permByInv (swapMap q m (x.k - 1) (cG q m x.k x.G i j) (cB q m x.k x.B j)) u with hu'
  set S0 := nodeSt kit x.S x.rest srow us with hS0
  -- slot facts
  have hwio : kit.slot (.role w) ≠ kit.slot .io := role_ne_slot kit w .io rfl
  have hwtmp : kit.slot (.role w) ≠ kit.slot .tmp := role_ne_slot kit w .tmp rfl
  have hwck : kit.slot (.role w) ≠ kit.slot .ck := role_ne_slot kit w .ck rfl
  have hwN1 : kit.slot (.role w) ≠ kit.slot .cN1 := role_ne_slot kit w .cN1 rfl
  have hwG : kit.slot (.role w) ≠ kit.slot .cG := role_ne_slot kit w .cG rfl
  have hwB : kit.slot (.role w) ≠ kit.slot .cB := role_ne_slot kit w .cB rfl
  have hiotmp : kit.slot .io ≠ kit.slot .tmp := slot_ne kit (by simp)
  have hck_io : kit.slot .ck ≠ kit.slot .io := slot_ne kit (by simp)
  have hN1_io : kit.slot .cN1 ≠ kit.slot .io := slot_ne kit (by simp)
  have hG_io : kit.slot .cG ≠ kit.slot .io := slot_ne kit (by simp)
  have hB_io : kit.slot .cB ≠ kit.slot .io := slot_ne kit (by simp)
  have hck_N1 : kit.slot .ck ≠ kit.slot .cN1 := slot_ne kit (by simp)
  have hck_G : kit.slot .ck ≠ kit.slot .cG := slot_ne kit (by simp)
  have hck_B : kit.slot .ck ≠ kit.slot .cB := slot_ne kit (by simp)
  have hN1_G : kit.slot .cN1 ≠ kit.slot .cG := slot_ne kit (by simp)
  have hN1_B : kit.slot .cN1 ≠ kit.slot .cB := slot_ne kit (by simp)
  have hG_B : kit.slot .cG ≠ kit.slot .cB := slot_ne kit (by simp)
  have hS0io : S0 (kit.slot .io) = x.rest := nodeSt_io kit _ _ _ _
  have hS0w : S0 (kit.slot (.role w)) = arrSyms u ++ Sym.mark :: x.S (kit.slot (.role w)) :=
    nodeSt_role kit _ _ _ _ w
  have hS0ck : S0 (kit.slot .ck) = x.S (kit.slot .ck) := nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp)
  have hS0N1 : S0 (kit.slot .cN1) = x.S (kit.slot .cN1) :=
    nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp)
  have hS0G : S0 (kit.slot .cG) = x.S (kit.slot .cG) := nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp)
  have hS0B : S0 (kit.slot .cB) = x.S (kit.slot .cB) := nodeSt_other kit _ _ _ _ _ rfl (by simp) (by simp)
  -- step 1: role w → io
  have h1 := xfer_runsIn kit hwio hwtmp hiotmp u (Sym.mark :: x.S (kit.slot (.role w))) S0 rfl hS0w
    [bodyProg kit]
  set A1 := Function.update (Function.update S0 (kit.slot (.role w))
    (Sym.mark :: x.S (kit.slot (.role w)))) (kit.slot .io) (arrSyms u ++ S0 (kit.slot .io)) with hA1
  have hA1io : A1 (kit.slot .io) = arrSyms u ++ x.rest := by rw [hA1, Function.update_self, hS0io]
  have hA1ck : A1 (kit.slot .ck) = x.S (kit.slot .ck) := by
    rw [hA1, Function.update_of_ne hck_io, Function.update_of_ne (Ne.symm hwck), hS0ck]
  have hA1N1 : A1 (kit.slot .cN1) = x.S (kit.slot .cN1) := by
    rw [hA1, Function.update_of_ne hN1_io, Function.update_of_ne (Ne.symm hwN1), hS0N1]
  have hA1G : A1 (kit.slot .cG) = x.S (kit.slot .cG) := by
    rw [hA1, Function.update_of_ne hG_io, Function.update_of_ne (Ne.symm hwG), hS0G]
  have hA1B : A1 (kit.slot .cB) = x.S (kit.slot .cB) := by
    rw [hA1, Function.update_of_ne hB_io, Function.update_of_ne (Ne.symm hwB), hS0B]
  -- step 2: child descriptor
  have hctrA1 : CtrOK kit.slot A1 x.k x.N1 x.G x.B :=
    ctrOK_of_eq kit hctr hA1ck hA1N1 hA1G hA1B
  have h2 := RunsIn.of_runs (kit.desc_spec i j x.k x.N1 x.G x.B A1 hk hN1 hG hB hctrA1) (kit.desc_closed i j)
    [bodyProg kit]
  set A2 := descPost kit.slot q m i j x.k x.N1 x.G x.B A1 with hA2
  have hA2io : A2 (kit.slot .io) = arrSyms u ++ x.rest := by
    rw [hA2, descPost, Function.update_of_ne (Ne.symm hB_io), Function.update_of_ne (Ne.symm hG_io),
      Function.update_of_ne (Ne.symm hN1_io), Function.update_of_ne (Ne.symm hck_io), hA1io]
  have hA2ck : A2 (kit.slot .ck) = natSyms (x.k - 1) ++ Sym.mark :: A1 (kit.slot .ck) := by
    rw [hA2, descPost, Function.update_of_ne hck_B, Function.update_of_ne hck_G,
      Function.update_of_ne hck_N1, Function.update_self]
  have hA2N1 : A2 (kit.slot .cN1) = natSyms (cN1 q m x.k x.N1 i) ++ Sym.mark :: A1 (kit.slot .cN1) := by
    rw [hA2, descPost, Function.update_of_ne hN1_B, Function.update_of_ne hN1_G,
      Function.update_self]
  have hA2G : A2 (kit.slot .cG) = natSyms (cG q m x.k x.G i j) ++ Sym.mark :: A1 (kit.slot .cG) := by
    rw [hA2, descPost, Function.update_of_ne hG_B, Function.update_self]
  have hA2B : A2 (kit.slot .cB) = natSyms (cB q m x.k x.B j) ++ Sym.mark :: A1 (kit.slot .cB) := by
    rw [hA2, descPost, Function.update_self]
  -- step 3: the recursive call
  have hWR : W ∣ x.R := dvd_trans (dvd_pow_self W (by omega)) hdiv
  have hRW : 1 ≤ x.R / W := Nat.div_pos (Nat.le_of_dvd (by omega) hWR) hW
  have hyPre : Pre kit (childInst q W x i j u A2) := by
    refine ⟨hN0, hRW, ?_, ?_, ?_, ?_, ?_, hw, hrest, hA2io, ?_⟩
    · exact Nat.mul_le_mul hN1 (one_le_pow' hq _)
    · exact Nat.mul_le_mul (Nat.mul_le_mul (one_le_pow' hq _) hG) (one_le_pow' hq _)
    · exact Nat.mul_le_mul (one_le_pow' hq _) hB
    · obtain ⟨t, ht⟩ := hdiv
      refine ⟨t, ?_⟩
      show x.R / W = W ^ (x.k - 1) * t
      rw [ht, show W ^ x.k = W * W ^ (x.k - 1) by
        rw [← pow_succ']; congr 1; omega, Nat.mul_assoc, Nat.mul_div_cancel_left _ hW]
    · show u.length = x.N0 * (x.R / W) * rowSize q m (x.k - 1) (cN1 q m x.k x.N1 i)
        (cG q m x.k x.G i j) (cB q m x.k x.B j)
      rw [rowSize_child q m x.k x.N1 x.G x.B i j i.isLt j.isLt hk]
      exact hus
    · exact ⟨_, _, _, _, termOK_mark _, termOK_mark _, termOK_mark _, termOK_mark _, hA2ck, hA2N1,
        hA2G, hA2B⟩
  have h3 := IH _ hyPre (by show x.k - 1 < x.k; omega)
  set A3 := post kit (childInst q W x i j u A2) with hA3
  have hA3eq : A3 = Function.update A2 (kit.slot .io) (arrSyms u' ++ x.rest) := rfl
  -- steps 4-7: pop the child descriptor
  have hA3ck : A3 (kit.slot .ck) = natSyms (x.k - 1) ++ Sym.mark :: A1 (kit.slot .ck) := by
    rw [hA3eq, Function.update_of_ne hck_io, hA2ck]
  have h4 := popDesc_runsIn kit (kit.slot .ck) (x.k - 1) (A1 (kit.slot .ck)) A3 hA3ck [bodyProg kit]
  set A4 := Function.update A3 (kit.slot .ck) (A1 (kit.slot .ck)) with hA4
  have hA4N1 : A4 (kit.slot .cN1) = natSyms (cN1 q m x.k x.N1 i) ++ Sym.mark :: A1 (kit.slot .cN1) := by
    rw [hA4, Function.update_of_ne (Ne.symm hck_N1), hA3eq, Function.update_of_ne hN1_io, hA2N1]
  have h5 := popDesc_runsIn kit (kit.slot .cN1) _ (A1 (kit.slot .cN1)) A4 hA4N1 [bodyProg kit]
  set A5 := Function.update A4 (kit.slot .cN1) (A1 (kit.slot .cN1)) with hA5
  have hA5G : A5 (kit.slot .cG) = natSyms (cG q m x.k x.G i j) ++ Sym.mark :: A1 (kit.slot .cG) := by
    rw [hA5, Function.update_of_ne (Ne.symm hN1_G), hA4, Function.update_of_ne (Ne.symm hck_G),
      hA3eq, Function.update_of_ne hG_io, hA2G]
  have h6 := popDesc_runsIn kit (kit.slot .cG) _ (A1 (kit.slot .cG)) A5 hA5G [bodyProg kit]
  set A6 := Function.update A5 (kit.slot .cG) (A1 (kit.slot .cG)) with hA6
  have hA6B : A6 (kit.slot .cB) = natSyms (cB q m x.k x.B j) ++ Sym.mark :: A1 (kit.slot .cB) := by
    rw [hA6, Function.update_of_ne (Ne.symm hG_B), hA5, Function.update_of_ne (Ne.symm hN1_B), hA4,
      Function.update_of_ne (Ne.symm hck_B), hA3eq, Function.update_of_ne hB_io, hA2B]
  have h7 := popDesc_runsIn kit (kit.slot .cB) _ (A1 (kit.slot .cB)) A6 hA6B [bodyProg kit]
  set A7 := Function.update A6 (kit.slot .cB) (A1 (kit.slot .cB)) with hA7
  have hA7eq : A7 = Function.update A1 (kit.slot .io) (arrSyms u' ++ x.rest) := by
    funext key
    by_cases kB : key = kit.slot .cB
    · subst kB
      rw [hA7, Function.update_self, Function.update_of_ne hB_io]
    · rw [hA7, Function.update_of_ne kB]
      by_cases kG : key = kit.slot .cG
      · subst kG
        rw [hA6, Function.update_self, Function.update_of_ne hG_io]
      · rw [hA6, Function.update_of_ne kG]
        by_cases kN1 : key = kit.slot .cN1
        · subst kN1
          rw [hA5, Function.update_self, Function.update_of_ne hN1_io]
        · rw [hA5, Function.update_of_ne kN1]
          by_cases kck : key = kit.slot .ck
          · subst kck
            rw [hA4, Function.update_self, Function.update_of_ne hck_io]
          · rw [hA4, Function.update_of_ne kck, hA3eq]
            by_cases kio : key = kit.slot .io
            · subst kio
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne kio, Function.update_of_ne kio, hA2, descPost,
                Function.update_of_ne kB, Function.update_of_ne kG, Function.update_of_ne kN1,
                Function.update_of_ne kck]
  -- step 8: io → role w
  have hA7io : A7 (kit.slot .io) = arrSyms u' ++ x.rest := by rw [hA7eq, Function.update_self]
  have h8 := xfer_runsIn kit (Ne.symm hwio) hiotmp hwtmp u' x.rest A7 (isRecR_of_blkTerm hrest)
    hA7io [bodyProg kit]
  have hA7w : A7 (kit.slot (.role w)) = Sym.mark :: x.S (kit.slot (.role w)) := by
    rw [hA7eq, Function.update_of_ne hwio, hA1, Function.update_of_ne hwio, Function.update_self]
  have hfin : Function.update (Function.update A7 (kit.slot .io) x.rest) (kit.slot (.role w))
      (arrSyms u' ++ A7 (kit.slot (.role w))) =
      nodeSt kit x.S x.rest srow (Function.update us w u') := by
    rw [← nodeSt_update_role, hA7w]
    funext key
    by_cases hkw : key = kit.slot (.role w)
    · subst hkw
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hkw, Function.update_of_ne hkw]
      by_cases hkio : key = kit.slot .io
      · subst hkio
        rw [Function.update_self]
        exact (nodeSt_io kit _ _ _ _).symm
      · rw [Function.update_of_ne hkio, hA7eq, Function.update_of_ne hkio, hA1,
          Function.update_of_ne hkio, Function.update_of_ne hkw]
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 (RunsIn.seq h4 (RunsIn.seq h5
    (RunsIn.seq h6 (RunsIn.seq h7 h8))))))
  refine RunsIn.congr hall hfin ?_
  -- cost
  have hsr := rowSize_child q m x.k x.N1 x.G x.B i j i.isLt j.isLt hk
  set b := m ^ (x.k - 1) with hb
  have hqb : 1 ≤ q ^ b := one_le_pow' hq b
  have hcN1 : 1 ≤ cN1 q m x.k x.N1 i := Nat.mul_le_mul hN1 (one_le_pow' hq _)
  have hcG : 1 ≤ cG q m x.k x.G i j :=
    Nat.mul_le_mul (Nat.mul_le_mul (one_le_pow' hq _) hG) (one_le_pow' hq _)
  have hcB : 1 ≤ cB q m x.k x.B j := Nat.mul_le_mul (one_le_pow' hq _) hB
  have hsr' : cN1 q m x.k x.N1 i * q ^ b * cG q m x.k x.G i j * q ^ b * cB q m x.k x.B j = srow := by
    rw [hsrow, ← hsr]; rfl
  have b1 : cN1 q m x.k x.N1 i ≤ srow := by
    rw [← hsr']
    calc cN1 q m x.k x.N1 i = cN1 q m x.k x.N1 i * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have b2 : cG q m x.k x.G i j ≤ srow := by
    rw [← hsr']
    calc cG q m x.k x.G i j = 1 * 1 * cG q m x.k x.G i j * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have b3 : cB q m x.k x.B j ≤ srow := by
    rw [← hsr']
    calc cB q m x.k x.B j = 1 * 1 * 1 * 1 * cB q m x.k x.B j := by ring
      _ ≤ _ := by gcongr
  have b0 : x.k - 1 ≤ srow := by
    have h1' : x.k - 1 < 2 ^ (x.k - 1) := Nat.lt_two_pow_self
    have h2' : 2 ^ (x.k - 1) ≤ q ^ b := by
      calc 2 ^ (x.k - 1) ≤ q ^ (x.k - 1) := Nat.pow_le_pow_left hq2 _
        _ ≤ q ^ b := Nat.pow_le_pow_right (by omega) (by
          rw [hb]; exact (Nat.lt_pow_self (by omega)).le)
    have h3' : q ^ b ≤ srow := by
      rw [← hsr']
      calc q ^ b = 1 * q ^ b * 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    omega
  have hl' : u'.length = u.length := permByInv_length _ _
  have hvol' : vol u' = vol u := by
    have hwu' : ∀ p ∈ u', p.length = x.w :=
      permByInv_widths _ u x.w (fun y hy => swapFieldsInv_lt _ _ _ _ _ y (by
        rw [hus]
        have : q ^ m ^ (x.k - 1) * cG q m x.k x.G i j * q ^ m ^ (x.k - 1) * cB q m x.k x.B j ∣ srow := by
          rw [← hsr']; exact ⟨cN1 q m x.k x.N1 i, by ring⟩
        exact Dvd.dvd.mul_left this _) hy) hw
    rw [vol_of_widths u' x.w hwu', vol_of_widths u x.w hw, hl']
  have hlu := length_le_vol u
  have bl0 := bitLen_le_self (x.k - 1)
  have bl1 := bitLen_le_self (cN1 q m x.k x.N1 i)
  have bl2 := bitLen_le_self (cG q m x.k x.G i j)
  have bl3 := bitLen_le_self (cB q m x.k x.B j)
  show 6 * vol u + 2 * u.length + 5 + (kit.C * (srow + 1) + (powBudget s W c (x.k - 1) (vol u) + 2 +
    (2 * bitLen (x.k - 1) + 5 + (2 * bitLen (cN1 q m x.k x.N1 i) + 5 +
    (2 * bitLen (cG q m x.k x.G i j) + 5 + (2 * bitLen (cB q m x.k x.B j) + 5 +
    (6 * vol u' + 2 * u'.length + 5))))))) ≤
    powBudget s W c (x.k - 1) (vol u) + (kit.C + 40) * (vol u + srow + 1)
  rw [hvol', hl', Nat.add_mul]
  have hle1 : kit.C * (srow + 1) ≤ kit.C * (vol u + srow + 1) := Nat.mul_le_mul_left _ (by omega)
  omega


/-! ### Shapes along the schedule -/

/-- Every role array has `n` records of width `w`. -/
def Shp (n w : ℕ) (us : Fin W → List (List Bool)) : Prop :=
  ∀ r, (us r).length = n ∧ ∀ p ∈ us r, p.length = w

theorem runOp_shape {s : ℕ} (hNF : NetFacts q N s) (k N1 G B g w : ℕ) (hk : 1 ≤ k)
    (op : SchedOp W m N.Op N.Gt) (us : Fin W → List (List Bool))
    (h : Shp (g * rowSize q m k N1 G B) w us) :
    Shp (g * rowSize q m k N1 G B) w (runOp q N k N1 G B op us) := by
  cases op with
  | stream w' o =>
    intro r
    by_cases hr : r = w'
    · subst hr
      simp only [runOp, Function.update_self]
      refine ⟨by rw [permByInv_length]; exact (h r).1, ?_⟩
      exact permByInv_widths _ _ w (fun y hy => hNF.stream_lt o k N1 G B _ hk
        (by rw [(h r).1]; exact Dvd.intro_left _ rfl) y hy) (h r).2
    · simp only [runOp, Function.update_of_ne hr]
      exact h r
  | gate g' =>
    obtain ⟨h1, h2⟩ := hNF.gate_shape g' us _ w (fun r => (h r).1) (fun r => (h r).2)
    exact fun r => ⟨h1 r, h2 r⟩
  | call w' i j =>
    intro r
    by_cases hr : r = w'
    · subst hr
      simp only [runOp, Function.update_self]
      refine ⟨by rw [permByInv_length]; exact (h r).1, ?_⟩
      refine permByInv_widths _ _ w (fun y hy => swapFieldsInv_lt _ _ _ _ _ y ?_ hy) (h r).2
      rw [(h r).1, ← rowSize_child q m k N1 G B i j i.isLt j.isLt hk]
      exact Dvd.dvd.mul_left ⟨cN1 q m k N1 i, by simp only [rowSize]; ring⟩ _
    · simp only [runOp, Function.update_of_ne hr]
      exact h r

theorem runSched_shape {s : ℕ} (hNF : NetFacts q N s) (k N1 G B g w : ℕ) (hk : 1 ≤ k) :
    ∀ (l : List (SchedOp W m N.Op N.Gt)) (us : Fin W → List (List Bool)),
      Shp (g * rowSize q m k N1 G B) w us →
      Shp (g * rowSize q m k N1 G B) w (runSched q N k N1 G B l us)
  | [], _, h => h
  | op :: l, us, h => runSched_shape hNF k N1 G B g w hk l _ (runOp_shape hNF k N1 G B g w hk op us h)

theorem runSched_take_succ (k N1 G B : ℕ) (l : List (SchedOp W m N.Op N.Gt)) (i : ℕ)
    (hi : i < l.length) (us : Fin W → List (List Bool)) :
    runSched q N k N1 G B (l.take (i + 1)) us =
      runOp q N k N1 G B l[i] (runSched q N k N1 G B (l.take i) us) := by
  unfold runSched
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem sum_sched_cost (a b : ℕ) :
    ∀ l : List (SchedOp W m N.Op N.Gt),
      (l.map fun op => (if op.isCall then a else 0) + b).sum =
        (l.filter SchedOp.isCall).length * a + l.length * b
  | [] => by simp
  | op :: l => by
    rw [List.map_cons, List.sum_cons, sum_sched_cost a b l]
    cases h : op.isCall
    · simp [h]; ring
    · simp [h]; ring

/-- **The schedule of a node** runs op by op (pure semantics `runSched`), each call recursing. -/
theorem sched_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s c : ℕ) (hNF : NetFacts q N s)
    (x : Inst K) (hx : Pre kit x) (hk : 1 ≤ x.k)
    (IH : ∀ y : Inst K, Pre kit y → y.k < x.k →
      RunsIn [bodyProg kit] (.recur 0) y.S (post kit y) (fun _ => True)
        (powBudget s W c y.k (vol y.v) + 2))
    (us0 : Fin W → List (List Bool))
    (hus0 : Shp (x.N0 * (x.R / W) * rowSize q m x.k x.N1 x.G x.B) x.w us0) :
    RunsIn [bodyProg kit] (forEachProg N.sched (compileOp kit))
      (nodeSt kit x.S x.rest (rowSize q m x.k x.N1 x.G x.B) us0)
      (nodeSt kit x.S x.rest (rowSize q m x.k x.N1 x.G x.B)
        (runSched q N x.k x.N1 x.G x.B N.sched us0))
      (fun _ => True)
      ((N.sched.filter SchedOp.isCall).length * powBudget s W c (x.k - 1)
          (x.N0 * (x.R / W) * rowSize q m x.k x.N1 x.G x.B * (x.w + 1)) +
        N.sched.length * ((kit.C + 40) * (W * (x.N0 * (x.R / W) * rowSize q m x.k x.N1 x.G x.B *
          (x.w + 1)) + rowSize q m x.k x.N1 x.G x.B + 1)) + 1) := by
  have hx' := hx
  obtain ⟨hN0, hR, _, _, _, hdiv, _, _, _, _, _⟩ := hx'
  have hWR : W ∣ x.R := dvd_trans (dvd_pow_self W (by omega)) hdiv
  have hRW : 1 ≤ x.R / W := Nat.div_pos (Nat.le_of_dvd (by omega) hWR) hW
  have hgpos : 1 ≤ x.N0 * (x.R / W) := Nat.mul_le_mul hN0 hRW
  set srow := rowSize q m x.k x.N1 x.G x.B with hsrow
  set n := x.N0 * (x.R / W) * srow with hn
  set Vr := n * (x.w + 1) with hVr
  have hVrW : Vr ≤ W * Vr := Nat.le_mul_of_pos_left _ hW
  have h := RunsIn.forEachProg (ρ := [bodyProg kit]) (compileOp kit)
    (fun op => (if op.isCall then powBudget s W c (x.k - 1) Vr else 0) +
      (kit.C + 40) * (W * Vr + srow + 1))
    N.sched (fun i => nodeSt kit x.S x.rest srow (runSched q N x.k x.N1 x.G x.B (N.sched.take i) us0))
    (fun i hi => by
      have hsh := runSched_shape hNF x.k x.N1 x.G x.B (x.N0 * (x.R / W)) x.w hk (N.sched.take i)
        us0 hus0
      show RunsIn _ _ (nodeSt kit x.S x.rest srow (runSched q N x.k x.N1 x.G x.B (N.sched.take i) us0))
        (nodeSt kit x.S x.rest srow (runSched q N x.k x.N1 x.G x.B (N.sched.take (i + 1)) us0)) _ _
      rw [runSched_take_succ x.k x.N1 x.G x.B N.sched i hi us0]
      generalize runSched q N x.k x.N1 x.G x.B (N.sched.take i) us0 = us at hsh ⊢
      generalize N.sched[i] = op
      have hvol : ∀ r, vol (us r) = Vr := fun r => by rw [vol_of_widths _ x.w (hsh r).2, (hsh r).1]
      cases op with
      | stream w o =>
        refine RunsIn.mono (stream_op_runs kit x hx hk _ hgpos w o us (hsh w).1 (hsh w).2 srow _)
          (fun _ h => h) ?_
        simp only [SchedOp.isCall, if_false, Bool.false_eq_true, Nat.zero_add, hvol w]
        have : kit.C * (Vr + 1) ≤ kit.C * (W * Vr + srow + 1) := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.add_mul (kit.C) 40]
        omega
      | gate g =>
        refine RunsIn.mono (gate_op_runs kit x g us n (fun r => (hsh r).1) (fun r => (hsh r).2)
          srow _) (fun _ h => h) ?_
        simp only [SchedOp.isCall, if_false, Bool.false_eq_true, Nat.zero_add]
        have : kit.C * (W * (n * (x.w + 1)) + 1) ≤ kit.C * (W * Vr + srow + 1) :=
          Nat.mul_le_mul_left _ (by rw [hVr]; omega)
        rw [Nat.add_mul (kit.C) 40]
        omega
      | call w i' j' =>
        refine RunsIn.mono (call_op_runs kit hq2 hm hW s c x hx hk IH w i' j' us (hsh w).1 (hsh w).2)
          (fun _ h => h) ?_
        simp only [SchedOp.isCall, if_true, hvol w]
        rw [← hsrow]
        have : (kit.C + 40) * (Vr + srow + 1) ≤ (kit.C + 40) * (W * Vr + srow + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega)
  rw [List.take_length] at h
  refine RunsIn.mono h (fun _ h => h) (le_of_eq ?_)
  rw [sum_sched_cost]

end Main

end SubNLogN.Machine.C5
