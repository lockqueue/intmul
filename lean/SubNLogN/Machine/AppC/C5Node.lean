/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Main

/-!
# Proposition A.7 skeleton, part 3 (`AppC/C5Node.lean`): one node of the recursion

Proposition A.7 (`prop:transfer11`). A node at level `k ≥ 1`: the outer shear
`pre` on the whole array; inside the protection of the `W` role stacks: push the row size, cyclic
row distribution (K2DistributeBlk), the fixed schedule (`sched_runs`, children recurse), merge in
order `ρ` (K2MergeBlk), pop the row size; then the outer shear `post`. With `NodeCorrect` this is
the level-`k` interchange; the cost is `#calls · T_{k-1}(V/W) + O(V)`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
open SubNLogN.Math.Cost.Recurrence

section Node

variable {q : ℕ} {W m : ℕ} {N : Net W m} {K σ : Type} [DecidableEq K] (kit : Kit q N K σ)

theorem role_inj : Function.Injective (fun w : Fin W => kit.slot (.role w)) := fun _ _ h =>
  Slot.role.inj (kit.slot_inj h)

theorem mem_roles_iff (key : K) :
    key ∈ (List.finRange W).map (fun w => kit.slot (.role w)) ↔ (kit.roleOf key).isSome := by
  constructor
  · intro h
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    rw [roleOf_role]
    rfl
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    rw [kit.roleOf_eq_some key r hr]
    exact List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩

theorem not_mem_roles {key : K} (hk : kit.roleOf key = none) :
    key ∉ (List.finRange W).map (fun w => kit.slot (.role w)) := fun h => by
  have := (mem_roles_iff kit key).1 h
  rw [hk] at this
  simp at this

theorem protState_roles (S : K → List Sym) :
    protState ((List.finRange W).map (fun w => kit.slot (.role w))) S =
      setRoles kit.roleOf S (fun r => Sym.mark :: S (kit.slot (.role r))) := by
  funext key
  rcases hk : kit.roleOf key with _ | r
  · rw [setRoles_none kit _ _ _ hk]
    simp only [protState, if_neg (not_mem_roles kit hk)]
  · have hm : key ∈ (List.finRange W).map (fun w => kit.slot (.role w)) :=
      (mem_roles_iff kit key).2 (by rw [hk]; rfl)
    have e := kit.roleOf_eq_some key r hk
    subst e
    rw [setRoles_role]
    simp only [protState, if_pos hm]

/-- The final state of a protected call, from agreement on role and non-role stacks. -/
theorem prot_final (S1 S' S2 : K → List Sym)
    (hrole : ∀ r, S1 (kit.slot (.role r)) = S2 (kit.slot (.role r)))
    (hother : ∀ key, kit.roleOf key = none → S' key = S2 key) :
    (fun key => if key ∈ (List.finRange W).map (fun w => kit.slot (.role w)) then S1 key
      else S' key) = S2 := by
  funext key
  rcases hk : kit.roleOf key with _ | r
  · simp only [if_neg (not_mem_roles kit hk)]
    exact hother key hk
  · have hm : key ∈ (List.finRange W).map (fun w => kit.slot (.role w)) :=
      (mem_roles_iff kit key).2 (by rw [hk]; rfl)
    have e := kit.roleOf_eq_some key r hk
    simp only [if_pos hm]
    rw [e]
    exact hrole r

/-- After `rowsz` and `dist` from the protected state: the schedule state `nodeSt`. -/
theorem dist_state (S P0 : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us : Fin W → List (List Bool))
    (h0 : ∀ key, kit.roleOf key = none → key ≠ kit.slot .io → P0 key = S key)
    (h0r : ∀ r, P0 (kit.slot (.role r)) = Sym.mark :: S (kit.slot (.role r))) :
    setRoles kit.roleOf (Function.update (Function.update P0 (kit.slot .rsz)
        (natSyms srow ++ Sym.mark :: P0 (kit.slot .rsz))) (kit.slot .io) rest)
      (fun r => arrSyms (us r) ++ Function.update P0 (kit.slot .rsz)
        (natSyms srow ++ Sym.mark :: P0 (kit.slot .rsz)) (kit.slot (.role r))) =
    nodeSt kit S rest srow us := by
  have hio_rsz : kit.slot .io ≠ kit.slot .rsz := slot_ne kit (by simp)
  have hP0rsz : P0 (kit.slot .rsz) = S (kit.slot .rsz) :=
    h0 _ (roleOf_none kit .rsz rfl) (Ne.symm hio_rsz)
  funext key
  rcases hk : kit.roleOf key with _ | r
  · rw [setRoles_none kit _ _ _ hk, nodeSt, setRoles_none kit _ _ _ hk]
    by_cases hio : key = kit.slot .io
    · subst hio
      rw [Function.update_self, Function.update_of_ne hio_rsz, Function.update_self]
    · by_cases hrsz : key = kit.slot .rsz
      · subst hrsz
        rw [Function.update_of_ne hio, Function.update_self, Function.update_self, hP0rsz]
      · simp only [Function.update_of_ne hio, Function.update_of_ne hrsz]
        exact h0 key hk hio
  · have e := kit.roleOf_eq_some key r hk
    subst e
    rw [setRoles_role, nodeSt_role, Function.update_of_ne (role_ne_slot kit r .rsz rfl), h0r]

/-- After `merge` and popping the row size: the array is back on `io`, roles protected. -/
theorem merge_state (S : K → List Sym) (rest : List Sym) (srow : ℕ)
    (us : Fin W → List (List Bool)) (vM : List (List Bool)) :
    Function.update (setRoles kit.roleOf (Function.update (nodeSt kit S rest srow us)
        (kit.slot .io) (arrSyms vM ++ rest)) (fun r => Sym.mark :: S (kit.slot (.role r))))
      (kit.slot .rsz) (S (kit.slot .rsz)) =
    setRoles kit.roleOf (Function.update S (kit.slot .io) (arrSyms vM ++ rest))
      (fun r => Sym.mark :: S (kit.slot (.role r))) := by
  have hio_rsz : kit.slot .io ≠ kit.slot .rsz := slot_ne kit (by simp)
  funext key
  by_cases hrsz : key = kit.slot .rsz
  · subst hrsz
    rw [Function.update_self, setRoles_none kit _ _ _ (roleOf_none kit .rsz rfl),
      Function.update_of_ne (Ne.symm hio_rsz)]
  · rw [Function.update_of_ne hrsz]
    rcases hk : kit.roleOf key with _ | r
    · rw [setRoles_none kit _ _ _ hk, setRoles_none kit _ _ _ hk]
      by_cases hio : key = kit.slot .io
      · subst hio
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hio, Function.update_of_ne hio, nodeSt,
          setRoles_none kit _ _ _ hk, Function.update_of_ne hrsz, Function.update_of_ne hio]
    · have e := kit.roleOf_eq_some key r hk
      subst e
      rw [setRoles_role, setRoles_role]

/-- **The protected inside of a node**: row size, distribution, schedule, merge, pop. -/
theorem inner_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s c : ℕ) (hNF : NetFacts q N s)
    (x : Inst K) (hx : Pre kit x) (hk : 1 ≤ x.k)
    (IH : ∀ y : Inst K, Pre kit y → y.k < x.k →
      RunsIn [bodyProg kit] (.recur 0) y.S (post kit y) (fun _ => True)
        (powBudget s W c y.k (vol y.v) + 2))
    (u : List (List Bool)) (hu : u.length = x.N0 * x.R * rowSize q m x.k x.N1 x.G x.B)
    (huw : ∀ p ∈ u, p.length = x.w) :
    RunsIn [bodyProg kit] (innerProg kit)
      (setRoles kit.roleOf (Function.update x.S (kit.slot .io) (arrSyms u ++ x.rest))
        (fun r => Sym.mark :: x.S (kit.slot (.role r))))
      (setRoles kit.roleOf (Function.update x.S (kit.slot .io)
        (arrSyms (mergeBlocks W N.ρ (x.N0 * (x.R / W)) (rowSize q m x.k x.N1 x.G x.B)
          (runSched q N x.k x.N1 x.G x.B N.sched
            (fun r => roleBlocks W r.val (rowSize q m x.k x.N1 x.G x.B) u))) ++ x.rest))
        (fun r => Sym.mark :: x.S (kit.slot (.role r))))
      (fun _ => True)
      ((N.sched.filter SchedOp.isCall).length * powBudget s W c (x.k - 1) (vol x.v / W) +
        3 * (N.sched.length + 4) * (kit.C + 40) * vol x.v) := by
  have hx' := hx
  obtain ⟨hN0, hR, hN1, hG, hB, hdiv, hvlen, hvw, hrest, _, hctr⟩ := hx'
  have hWR : W ∣ x.R := dvd_trans (dvd_pow_self W (by omega)) hdiv
  have hRg : x.N0 * x.R = W * (x.N0 * (x.R / W)) := by
    rw [Nat.mul_left_comm, Nat.mul_div_cancel' hWR]
  have hio_rsz : kit.slot .io ≠ kit.slot .rsz := slot_ne kit (by simp)
  have hck_io : kit.slot .ck ≠ kit.slot .io := slot_ne kit (by simp)
  have hN1_io : kit.slot .cN1 ≠ kit.slot .io := slot_ne kit (by simp)
  have hG_io : kit.slot .cG ≠ kit.slot .io := slot_ne kit (by simp)
  have hB_io : kit.slot .cB ≠ kit.slot .io := slot_ne kit (by simp)
  obtain ⟨srow, hsrow⟩ : ∃ t, t = rowSize q m x.k x.N1 x.G x.B := ⟨_, rfl⟩
  rw [← hsrow] at hu hvlen ⊢
  set P0 := setRoles kit.roleOf (Function.update x.S (kit.slot .io) (arrSyms u ++ x.rest))
    (fun r => Sym.mark :: x.S (kit.slot (.role r))) with hP0
  have hP0none : ∀ key, kit.roleOf key = none → key ≠ kit.slot .io → P0 key = x.S key := by
    intro key hk' hio'
    rw [hP0, setRoles_none kit _ _ _ hk', Function.update_of_ne hio']
  have hP0r : ∀ r, P0 (kit.slot (.role r)) = Sym.mark :: x.S (kit.slot (.role r)) := by
    intro r
    rw [hP0, setRoles_role]
  have hP0io : P0 (kit.slot .io) = arrSyms u ++ x.rest := by
    rw [hP0, setRoles_none kit _ _ _ (roleOf_none kit .io rfl), Function.update_self]
  have hctr0 : CtrOK kit.slot P0 x.k x.N1 x.G x.B :=
    ctrOK_of_eq kit hctr (hP0none _ (roleOf_none kit .ck rfl) hck_io)
      (hP0none _ (roleOf_none kit .cN1 rfl) hN1_io) (hP0none _ (roleOf_none kit .cG rfl) hG_io)
      (hP0none _ (roleOf_none kit .cB rfl) hB_io)
  -- (a) row size
  have ha : RunsIn [bodyProg kit] kit.rowsz P0
      (Function.update P0 (kit.slot .rsz) (natSyms srow ++ Sym.mark :: P0 (kit.slot .rsz)))
      (fun _ => True) (kit.C * (srow + 1)) := by
    rw [hsrow]
    exact RunsIn.of_runs (kit.rowsz_spec x.k x.N1 x.G x.B P0 hN1 hG hB hctr0) kit.rowsz_closed _
  -- (b) distribution
  have hb := RunsIn.of_runs (kit.dist_spec srow (x.N0 * x.R) u x.rest
      (Sym.mark :: P0 (kit.slot .rsz))
      (Function.update P0 (kit.slot .rsz) (natSyms srow ++ Sym.mark :: P0 (kit.slot .rsz))) hu
      hrest (termOK_mark _) (by rw [Function.update_of_ne hio_rsz, hP0io])
      (Function.update_self _ _ _)) kit.dist_closed [bodyProg kit]
  have hb' := RunsIn.congr hb (dist_state kit x.S P0 x.rest srow
    (fun r => roleBlocks W r.val srow u) hP0none hP0r) le_rfl
  -- (c) the schedule
  have hus0 : Shp (x.N0 * (x.R / W) * srow) x.w (fun r => roleBlocks W r.val srow u) := fun r =>
    ⟨roleBlocks_length W srow hW r.val r.isLt u _ (by rw [hu, hRg]),
      fun p hp => huw p (roleBlocks_mem W r.val srow u hp)⟩
  have hc := sched_runs kit hq2 hm hW s c hNF x hx hk IH (fun r => roleBlocks W r.val srow u)
    (by rw [← hsrow]; exact hus0)
  rw [← hsrow] at hc
  have hshF := runSched_shape hNF x.k x.N1 x.G x.B (x.N0 * (x.R / W)) x.w hk N.sched _
    (by rw [← hsrow]; exact hus0)
  rw [← hsrow] at hshF
  set usF := runSched q N x.k x.N1 x.G x.B N.sched (fun r => roleBlocks W r.val srow u) with husF
  -- (d) merge
  have hd := RunsIn.of_runs (kit.merge_spec (x.N0 * (x.R / W)) srow usF
      (fun r => Sym.mark :: x.S (kit.slot (.role r))) (Sym.mark :: x.S (kit.slot .rsz))
      (nodeSt kit x.S x.rest srow usF) (fun r => (hshF r).1) (fun _ => blkTerm_mark _)
      (termOK_mark _) (fun r => nodeSt_role kit _ _ _ _ r) (nodeSt_rsz kit _ _ _ _))
    kit.merge_closed [bodyProg kit]
  rw [nodeSt_io] at hd
  -- (e) pop the row size
  have hP4rsz : setRoles kit.roleOf (Function.update (nodeSt kit x.S x.rest srow usF)
      (kit.slot .io) (arrSyms (mergeBlocks W N.ρ (x.N0 * (x.R / W)) srow usF) ++ x.rest))
      (fun r => Sym.mark :: x.S (kit.slot (.role r))) (kit.slot .rsz) =
      natSyms srow ++ Sym.mark :: x.S (kit.slot .rsz) := by
    rw [setRoles_none kit _ _ _ (roleOf_none kit .rsz rfl),
      Function.update_of_ne (Ne.symm hio_rsz), nodeSt_rsz]
  have he := popDesc_runsIn kit (kit.slot .rsz) srow (x.S (kit.slot .rsz)) _ hP4rsz [bodyProg kit]
  have hall := RunsIn.seq ha (RunsIn.seq hb' (RunsIn.seq hc (RunsIn.seq hd he)))
  refine RunsIn.congr hall (merge_state kit x.S x.rest srow usF _) ?_
  -- cost
  have hsrow1 : 1 ≤ srow := by
    rw [hsrow, rowSize]
    have h1 := one_le_pow' (q := q) (by omega) (m ^ x.k)
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN1 h1) hG) h1) hB
  obtain ⟨Vr, hVr⟩ : ∃ t, t = x.N0 * (x.R / W) * srow * (x.w + 1) := ⟨_, rfl⟩
  rw [← hVr]
  have hV : vol x.v = W * Vr := by
    rw [vol_of_widths x.v x.w hvw, hvlen, hRg, hVr]; ring
  have hVW : vol x.v / W = Vr := by rw [hV, Nat.mul_div_cancel_left _ hW]
  have hvolu : vol u = vol x.v := by
    rw [vol_of_widths u x.w huw, hu, vol_of_widths x.v x.w hvw, hvlen]
  have hsum : ∑ r, vol (usF r) = vol x.v := by
    rw [hV]
    have e : ∀ r, vol (usF r) = Vr := fun r => by
      rw [vol_of_widths _ x.w (hshF r).2, (hshF r).1, hVr]
    simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsrowV : srow ≤ vol x.v := by
    rw [vol_of_widths x.v x.w hvw, hvlen]
    have h1 : 1 ≤ x.N0 * x.R := Nat.mul_le_mul hN0 hR
    calc srow = 1 * srow * 1 := by ring
      _ ≤ x.N0 * x.R * srow * (x.w + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) (by omega)
  have hbit := bitLen_le_self srow
  rw [hvolu, hsum, hVW]
  set V := vol x.v with hVdef
  set L := N.sched.length
  have hA : kit.C * (srow + 1) ≤ 2 * (kit.C * V) := by
    calc kit.C * (srow + 1) ≤ kit.C * (2 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (kit.C * V) := by ring
  have hB' : kit.C * (V + 1) ≤ 2 * (kit.C * V) := by
    calc kit.C * (V + 1) ≤ kit.C * (2 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (kit.C * V) := by ring
  have hC : L * ((kit.C + 40) * (W * Vr + srow + 1)) ≤ 3 * (L * ((kit.C + 40) * V)) := by
    calc L * ((kit.C + 40) * (W * Vr + srow + 1)) ≤ L * ((kit.C + 40) * (3 * V)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 3 * (L * ((kit.C + 40) * V)) := by ring
  have hexp : 3 * (L + 4) * (kit.C + 40) * V =
      3 * (L * ((kit.C + 40) * V)) + 12 * (kit.C * V) + 480 * V := by ring
  rw [hexp]
  omega

theorem one_le_rowSize (hq : 1 ≤ q) (k N1 G B : ℕ) (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    1 ≤ rowSize q m k N1 G B := by
  rw [rowSize]
  have h1 := one_le_pow' (q := q) hq (m ^ k)
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN1 h1) hG) h1) hB

theorem one_le_vol (hq : 1 ≤ q) (x : Inst K) (hx : Pre kit x) : 1 ≤ vol x.v := by
  obtain ⟨hN0, hR, hN1, hG, hB, _, hvlen, hvw, _, _, _⟩ := hx
  rw [vol_of_widths x.v x.w hvw, hvlen]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN0 hR)
    (one_le_rowSize hq x.k x.N1 x.G x.B hN1 hG hB)) (by omega : 1 ≤ x.w + 1)

/-- **One node** (`k ≥ 1`): `pre`, the protected inside, `post`; by `NodeCorrect` the result is
the level-`k` interchange. -/
theorem node_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s c : ℕ) (hNF : NetFacts q N s)
    (x : Inst K) (hx : Pre kit x) (hk : 1 ≤ x.k)
    (IH : ∀ y : Inst K, Pre kit y → y.k < x.k →
      RunsIn [bodyProg kit] (.recur 0) y.S (post kit y) (fun _ => True)
        (powBudget s W c y.k (vol y.v) + 2)) :
    RunsIn [bodyProg kit] (nodeProg kit) x.S (post kit x) (fun _ => True)
      ((N.sched.filter SchedOp.isCall).length * powBudget s W c (x.k - 1) (vol x.v / W) +
        (3 * (N.sched.length + 4) * (kit.C + 40) + 4 * kit.C + 2 * W + 2) * vol x.v) := by
  have hx' := hx
  obtain ⟨hN0, hR, hN1, hG, hB, hdiv, hvlen, hvw, hrest, hio, hctr⟩ := hx'
  have hWR : W ∣ x.R := dvd_trans (dvd_pow_self W (by omega)) hdiv
  have hRg : x.N0 * x.R = W * (x.N0 * (x.R / W)) := by
    rw [Nat.mul_left_comm, Nat.mul_div_cancel' hWR]
  have hck_io : kit.slot .ck ≠ kit.slot .io := slot_ne kit (by simp)
  have hN1_io : kit.slot .cN1 ≠ kit.slot .io := slot_ne kit (by simp)
  have hG_io : kit.slot .cG ≠ kit.slot .io := slot_ne kit (by simp)
  have hB_io : kit.slot .cB ≠ kit.slot .io := slot_ne kit (by simp)
  have hRt : 1 ≤ x.N0 * x.R := Nat.mul_le_mul hN0 hR
  have hV1 := one_le_vol kit (by omega) x hx
  -- (1) the outer shear `pre`
  have hlt_pre := hNF.stream_lt N.pre x.k x.N1 x.G x.B x.v.length hk
    (by rw [hvlen]; exact Dvd.intro_left _ rfl)
  set u := permByInv (N.streamMap N.pre x.k x.N1 x.G x.B) x.v with hu_def
  have hu : u.length = x.N0 * x.R * rowSize q m x.k x.N1 x.G x.B := by
    rw [hu_def, permByInv_length, hvlen]
  have huw : ∀ p ∈ u, p.length = x.w := permByInv_widths _ _ _ hlt_pre hvw
  have h1 : RunsIn [bodyProg kit] (kit.stream N.pre none) x.S
      (Function.update x.S (kit.slot .io) (arrSyms u ++ x.rest)) (fun _ => True)
      (kit.C * (vol x.v + 1)) :=
    RunsIn.of_runs (kit.stream_spec N.pre none x.k (x.N0 * x.R) x.N1 x.G x.B x.w x.v x.rest x.S
      hk hRt hN1 hG hB hvlen hvw hrest hio hctr) (kit.stream_closed _ _) _
  -- (2) the protected inside
  have hin := inner_runs kit hq2 hm hW s c hNF x hx hk IH u hu huw
  have hP : protState ((List.finRange W).map (fun w => kit.slot (.role w)))
      (Function.update x.S (kit.slot .io) (arrSyms u ++ x.rest)) =
      setRoles kit.roleOf (Function.update x.S (kit.slot .io) (arrSyms u ++ x.rest))
        (fun r => Sym.mark :: x.S (kit.slot (.role r))) := by
    rw [protState_roles]
    congr 1
    funext r
    rw [Function.update_of_ne (role_ne_slot kit r .io rfl)]
  rw [← hP] at hin
  have h2 := runsIn_protectFinCall kit.lr (role_inj kit) hin (fun i => by
    rw [setRoles_role, Function.update_of_ne (role_ne_slot kit i .io rfl)])
  set vM := mergeBlocks W N.ρ (x.N0 * (x.R / W)) (rowSize q m x.k x.N1 x.G x.B)
    (runSched q N x.k x.N1 x.G x.B N.sched
      (fun r => roleBlocks W r.val (rowSize q m x.k x.N1 x.G x.B) u)) with hvM_def
  have h2' := RunsIn.congr h2 (prot_final kit _ _
    (Function.update x.S (kit.slot .io) (arrSyms vM ++ x.rest))
    (fun r => by rw [Function.update_of_ne (role_ne_slot kit r .io rfl),
      Function.update_of_ne (role_ne_slot kit r .io rfl)])
    (fun key hk' => by rw [setRoles_none kit _ _ _ hk'])) le_rfl
  -- (3) the outer shear `post`
  have hshF := runSched_shape hNF x.k x.N1 x.G x.B (x.N0 * (x.R / W)) x.w hk N.sched
    (fun r => roleBlocks W r.val (rowSize q m x.k x.N1 x.G x.B) u)
    (fun r => ⟨roleBlocks_length W _ hW r.val r.isLt u _ (by rw [hu, hRg]),
      fun p hp => huw p (roleBlocks_mem W r.val _ u hp)⟩)
  have hvM : vM.length = x.N0 * x.R * rowSize q m x.k x.N1 x.G x.B := by
    rw [hvM_def, mergeBlocks_length W N.ρ _ _ _ (fun r => (hshF r).1), hRg]
  have hvMw : ∀ p ∈ vM, p.length = x.w := fun p hp => by
    obtain ⟨r, hr⟩ := mergeBlocks_mem W N.ρ _ _ _ hp
    exact (hshF r).2 p hr
  have hctr2 : CtrOK kit.slot (Function.update x.S (kit.slot .io) (arrSyms vM ++ x.rest))
      x.k x.N1 x.G x.B :=
    ctrOK_of_eq kit hctr (Function.update_of_ne hck_io _ _) (Function.update_of_ne hN1_io _ _)
      (Function.update_of_ne hG_io _ _) (Function.update_of_ne hB_io _ _)
  have h3 : RunsIn [bodyProg kit] (kit.stream N.post none)
      (Function.update x.S (kit.slot .io) (arrSyms vM ++ x.rest))
      (Function.update (Function.update x.S (kit.slot .io) (arrSyms vM ++ x.rest)) (kit.slot .io)
        (arrSyms (permByInv (N.streamMap N.post x.k x.N1 x.G x.B) vM) ++ x.rest))
      (fun _ => True) (kit.C * (vol vM + 1)) :=
    RunsIn.of_runs (kit.stream_spec N.post none x.k (x.N0 * x.R) x.N1 x.G x.B x.w vM x.rest _
      hk hRt hN1 hG hB hvM hvMw hrest (Function.update_self _ _ _) hctr2) (kit.stream_closed _ _) _
  rw [Function.update_idem] at h3
  have hall := RunsIn.seq h1 (RunsIn.seq h2' h3)
  have hnode : permByInv (N.streamMap N.post x.k x.N1 x.G x.B) vM =
      permByInv (swapMap q m x.k x.G x.B) x.v := by
    have := hNF.node x.k x.N0 x.R x.N1 x.G x.B x.w x.v hk hN0 hR hN1 hG hB hdiv hvlen hvw
    rw [Nat.mul_div_assoc _ hWR] at this
    exact this
  refine RunsIn.congr hall (by rw [hnode]; rfl) ?_
  -- cost
  have hvolM : vol vM = vol x.v := by
    rw [vol_of_widths vM x.w hvMw, hvM, vol_of_widths x.v x.w hvw, hvlen]
  rw [hvolM]
  set V := vol x.v with hVdef
  have hA : kit.C * (V + 1) ≤ 2 * (kit.C * V) := by
    calc kit.C * (V + 1) ≤ kit.C * (2 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (kit.C * V) := by ring
  have hWV : W ≤ W * V := Nat.le_mul_of_pos_right _ hV1
  have hexp : (3 * (N.sched.length + 4) * (kit.C + 40) + 4 * kit.C + 2 * W + 2) * V =
      3 * (N.sched.length + 4) * (kit.C + 40) * V + 4 * (kit.C * V) + 2 * (W * V) + 2 * V := by
    ring
  rw [hexp]
  omega

/-- The per-level budget constant of the Proposition A.7 recursion (from the kit constant). -/
def budgetC (kit : Kit q N K σ) : ℕ := 3 * (N.sched.length + 6) * (kit.C + 40) + 2 * W + 4

/-- **The body of the recursion** meets the instance spec within `T_k(V) = powBudget s W c k V`,
given the spec (plus the call overhead) at all smaller levels. -/
theorem body_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s : ℕ) (hNF : NetFacts q N s)
    (x : Inst K) (hx : Pre kit x)
    (IH : ∀ y : Inst K, Pre kit y → y.k < x.k →
      RunsIn [bodyProg kit] (.recur 0) y.S (post kit y) (fun _ => True)
        (powBudget s W (budgetC kit) y.k (vol y.v) + 2)) :
    RunsIn [bodyProg kit] (bodyProg kit) x.S (post kit x) (fun _ => True)
      (powBudget s W (budgetC kit) x.k (vol x.v)) := by
  have hx' := hx
  obtain ⟨hN0, hR, hN1, hG, hB, _, hvlen, hvw, hrest, hio, hctr⟩ := hx'
  have hctr' := hctr
  obtain ⟨r1, _, _, _, t1, _, _, _, e1, _, _, _⟩ := hctr'
  have hV1 := one_le_vol kit (by omega) x hx
  have hz := RunsIn.of_runs_liftRegs kit.lr (runs_zeroTest (kit.slot .ck) x.k r1 x.S t1 e1)
    (by simp [Prog.Closed, zeroTest, peekR, Prog.FreeBelow]) [bodyProg kit]
  by_cases h0 : x.k = 0
  · -- level 0: the base kernel
    have hz' : RunsIn [bodyProg kit] ((peekR (kit.slot .ck)).liftRegs kit.lr) x.S x.S
        (fun v => optIsBit (kit.lr.get v) = false) 1 :=
      RunsIn.mono hz (fun v hv => by rw [hv, h0]; rfl) le_rfl
    have hbase := RunsIn.of_runs (kit.base_spec (x.N0 * x.R) x.N1 x.G x.B x.w x.v x.rest x.S
      (Nat.mul_le_mul hN0 hR) hN1 hG hB (by rw [hvlen, h0]) hvw hrest hio (by rw [← h0]; exact hctr))
      kit.base_closed [bodyProg kit]
    have hall := RunsIn.ite_false (Pt := nodeProg kit) hz' hbase
    refine RunsIn.congr hall (by rw [post, h0]) ?_
    rw [h0, powBudget_zero]
    have hc : 2 * kit.C + 2 ≤ budgetC kit := by unfold budgetC; nlinarith
    have : (2 * kit.C + 2) * vol x.v ≤ budgetC kit * vol x.v := Nat.mul_le_mul_right _ hc
    have hexp : (2 * kit.C + 2) * vol x.v = kit.C * vol x.v + kit.C * vol x.v + 2 * vol x.v := by
      ring
    have hCV : kit.C ≤ kit.C * vol x.v := Nat.le_mul_of_pos_right _ hV1
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · -- level `k ≥ 1`: a node
    have hk : 1 ≤ x.k := Nat.one_le_iff_ne_zero.2 h0
    have hz' : RunsIn [bodyProg kit] ((peekR (kit.slot .ck)).liftRegs kit.lr) x.S x.S
        (fun v => optIsBit (kit.lr.get v) = true) 1 :=
      RunsIn.mono hz (fun v hv => by rw [hv, decide_eq_false h0]; rfl) le_rfl
    have hnode := node_runs kit hq2 hm hW s (budgetC kit) hNF x hx hk IH
    refine RunsIn.mono (RunsIn.ite_true (Pf := kit.base) hz' hnode) (fun _ _ => trivial) ?_
    obtain ⟨k', hk'⟩ : ∃ k', x.k = k' + 1 := ⟨x.k - 1, by omega⟩
    rw [hk', powBudget_succ, show k' + 1 - 1 = k' by omega]
    have hcalls : (N.sched.filter SchedOp.isCall).length * powBudget s W (budgetC kit) k'
        (vol x.v / W) ≤ s * powBudget s W (budgetC kit) k' (vol x.v / W) :=
      Nat.mul_le_mul_right _ hNF.calls_le
    have hexp : budgetC kit * vol x.v = (3 * (N.sched.length + 4) * (kit.C + 40) + 4 * kit.C +
        2 * W + 2) * vol x.v + (2 * kit.C + 242) * vol x.v := by
      unfold budgetC; ring
    have h242 : 242 ≤ (2 * kit.C + 242) * vol x.v :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ hV1)
    omega

/-- **The Proposition A.7 program meets the instance spec at every level** (`runs_fix`), with cost
`powBudget s W c k V + 2`, `c = budgetC kit`. -/
theorem kit_runs (hq2 : 2 ≤ q) (hm : 2 ≤ m) (hW : 0 < W) (s : ℕ) (hNF : NetFacts q N s)
    (x : Inst K) (hx : Pre kit x) :
    Runs (c5Prog kit) x.S (post kit x) (fun _ => True)
      (powBudget s W (budgetC kit) x.k (vol x.v) + 2) := by
  have key := runs_fix (b := bodyProg kit) (X := {y : Inst K // Pre kit y}) (fun y => y.1.k)
    (S := fun y => y.1.S) (S' := fun y => post kit y.1) (Q := fun _ _ => True)
    (T := fun y => powBudget s W (budgetC kit) y.1.k (vol y.1.v))
    (fun y ih => body_runs kit hq2 hm hW s hNF y.1 y.2 (fun z hz hlt => ih ⟨z, hz⟩ hlt))
  exact key ⟨x, hx⟩

end Node

end SubNLogN.Machine.C5
