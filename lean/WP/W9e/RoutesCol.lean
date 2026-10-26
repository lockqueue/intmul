import WP.W9e.Output

/-!
# WP.W9e.RoutesCol — Q3+Q4, one column: isolate, route, rescale

`colBody = partA; partB; partC`, for column `u2` of the `r × t1` buffer on `W0`:

* `partA`: copy `t1` (on `t1s`) to the counter `cnt`; move `t1` records `W0 → x` (`moveRecs`, a
  counted record loop), then `x → x2` (second reversal): `x2 = ⟦col⟧ ++ guard`.
* `partB`: W4 `oddStrideFactor (m_t1, u2) → ws`; W4 `oddRoute .down .down` from `x2` onto `y`
  (`b = 0` on `bs`); drop the guard and the factor.
* `partC`: `rscLoop y acc`: rescale (`pChild → pSub`) and accumulate the routed column on `acc`;
  pop the guard; `u2 := u2 + 1`.
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

theorem natSyms_zero_append (l : List Sym) : natSyms 0 ++ l = l := by
  rw [natSyms_zero, List.nil_append]

theorem rscFree_y : RscFree .y := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem rscFree_acc : RscFree .acc := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Counted record mover -/

section MoveRecs

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- Move as many records as the counter on `cnt` says from `w0` onto `x` (reversed). -/
def moveRecs : Prog Stk (fun _ => Sym) σ :=
  peekLoop lS .cnt optIsBit (.seq (sym lS (moveRec .w0 .x)) (sym lS (dec .cnt .tmp)))

theorem upd3_upd3 {K : Type} [DecidableEq K] (S : K → List Sym) {a b c : K}
    (v1 v2 v3 v4 v5 v6 : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update S a v1) b v2) c v3) a v4) b v5) c v6 =
    Function.update (Function.update (Function.update S a v4) b v5) c v6 := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem rs_moveRecs (w : ℕ) (zs rest : List (ℤ × ℤ)) (C0 X : List Sym) (S : Stk → List Sym)
    (hw : ∀ z ∈ zs, EntryW w z) (hcnt : S .cnt = natSyms zs.length ++ Sym.mark :: C0)
    (hw0 : S .w0 = blkE (zs ++ rest)) (hx : S .x = X) :
    Runs (moveRecs lS) S
      (Function.update (Function.update (Function.update S .w0 (blkE rest)) .x
        ((blkE zs).reverse ++ X)) .cnt (Sym.mark :: C0))
      (fun _ => True) (zs.length * (3 * eb w + 6 * bitLen zs.length + 10) + 2) := by
  set Si : ℕ → Stk → List Sym := fun i => Function.update (Function.update (Function.update S
    .w0 (blkE (zs.drop i ++ rest))) .x ((blkE (zs.take i)).reverse ++ X)) .cnt
    (natSyms (zs.length - i) ++ Sym.mark :: C0) with hSi
  have hS0 : Si 0 = S := by
    funext k
    cases k <;> simp [hSi, hw0, hx, hcnt, blkE_nil]
  have hSn : Si zs.length = Function.update (Function.update (Function.update S .w0 (blkE rest))
      .x ((blkE zs).reverse ++ X)) .cnt (Sym.mark :: C0) := by
    simp only [hSi, List.drop_length, List.take_length, List.nil_append, Nat.sub_self,
      natSyms_zero_append]
  have hcore : ∀ i < zs.length, Runs (.seq (sym lS (moveRec .w0 .x)) (sym lS (dec .cnt .tmp)))
      (Si i) (Si (i + 1)) (fun _ => True) (3 * eb w + 6 * bitLen zs.length + 8) := by
    intro i hi
    have hd : zs.drop i = zs[i] :: zs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hw0i : Si i .w0 = entrySyms zs[i] ++ blkE (zs.drop (i + 1) ++ rest) := by
      simp only [hSi]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, hd, List.cons_append, blkE_cons]
    have hxi : Si i .x = (blkE (zs.take i)).reverse ++ X := by
      simp only [hSi]
      rw [Function.update_of_ne (by decide), Function.update_self]
    have hci : Si i .cnt = natSyms (zs.length - i - 1 + 1) ++ Sym.mark :: C0 := by
      simp only [hSi]
      rw [Function.update_self, show zs.length - i - 1 + 1 = zs.length - i by omega]
    have m1 := rs_moveRec lS (src := Stk.w0) (dst := .x) (by decide) (entrySyms zs[i])
      (blkE (zs.drop (i + 1) ++ rest)) (Si i) (entrySyms_recOK _) hw0i
    set T1 := Function.update (Function.update (Si i) .w0 (blkE (zs.drop (i + 1) ++ rest))) .x
      ((entrySyms zs[i]).reverse ++ Si i .x) with hT1
    have m2 := rs_dec lS (k := Stk.cnt) (t := .tmp) (by decide) (zs.length - i - 1)
      (Sym.mark :: C0) T1 (TermOK.cons (by rfl) _)
      (by rw [hT1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hci])
    refine runs_post (runs_seq m1 m2) ?_ ?_
    · clear m1 m2
      have ht : zs.take (i + 1) = zs.take i ++ [zs[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]
        rfl
      have hB : (entrySyms zs[i]).reverse ++ ((blkE (zs.take i)).reverse ++ X) =
          (blkE (zs.take (i + 1))).reverse ++ X := by
        rw [ht, blkE_append, blkE_cons, blkE_nil, List.append_nil, List.reverse_append,
          List.append_assoc]
      have hni : zs.length - i - 1 = zs.length - (i + 1) := by omega
      rw [hT1, hxi]
      simp only [hSi]
      rw [upd3_upd3 S, hB, hni]
    · have h1 := length_entrySyms_le (hw zs[i] (List.getElem_mem hi))
      have h2 : bitLen (zs.length - i - 1 + 1) ≤ bitLen zs.length := bitLen_mono (by omega)
      omega
  have hcont : ∀ i < zs.length, optIsBit (Si i .cnt).head? = true := by
    intro i hi
    simp only [hSi, Function.update_self]
    rw [natSyms_pos (zs.length - i) (by omega)]
    rfl
  have hstp : optIsBit (Si zs.length .cnt).head? = false := by
    simp only [hSi, Function.update_self, Nat.sub_self, natSyms_zero_append]
    rfl
  have hl := runs_peekLoop lS .cnt optIsBit _ (3 * eb w + 6 * bitLen zs.length + 8) zs.length Si
    hcore hcont hstp
  rw [hS0, hSn] at hl
  refine runs_mono hl (fun _ _ => trivial) ?_
  have : 3 * eb w + 6 * bitLen zs.length + 8 + 2 = 3 * eb w + 6 * bitLen zs.length + 10 := by
    omega
  rw [this]

end MoveRecs

/-! ## The three parts of a column -/

section Parts

variable {σ RF RR Rh Rp : Type} (lS : Lens σ (Option Sym)) (lF : Lens σ RF) (lR : Lens σ RR)
  (lH : Lens σ Rh) (lP : Lens σ Rp)
  {mF mR mh mp : ℕ} (PF : Prog (Loc 3 mF) (fun _ => Sym) RF) (hmF : mF ≤ 4)
  (PR : Prog (Loc 5 mR) (fun _ => Sym) RR) (hmR : mR ≤ 4)
  (Ph : Prog (Loc 2 mh) (fun _ => Sym) Rh) (hmh : mh ≤ 4)
  (Pp : Prog (Loc 3 mp) (fun _ => Sym) Rp) (hmp : mp ≤ 4)

/-- Part A: isolate the next column (`t1` records) on `x2`, above a guard. -/
def partA : Prog Stk (fun _ => Sym) σ :=
  .seq (sym lS (copyBlock .t1s .cnt .tmp)) <| .seq (sym lS (pushC .x symGuard)) <|
  .seq (moveRecs lS) <| .seq (sym lS (pushC .x2 symGuard)) (sym lS (moveTo symGuard .x .x2))

/-- Part B: odd-stride factor and route `x2 → y`. -/
def partB : Prog Stk (fun _ => Sym) σ :=
  .seq ((PF.mapStk (embL (nm3 .ks .u .ws) (scr hmF))).liftRegs lF) <|
  .seq (sym lS (pushC .y symGuard)) <|
  .seq ((PR.mapStk (embL (nm5 .x2 .y .ks .ws .bs) (scr hmR))).liftRegs lR) <|
  .seq (sym lS (popR .x2)) (sym lS (dropBits .ws))

/-- Part C: rescale the routed column onto `acc`; next column index. -/
def partC : Prog Stk (fun _ => Sym) σ :=
  .seq (rscLoop lS lH lP Ph hmh Pp hmp .y .acc (some symGuard)) <|
  .seq (sym lS (popR .y)) (sym lS (inc .u .tmp))

/-- One column. -/
def colBody : Prog Stk (fun _ => Sym) σ :=
  .seq (partA lS) (.seq (partB lS lF lR PF hmF PR hmR) (partC lS lH lP Ph hmh Pp hmp))

theorem closed_colBody (hF : PF.Closed) (hR : PR.Closed) (hh : Ph.Closed) (hp : Pp.Closed) :
    (colBody lS lF lR lH lP PF hmF PR hmR Ph hmh Pp hmp).Closed := by
  simp only [colBody, partA, partB, partC, moveRecs, closed_seq]
  exact ⟨⟨(closed_sym _ _).2 (closed_copyBlock _ _ _), trivial,
      (closed_peekLoop _ _ _ _).2 ⟨(closed_sym _ _).2 (closed_moveRec _ _),
        (closed_sym _ _).2 (closed_dec _ _)⟩, trivial, (closed_sym _ _).2 (closed_moveTo _ _ _)⟩,
    ⟨(closed_call _ _ _).2 hF, trivial, (closed_call _ _ _).2 hR, trivial,
      (closed_sym _ _).2 (closed_dropBits _)⟩,
    closed_rscLoop _ _ _ _ _ hh hp _ _ _, trivial, (closed_sym _ _).2 (closed_inc _ _)⟩

theorem rs_partA (w t1 : ℕ) (col rest : List (ℤ × ℤ)) (T0 C0 : List Sym) (S : Stk → List Sym)
    (hcol : col.length = t1) (hw : ∀ z ∈ col, EntryW w z)
    (ht1s : S .t1s = natSyms t1 ++ Sym.mark :: T0) (hcnt : S .cnt = Sym.mark :: C0)
    (hw0 : S .w0 = blkE (col ++ rest)) :
    Runs (partA lS) S
      (Function.update (Function.update S .w0 (blkE rest)) .x2 (blkE col ++ symGuard :: S .x2))
      (fun _ => True) (t1 * (6 * eb w + 6 * bitLen t1 + 10) + 7 * bitLen t1 + 14) := by
  have a1 := rs_copy lS (src := Stk.t1s) (dst := .cnt) (tmp := .tmp) (by decide) (by decide)
    (by decide) t1 (Sym.mark :: T0) S (TermOK.cons (by rfl) _) ht1s
  set S1 := Function.update S .cnt (natSyms t1 ++ S .cnt) with hS1
  have a2 := rs_push lS .x symGuard S1
  set S2 := Function.update S1 .x (symGuard :: S1 .x) with hS2
  have a3 := rs_moveRecs lS w col rest C0 (symGuard :: S .x) S2 hw
    (by simp [hS2, hS1, hcnt, hcol]) (by simp [hS2, hS1, hw0]) (by simp [hS2, hS1])
  rw [hcol] at a3
  set S3 := Function.update (Function.update (Function.update S2 .w0 (blkE rest)) .x
    ((blkE col).reverse ++ symGuard :: S .x)) .cnt (Sym.mark :: C0) with hS3
  have a4 := rs_push lS .x2 symGuard S3
  set S4 := Function.update S3 .x2 (symGuard :: S3 .x2) with hS4
  have a5 := rs_moveTo lS (src := Stk.x) (dst := .x2) (by decide) symGuard (blkE col).reverse
    (S .x) S4 (by rw [List.mem_reverse]; exact tag_not_mem_blkE _ _) (by simp [hS4, hS3])
  refine runs_post (runs_seq a1 (runs_seq a2 (runs_seq a3 (runs_seq a4 a5)))) ?_ ?_
  · clear a1 a2 a3 a4 a5
    funext k
    cases k <;> simp [hS4, hS3, hS2, hS1, hcnt]
  · have hb := length_blkE_le w col hw
    rw [hcol] at hb
    have hrl : (blkE col).reverse.length = (blkE col).length := List.length_reverse
    have : t1 * (6 * eb w + 6 * bitLen t1 + 10) =
        t1 * (3 * eb w + 6 * bitLen t1 + 10) + 3 * (t1 * eb w) := by ring
    omega

theorem rs_partB {CF CR : ℕ} (hF : OfSpec PF CF) (hR : OrSpec PR CR) (w k u2 : ℕ)
    (col : List (ℤ × ℤ)) (X2 K0 U0 W0 B0 : List Sym) (S : Stk → List Sym)
    (hcol : col.length = 2 ^ k) (hw : ∀ z ∈ col, EntryW w z)
    (hx2 : S .x2 = blkE col ++ symGuard :: X2) (hks : S .ks = natSyms k ++ Sym.mark :: K0)
    (hu : S .u = natSyms u2 ++ Sym.mark :: U0) (hws : S .ws = Sym.mark :: W0)
    (hbs : S .bs = Sym.mark :: B0) :
    Runs (partB lS lF lR PF hmF PR hmR) S
      (Function.update (Function.update S .x2 X2) .y
        (blkE (oddRouteL k (TMFw.Contracts.computableOddStrideFactor k u2) 0 col) ++
          symGuard :: S .y))
      (fun _ => True) (CF * ((k + 1) ^ 2 + bitLen u2) + CR * (2 ^ k * eb w + 1) * (k + 1) +
        3 * k + 8) := by
  set wf := TMFw.Contracts.computableOddStrideFactor k u2 with hwf
  have hok3 := nm3_ok (a := Stk.ks) (b := .u) (c := .ws) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) (by rfl)
  have b1 := rs_ofCall hF lF hmF (embL_scr_inj hmF hok3.1 hok3.2) k u2 (Sym.mark :: K0)
    (Sym.mark :: U0) S (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _) hks hu
  rw [← hwf] at b1
  set S1 := Function.update S .ws (natSyms wf ++ S .ws) with hS1
  have b2 := rs_push lS .y symGuard S1
  set S2 := Function.update S1 .y (symGuard :: S1 .y) with hS2
  have hok5 := nm5_ok (a := Stk.x2) (b := .y) (c := .ks) (d := .ws) (e := .bs) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have hparam : OddRouteParam k wf := computableOddStrideFactor_param k u2
  have b3 := rs_orCall hR lR hmR (embL_scr_inj hmR hok5.1 hok5.2) k wf 0 (col.map entrySyms)
    (symGuard :: X2) (Sym.mark :: K0) (Sym.mark :: W0) (Sym.mark :: B0) S2 hparam
    (Nat.two_pow_pos k) (by rw [List.length_map, hcol])
    (fun rc hrc => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hrc
      exact entrySyms_recOK z)
    (fun d hd => by
      simp only [List.head?_cons, Option.some.injEq] at hd
      subst hd
      exact ⟨rfl, by decide⟩)
    (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _) (TermOK.cons (by rfl) _)
    (by simp [hS2, hS1, hx2, blkE]) (by simp [hS2, hS1, hks]) (by simp [hS2, hS1, hws])
    (by simp [hS2, hS1, hbs, natSyms_zero])
  have hval : blk .down (oddRouteL k wf 0 (col.map entrySyms)) = blkE (oddRouteL k wf 0 col) := by
    rw [oddRouteL_map _ _ _ _ _ hcol]
    rfl
  rw [hval] at b3
  set S3 := Function.update (Function.update S2 .x2 (symGuard :: X2)) .y
    (blkE (oddRouteL k wf 0 col) ++ S2 .y) with hS3
  have b4 := rs_pop lS .x2 symGuard X2 S3 (by simp [hS3])
  set S4 := Function.update S3 .x2 X2 with hS4
  have b5 := rs_dropBits lS .ws wf (Sym.mark :: W0) S4 (TermOK.cons (by rfl) _)
    (by simp [hS4, hS3, hS2, hS1, hws])
  refine runs_post (runs_seq b1 (runs_seq b2 (runs_seq b3 (runs_seq (runs_weak b4) b5)))) ?_ ?_
  · clear b1 b2 b3 b4 b5
    funext k'
    cases k' <;> simp [hS4, hS3, hS2, hS1, hws]
  · have hbw : bitLen wf ≤ k + 1 := bitLen_le_of_lt_two_pow hparam.2
    have hb := length_blkE_le w col hw
    rw [hcol] at hb
    have hlen : (blk .down (col.map entrySyms)).length = (blkE col).length := rfl
    have hc : CR * ((blk .down (col.map entrySyms)).length + 1) * (k + 1) ≤
        CR * (2 ^ k * eb w + 1) * (k + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    omega

theorem rs_partC {Ch Cp : ℕ} (hPh : ShlSpec Ph Ch) (hPp : SplitSpec Pp Cp) (pi po w u2 : ℕ)
    (zs : List (ℤ × ℤ)) (Y0 U0 : List Sym) (S : Stk → List Sym) (hok : RscOK pi po S)
    (hy : S .y = blkE zs ++ symGuard :: Y0) (hu : S .u = natSyms u2 ++ Sym.mark :: U0)
    (hw : ∀ z ∈ zs, EntryW w z ∧ EntryW w (gRescale pi po z)) :
    Runs (partC lS lH lP Ph hmh Pp hmp) S
      (Function.update (Function.update (Function.update S .y Y0) .acc
        ((blkE (zs.map (gRescale pi po))).reverse ++ S .acc)) .u
        (natSyms (u2 + 1) ++ Sym.mark :: U0))
      (fun _ => True) (zs.length * (recCost Ch Cp w pi po + 2) + 6 * bitLen u2 + 13) := by
  have c1 := rs_rscLoop lS lH lP hmh hmp hPh hPp rscFree_y rscFree_acc (by decide) pi po w
    (some symGuard) sgn_ne_guard zs (symGuard :: Y0) S hok hy rfl hw
  set S1 := Function.update (Function.update S .y (symGuard :: Y0)) .acc
    ((blkE (zs.map (gRescale pi po))).reverse ++ S .acc) with hS1
  have c2 := rs_pop lS .y symGuard Y0 S1 (by simp [hS1])
  set S2 := Function.update S1 .y Y0 with hS2
  have c3 := rs_inc lS (k := Stk.u) (t := .tmp) (by decide) u2 (Sym.mark :: U0) S2
    (TermOK.cons (by rfl) _) (by simp [hS2, hS1, hu])
  refine runs_post (runs_seq c1 (runs_seq (runs_weak c2) c3)) ?_ (by omega)
  clear c1 c2 c3
  funext k
  cases k <;> simp [hS2, hS1]

end Parts

#assert_std_axioms natSyms_zero_append rscFree_y rscFree_acc upd3_upd3 rs_moveRecs closed_colBody rs_partA
  rs_partB rs_partC

end WP.W9e
