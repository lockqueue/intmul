/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseDefs
import SubNLogN.Machine.Layer.DrvPad

/-!
# Layer driver post-phase: unpadding (`Machine/Layer/DrvUnpad.lean`)

**Scope (honest summary).** Proof of `DrvUnpadStmt` (`Machine/Layer/DrvPhaseDefs.lean`;
Section A.6 (`sec:transfer-layer`), the inverse of `DrvPadStmt`): `SubNLogN.Machine.Layer.drvUnpad_holds`,
no hypotheses. Helpers live in `SubNLogN.Machine.Layer.DrvPadDescAux` (shared with `DrvPad.lean`).

**The program** `unpadProg` (one `Option Sym` register, private scratch `Fin 5`): floors on `Y, Tmp,
Cnt`; while the next array symbol is a record symbol, one block: copy `N0` to `Cnt` and move `N0`
records to `Y` (`runs_moveRecsU`), copy `Npad` to `Cnt` and drop `Npad` records (`dropRec` = Pass E
up to `sep`, then pop the `sep`; `runs_dropRecs`), peek the array; finally `passR` moves `Y` back
and the floors are removed. When `N0 + Npad = 0` every block is empty and input = output = `rest`;
this case is reduced to the empty block list.

**Cost** (`runs_unpadProg`): at most `40·(V_in + (#blocks + 1)·(bitLen N0 + bitLen Npad + 1))`
(`24·` the input volume for the loop via the potential `upot`, `8·V_out + 2 ≤ 8·V_in + 2` for the
final `passR`, per-block counter overhead `≤ 7·(bitLen N0 + bitLen Npad) + 19`).
-/

namespace SubNLogN.Machine.Layer.DrvPadDescAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

/-! ## Layout and programs of the unpadding kernel -/

/-- Private scratch of the unpadding kernel. -/
abbrev UE : Type := Fin 5

/-- Stacks of the unpadding kernel. -/
abbrev UK : Type := KLoc (Fin 3) UE

abbrev uA : UK := .inl 0
abbrev uN0 : UK := .inl 1
abbrev uNp : UK := .inl 2
abbrev uY : UK := .inr 0
abbrev uTmp : UK := .inr 1
abbrev uCnt : UK := .inr 2
abbrev uT : UK := .inr 3
abbrev uT2 : UK := .inr 4

/-- Drop one record (payload up to `sep`, then the `sep`). -/
def dropRec : SProg UK := .seq (passE .sep uA) (popR uA)

/-- One block: keep `N0` records (moved to `Y`), drop `Npad` records, peek the array. -/
def unpadBody : SProg UK :=
  .seq (copyBlock uN0 uCnt uT2) (.seq (countdown lid uCnt uT (passRBody .mark uA uTmp uY))
    (.seq (copyBlock uNp uCnt uT2) (.seq (countdown lid uCnt uT dropRec) (peekR uA))))

/-- Floors on the private stacks with arbitrary content. -/
def ufloors : SProg UK := .seq (pushC uY .mark) (.seq (pushC uTmp .mark) (pushC uCnt .mark))

/-- Remove the floors. -/
def uunfloors : SProg UK := .seq (popR uY) (.seq (popR uTmp) (popR uCnt))

/-- **The unpadding kernel.** -/
def unpadProg : SProg UK :=
  .seq ufloors (.seq (.seq (peekR uA) (.loop isRecSym unpadBody))
    (.seq (passR .mark .mark uY uTmp uA) uunfloors))

theorem closed_copyBlockU (a b c : UK) : (copyBlock a b c).Closed := by
  simp [copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody, restoreR, pushC, popR,
    pushR, Prog.Closed, Prog.FreeBelow, Lib.skip]

theorem closed_pushCU (k : UK) (x : Sym) : (pushC k x).Closed := by
  simp [pushC, Prog.Closed, Prog.FreeBelow]

theorem closed_popRU (k : UK) : (popR k).Closed := by
  simp [popR, Prog.Closed, Prog.FreeBelow]

theorem closed_peekRU (k : UK) : (peekR k).Closed := by
  simp [peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_dropRec : dropRec.Closed := ⟨closed_passE _ _, closed_popRU _⟩

theorem closed_unpadBody : unpadBody.Closed :=
  ⟨closed_copyBlockU _ _ _, closed_countdown lid uCnt uT (closed_passRBody _ _ _ _),
    closed_copyBlockU _ _ _, closed_countdown lid uCnt uT closed_dropRec, closed_peekRU _⟩

theorem closed_unpadProg : unpadProg.Closed :=
  ⟨⟨closed_pushCU _ _, closed_pushCU _ _, closed_pushCU _ _⟩, ⟨closed_peekRU _, closed_unpadBody⟩,
    closed_passR _ _ _ _ _, ⟨closed_popRU _, closed_popRU _, closed_popRU _⟩⟩

theorem runsIn_pushCU (k : UK) (x : Sym) (S : UK → List Sym) (ρ : List (SProg UK)) :
    RunsIn ρ (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  RunsIn.of_runs (runs_pushC k x S) (closed_pushCU k x) ρ

theorem runsIn_popRU (k : UK) (S : UK → List Sym) (d : Sym) (tl : List Sym) (hS : S k = d :: tl)
    (ρ : List (SProg UK)) :
    RunsIn ρ (popR k) S (Function.update S k tl) (fun _ => True) 1 :=
  RunsIn.of_runs (runs_popR k S d tl hS) (closed_popRU k) ρ

theorem runsIn_peekRU (k : UK) (S : UK → List Sym) (ρ : List (SProg UK)) :
    RunsIn ρ (peekR k) S S (fun v => v = (S k).head?) 1 :=
  RunsIn.of_runs (FramePassRAux.runs_peekR_eq k S _ rfl) (closed_peekRU k) ρ

theorem runsIn_copyBlockU {src dst tmp : UK} (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (n : ℕ) (rest : List Sym) (hrest : TermOK rest) (S : UK → List Sym)
    (hS : S src = natSyms n ++ rest) (ρ : List (SProg UK)) :
    RunsIn ρ (copyBlock src dst tmp) S (Function.update S dst (natSyms n ++ S dst))
      (fun _ => True) (7 * bitLen n + 7) :=
  RunsIn.of_runs (Runs.of_eval fun v =>
    ⟨_, _, copyBlock_eval hsd hst hdt [] v (encodeNat n) rest S hrest hS, trivial, le_rfl⟩)
    (closed_copyBlockU src dst tmp) ρ


/-- **The records of a block** move from the array to `Y` (record order reversed on `Y`, each
record's symbol order preserved); the counter `|ps|` on `Cnt` is consumed. -/
theorem runs_moveRecsU (ps : List (List Bool)) (tail ct tt : List Sym) (hct : TermOK ct)
    (S : UK → List Sym) (hA : S uA = arrSyms ps ++ tail) (hC : S uCnt = natSyms ps.length ++ ct)
    (hTmp : S uTmp = Sym.mark :: tt) (ρ : List (SProg UK)) :
    RunsIn ρ (countdown lid uCnt uT (passRBody .mark uA uTmp uY)) S
      (Function.update (Function.update (Function.update S uA tail) uY
        (arrSyms ps.reverse ++ S uY)) uCnt ct)
      (fun _ => True) (24 * (arrSyms ps).length + 2) := by
  set L := ps.length with hL
  set Φ : ℕ → ℕ := fun j => 8 * (arrSyms (ps.drop (L - j))).length with hΦ
  have key := runsIn_countdown (ρ := ρ) lid (c := uCnt) (t := uT) (by decide)
    (body := passRBody .mark uA uTmp uY) L ct hct
    (fun j => Function.update (Function.update S uA (arrSyms (ps.drop (L - j)) ++ tail)) uY
      (arrSyms (ps.take (L - j)).reverse ++ S uY))
    (fun j => Φ (j + 1) - Φ j) (fun j hj => by
      have hlt : L - (j + 1) < ps.length := by omega
      have hdrop : ps.drop (L - (j + 1)) = ps[L - (j + 1)] :: ps.drop (L - j) := by
        rw [List.drop_eq_getElem_cons hlt]
        congr 2
        omega
      have htake : ps.take (L - j) = ps.take (L - (j + 1)) ++ [ps[L - (j + 1)]] := by
        rw [show L - j = L - (j + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl
      set X := Function.update (Function.update (Function.update S uA
        (arrSyms (ps.drop (L - (j + 1))) ++ tail)) uY
        (arrSyms (ps.take (L - (j + 1))).reverse ++ S uY)) uCnt (natSyms (j + 1) ++ ct) with hX
      have hXA : X uA = recSyms ps[L - (j + 1)] ++ (arrSyms (ps.drop (L - j)) ++ tail) := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self, hdrop, FramePassRAux.arrSyms_cons, List.append_assoc]
      have hXT : X uTmp = Sym.mark :: tt := by
        rw [hX, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hTmp]
      have hb := runs_passRBody (gt := Sym.mark) (src := uA) (tmp := uTmp) (dst := uY)
        (by decide) (by decide) (by decide) rfl ps[L - (j + 1)] (arrSyms (ps.drop (L - j)) ++ tail)
        tt X hXA hXT
      refine RunsIn.mono (RunsIn.congr (RunsIn.of_runs hb (closed_passRBody _ _ _ _) ρ) ?_ ?_)
        (fun _ _ => trivial) le_rfl
      · funext k
        simp only [hX, Function.update_apply, htake, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.singleton_append, FramePassRAux.arrSyms_cons,
          List.append_assoc]
        clear hb hXA hXT hX
        split_ifs <;> simp_all
      · simp only [hΦ]
        rw [hdrop, FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms]
        omega)
  have hinit : Function.update (Function.update (Function.update S uA
      (arrSyms (ps.drop (L - L)) ++ tail)) uY (arrSyms (ps.take (L - L)).reverse ++ S uY)) uCnt
      (natSyms L ++ ct) = S := by
    funext k
    simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.reverse_nil,
      FramePassRAux.arrSyms_nil, List.nil_append, Function.update_apply]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) (fun _ _ => trivial) le_rfl
  · simp only [Nat.sub_zero, List.drop_length, FramePassRAux.arrSyms_nil, List.nil_append,
      List.take_length, hL]
  · have h := countdownCost_le (fun j => Φ (j + 1) - Φ j) L
    have hsum := sum_telescope Φ (fun j => by
      simp only [hΦ]
      have := length_arrSyms_drop_mono ps (show L - (j + 1) ≤ L - j by omega)
      omega) 0 L
    simp only [Nat.add_zero, Nat.zero_mul] at hsum
    have hsum' : ((List.range L).map fun j => Φ (j + 1) - Φ j).sum = Φ L - Φ 0 := by
      rw [← hsum]
    have hΦL : Φ L = 8 * (arrSyms ps).length := by simp [hΦ]
    have hΦ0 : Φ 0 = 0 := by simp [hΦ, hL, FramePassRAux.arrSyms_nil]
    have hlen := length_le_length_arrSyms ps
    rw [hsum', hΦL, hΦ0] at h
    omega



/-- **One record dropped** from the array. -/
theorem runs_dropRec (p : List Bool) (tail : List Sym) (S : UK → List Sym)
    (hA : S uA = recSyms p ++ tail) (ρ : List (SProg UK)) :
    RunsIn ρ dropRec S (Function.update S uA tail) (fun _ => True) (3 * p.length + 3) := by
  have e1 := RunsIn.of_runs (runs_passE (g := Sym.sep) (src := uA) (p.map Sym.bit) tail
    (FramePassRAux.sep_not_mem_bits p) S (by rw [hA]; simp [recSyms])) (closed_passE _ _) ρ
  have e2 := runsIn_popRU uA (Function.update S uA (Sym.sep :: tail)) Sym.sep tail
    (Function.update_self _ _ _) ρ
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq e1 e2) ?_ ?_) (fun _ _ => trivial) le_rfl
  · rw [Function.update_idem]
  · simp only [List.length_map]
    omega

/-- **`|qs|` records dropped** from the array; the counter on `Cnt` is consumed. -/
theorem runs_dropRecs (qs : List (List Bool)) (tail ct : List Sym) (hct : TermOK ct)
    (S : UK → List Sym) (hA : S uA = arrSyms qs ++ tail) (hC : S uCnt = natSyms qs.length ++ ct)
    (ρ : List (SProg UK)) :
    RunsIn ρ (countdown lid uCnt uT dropRec) S
      (Function.update (Function.update S uA tail) uCnt ct) (fun _ => True)
      (19 * (arrSyms qs).length + 2) := by
  set L := qs.length with hL
  set Φ : ℕ → ℕ := fun j => 3 * (arrSyms (qs.drop (L - j))).length with hΦ
  have key := runsIn_countdown (ρ := ρ) lid (c := uCnt) (t := uT) (by decide) (body := dropRec)
    L ct hct (fun j => Function.update S uA (arrSyms (qs.drop (L - j)) ++ tail))
    (fun j => Φ (j + 1) - Φ j) (fun j hj => by
      have hlt : L - (j + 1) < qs.length := by omega
      have hdrop : qs.drop (L - (j + 1)) = qs[L - (j + 1)] :: qs.drop (L - j) := by
        rw [List.drop_eq_getElem_cons hlt]
        congr 2
        omega
      set X := Function.update (Function.update S uA (arrSyms (qs.drop (L - (j + 1))) ++ tail))
        uCnt (natSyms (j + 1) ++ ct) with hX
      have hXA : X uA = recSyms qs[L - (j + 1)] ++ (arrSyms (qs.drop (L - j)) ++ tail) := by
        rw [hX, Function.update_of_ne (by decide), Function.update_self, hdrop,
          FramePassRAux.arrSyms_cons, List.append_assoc]
      refine RunsIn.mono (RunsIn.congr (runs_dropRec _ _ X hXA ρ) ?_ ?_) (fun _ _ => trivial)
        le_rfl
      · funext k
        simp only [hX, Function.update_apply]
        clear hXA hX
        split_ifs <;> simp_all
      · simp only [hΦ]
        rw [hdrop, FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms]
        omega)
  have hinit : Function.update (Function.update S uA (arrSyms (qs.drop (L - L)) ++ tail)) uCnt
      (natSyms L ++ ct) = S := by
    funext k
    simp only [Nat.sub_self, List.drop_zero, Function.update_apply]
    split_ifs <;> simp_all
  rw [hinit] at key
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) (fun _ _ => trivial) le_rfl
  · simp only [Nat.sub_zero, List.drop_length, FramePassRAux.arrSyms_nil, List.nil_append, hL]
  · have h := countdownCost_le (fun j => Φ (j + 1) - Φ j) L
    have hsum := sum_telescope Φ (fun j => by
      simp only [hΦ]
      have := length_arrSyms_drop_mono qs (show L - (j + 1) ≤ L - j by omega)
      omega) 0 L
    simp only [Nat.add_zero, Nat.zero_mul] at hsum
    have hsum' : ((List.range L).map fun j => Φ (j + 1) - Φ j).sum = Φ L - Φ 0 := by
      rw [← hsum]
    have hΦL : Φ L = 3 * (arrSyms qs).length := by simp [hΦ]
    have hΦ0 : Φ 0 = 0 := by simp [hΦ, hL, FramePassRAux.arrSyms_nil]
    have hlen := length_le_length_arrSyms qs
    rw [hsum', hΦL, hΦ0] at h
    omega

/-- **One block of the unpadding loop**: keep `ps` (moved to `Y`), drop `qs`. -/
theorem runs_unpadBody (N0 Npad : ℕ) (ps qs : List (List Bool)) (hps : ps.length = N0)
    (hqs : qs.length = Npad) (later r1 r2 tt cntT : List Sym) (hr1 : TermOK r1)
    (hr2 : TermOK r2) (S : UK → List Sym) (hA : S uA = arrSyms ps ++ (arrSyms qs ++ later))
    (h1 : S uN0 = natSyms N0 ++ r1) (h2 : S uNp = natSyms Npad ++ r2)
    (hTmp : S uTmp = Sym.mark :: tt) (hcnt : S uCnt = Sym.mark :: cntT) (ρ : List (SProg UK)) :
    RunsIn ρ unpadBody S (Function.update (Function.update S uA later) uY
        (arrSyms ps.reverse ++ S uY))
      (fun v => v = later.head?)
      (7 * bitLen N0 + 7 + (24 * (arrSyms ps).length + 2) + (7 * bitLen Npad + 7 +
        ((19 * (arrSyms qs).length + 2) + 1))) := by
  have c1 := runsIn_copyBlockU (src := uN0) (dst := uCnt) (tmp := uT2) (by decide) (by decide)
    (by decide) N0 r1 hr1 S h1 ρ
  have c2 := runs_moveRecsU ps (arrSyms qs ++ later) (Sym.mark :: cntT) tt (TermOK.cons rfl _)
    (Function.update S uCnt (natSyms N0 ++ S uCnt))
    (by rw [Function.update_of_ne (by decide), hA]) (by rw [Function.update_self, hcnt, hps])
    (by rw [Function.update_of_ne (by decide), hTmp]) ρ
  set S2 := Function.update (Function.update (Function.update
    (Function.update S uCnt (natSyms N0 ++ S uCnt)) uA (arrSyms qs ++ later)) uY
    (arrSyms ps.reverse ++ Function.update S uCnt (natSyms N0 ++ S uCnt) uY)) uCnt
    (Sym.mark :: cntT) with hS2
  have c3 := runsIn_copyBlockU (src := uNp) (dst := uCnt) (tmp := uT2) (by decide) (by decide)
    (by decide) Npad r2 hr2 S2 (by
      rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), h2]) ρ
  have hS2cnt : S2 uCnt = Sym.mark :: cntT := by rw [hS2, Function.update_self]
  have hS2A : S2 uA = arrSyms qs ++ later := by
    rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have c4 := runs_dropRecs qs later (Sym.mark :: cntT) (TermOK.cons rfl _)
    (Function.update S2 uCnt (natSyms Npad ++ S2 uCnt))
    (by rw [Function.update_of_ne (by decide), hS2A])
    (by rw [Function.update_self, hS2cnt, hqs]) ρ
  have c5 := runsIn_peekRU uA (Function.update (Function.update
    (Function.update S2 uCnt (natSyms Npad ++ S2 uCnt)) uA later) uCnt (Sym.mark :: cntT)) ρ
  refine RunsIn.mono (RunsIn.congr (RunsIn.seq c1 (RunsIn.seq c2 (RunsIn.seq c3
    (RunsIn.seq c4 c5)))) ?_ (by omega)) ?_ le_rfl
  · funext k
    by_cases k1 : k = uA
    · subst k1
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k2 : k = uY
    · subst k2
      simp +decide only [hS2, Function.update_apply, ↓reduceIte]
    by_cases k3 : k = uCnt
    · subst k3
      simp +decide only [hS2, Function.update_apply, ↓reduceIte, hcnt]
    simp only [hS2, Function.update_apply, k1, k2, k3, ↓reduceIte]
  · intro v hv
    rw [hv]
    simp +decide only [Function.update_apply, ↓reduceIte]


/-! ## The unpadding loop -/

/-- Output records of the unpadded blocks. -/
def outU (N0 w : ℕ) (bs : List (List (List CInt))) : List (List Bool) :=
  ((bs.map (List.take N0)).flatten).map (crecBits w)

theorem outU_append_single (N0 w : ℕ) (bs : List (List (List CInt))) (b : List (List CInt)) :
    outU N0 w (bs ++ [b]) = outU N0 w bs ++ (b.take N0).map (crecBits w) := by
  simp [outU]

theorem length_outU_le (N0 w : ℕ) : ∀ bs : List (List (List CInt)),
    (arrSyms (outU N0 w bs)).length ≤ (carrSyms w bs.flatten).length
  | [] => by simp [outU, carrSyms_nil, FramePassRAux.arrSyms_nil]
  | b :: bs => by
    have ih := length_outU_le N0 w bs
    have e1 : outU N0 w (b :: bs) = (b.take N0).map (crecBits w) ++ outU N0 w bs := by
      simp [outU]
    have e2 : carrSyms w (b :: bs).flatten =
        arrSyms ((b.take N0).map (crecBits w)) ++ arrSyms ((b.drop N0).map (crecBits w)) ++
          carrSyms w bs.flatten := by
      rw [List.flatten_cons, carrSyms_append]
      conv_lhs => rw [← List.take_append_drop N0 b]
      rw [carrSyms_append]
      rfl
    rw [e1, e2, FramePassRAux.arrSyms_append]
    simp only [List.length_append]
    omega

/-- The state of the unpadding loop with `n` blocks left. -/
def ustLoop (N0 w : ℕ) (blks : List (List (List CInt))) (rest : List Sym)
    (S0 : UK → List Sym) (n : ℕ) : UK → List Sym :=
  Function.update (Function.update S0 uA
    (carrSyms w (blks.drop (blks.length - n)).flatten ++ rest)) uY
    (arrSyms (outU N0 w (blks.take (blks.length - n))).reverse ++ S0 uY)

/-- The potential of the unpadding loop: `24·` the input volume of the blocks left. -/
def upot (w : ℕ) (blks : List (List (List CInt))) (n : ℕ) : ℕ :=
  24 * (carrSyms w (blks.drop (blks.length - n)).flatten).length

theorem upot_step (w : ℕ) (blks : List (List (List CInt))) (n : ℕ) :
    upot w blks n ≤ upot w blks (n + 1) := by
  unfold upot
  have e : blks.drop (blks.length - (n + 1)) =
      (blks.drop (blks.length - (n + 1))).take (blks.length - n - (blks.length - (n + 1))) ++
        blks.drop (blks.length - n) := by
    conv_lhs => rw [← List.take_append_drop (blks.length - n - (blks.length - (n + 1)))
      (blks.drop (blks.length - (n + 1)))]
    rw [List.drop_drop]
    congr 2
    omega
  rw [e, List.flatten_append, carrSyms_append, List.length_append]
  omega

/-- **One iteration of the unpadding loop** (`n + 1 → n` blocks left). -/
theorem runs_uloopBody (N0 Npad w : ℕ) (hN : 1 ≤ N0 + Npad) (blks : List (List (List CInt)))
    (hblk : ∀ b ∈ blks, b.length = N0 + Npad) (rest : List Sym) (hrest : BlkTerm rest)
    (r1 r2 : List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2) (S0 : UK → List Sym)
    (h1 : S0 uN0 = natSyms N0 ++ r1) (h2 : S0 uNp = natSyms Npad ++ r2) (tt cntT : List Sym)
    (hTmp : S0 uTmp = Sym.mark :: tt) (hcnt : S0 uCnt = Sym.mark :: cntT)
    (ρ : List (SProg UK)) (n : ℕ) (hn : n < blks.length) :
    RunsIn ρ unpadBody (ustLoop N0 w blks rest S0 (n + 1)) (ustLoop N0 w blks rest S0 n)
      (fun v => isRecSym v = decide (0 < n))
      (upot w blks (n + 1) - upot w blks n + (7 * bitLen N0 + 7 * bitLen Npad + 19)) := by
  have hlt : blks.length - (n + 1) < blks.length := by omega
  have hdrop : blks.drop (blks.length - (n + 1)) =
      blks[blks.length - (n + 1)] :: blks.drop (blks.length - n) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    omega
  have htake : blks.take (blks.length - n) =
      blks.take (blks.length - (n + 1)) ++ [blks[blks.length - (n + 1)]] := by
    rw [show blks.length - n = blks.length - (n + 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hlt]
    rfl
  have hblen : (blks[blks.length - (n + 1)]).length = N0 + Npad := hblk _ (List.getElem_mem hlt)
  set b := blks[blks.length - (n + 1)] with hb
  set later := carrSyms w (blks.drop (blks.length - n)).flatten ++ rest with hlater
  have hloop : ∀ k : UK, k ≠ uA → k ≠ uY → ustLoop N0 w blks rest S0 (n + 1) k = S0 k := by
    intro k k1 k2
    simp only [ustLoop, Function.update_apply, k1, k2, ↓reduceIte]
  have hb2 : carrSyms w b = arrSyms ((b.take N0).map (crecBits w)) ++
      arrSyms ((b.drop N0).map (crecBits w)) := by
    conv_lhs => rw [← List.take_append_drop N0 b]
    rw [carrSyms_append]
    rfl
  have hStA : ustLoop N0 w blks rest S0 (n + 1) uA = arrSyms ((b.take N0).map (crecBits w)) ++
      (arrSyms ((b.drop N0).map (crecBits w)) ++ later) := by
    simp +decide only [ustLoop, Function.update_apply, ↓reduceIte]
    rw [hdrop, List.flatten_cons, carrSyms_append, hb2, List.append_assoc, List.append_assoc]
  have key := runs_unpadBody N0 Npad ((b.take N0).map (crecBits w)) ((b.drop N0).map (crecBits w))
    (by rw [List.length_map, List.length_take, hblen]; omega)
    (by rw [List.length_map, List.length_drop, hblen]; omega)
    later r1 r2 tt cntT hr1 hr2 (ustLoop N0 w blks rest S0 (n + 1)) hStA
    (by rw [hloop _ (by decide) (by decide), h1]) (by rw [hloop _ (by decide) (by decide), h2])
    (by rw [hloop _ (by decide) (by decide), hTmp]) (by rw [hloop _ (by decide) (by decide), hcnt])
    ρ
  have hY : arrSyms ((b.take N0).map (crecBits w)).reverse ++ ustLoop N0 w blks rest S0 (n + 1) uY =
      arrSyms (outU N0 w (blks.take (blks.length - n))).reverse ++ S0 uY := by
    simp +decide only [ustLoop, Function.update_apply, ↓reduceIte]
    rw [htake, outU_append_single]
    simp only [List.reverse_append, FramePassRAux.arrSyms_append, List.append_assoc]
  refine RunsIn.mono (RunsIn.congr key ?_ ?_) ?_ le_rfl
  · funext k
    by_cases k1 : k = uA
    · subst k1
      simp +decide only [ustLoop, Function.update_apply, ↓reduceIte]
      exact hlater
    by_cases k2 : k = uY
    · subst k2
      rw [Function.update_self, hY]
      simp +decide only [ustLoop, Function.update_apply, ↓reduceIte]
    rw [Function.update_of_ne k2, Function.update_of_ne k1, hloop k k1 k2]
    simp only [ustLoop, Function.update_apply, k1, k2, ↓reduceIte]
  · have hΨ : upot w blks (n + 1) = upot w blks n +
        24 * ((arrSyms ((b.take N0).map (crecBits w))).length +
          (arrSyms ((b.drop N0).map (crecBits w))).length) := by
      simp only [upot]
      rw [hdrop, List.flatten_cons, carrSyms_append, hb2, List.length_append, List.length_append]
      ring
    rw [hΨ, Nat.add_sub_cancel_left]
    omega
  · intro v hv
    rw [hv, hlater, isRecSym_head (N0 + Npad) w hN _
      (fun b' hb' => hblk b' (List.mem_of_mem_drop hb')) rest hrest, List.length_drop]
    congr 1
    apply propext
    omega

/-- The state after the floors of the unpadding kernel. -/
def ufloorSt (S : UK → List Sym) : UK → List Sym :=
  Function.update (Function.update (Function.update S uY (Sym.mark :: S uY)) uTmp
    (Sym.mark :: S uTmp)) uCnt (Sym.mark :: S uCnt)

theorem runs_ufloors (S : UK → List Sym) (ρ : List (SProg UK)) :
    RunsIn ρ ufloors S (ufloorSt S) (fun _ => True) 3 := by
  refine RunsIn.congr (RunsIn.seq (runsIn_pushCU uY _ _ ρ) (RunsIn.seq (runsIn_pushCU uTmp _ _ ρ)
    (runsIn_pushCU uCnt _ _ ρ))) ?_ le_rfl
  funext k
  simp only [ufloorSt, Function.update_apply]
  split_ifs <;> simp_all

/-- **The unpadding kernel**, exact stacks and cost (blocks of `N0 + Npad ≥ 1` records, or no
block at all). -/
theorem runs_unpadProg (N0 Npad w : ℕ) (blks : List (List (List CInt)))
    (hN : 1 ≤ N0 + Npad ∨ blks = []) (hblk : ∀ b ∈ blks, b.length = N0 + Npad)
    (rest r1 r2 : List Sym) (hrest : BlkTerm rest) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (S : UK → List Sym) (hS0 : S uA = carrSyms w blks.flatten ++ rest)
    (hS1 : S uN0 = natSyms N0 ++ r1) (hS2 : S uNp = natSyms Npad ++ r2) :
    Runs unpadProg S (Function.update S uA (carrSyms w (blks.map (List.take N0)).flatten ++ rest))
      (fun _ => True)
      (40 * (cvol w blks.flatten + (blks.length + 1) * (bitLen N0 + bitLen Npad + 1))) := by
  set S0 := ufloorSt S with hS0def
  have f1 := runs_ufloors S []
  have hS0n : ∀ i : Fin 3, S0 (.inl i) = S (.inl i) := by
    intro i
    simp [hS0def, ufloorSt]
  have hS0Y : S0 uY = Sym.mark :: S uY := by simp +decide [hS0def, ufloorSt]
  have hS0Tmp : S0 uTmp = Sym.mark :: S uTmp := by simp +decide [hS0def, ufloorSt]
  have hS0Cnt : S0 uCnt = Sym.mark :: S uCnt := by simp +decide [hS0def, ufloorSt]
  have hstep := fun n (hn : n < blks.length) => runs_uloopBody N0 Npad w
    (hN.resolve_right (List.ne_nil_of_length_pos (by omega))) blks hblk rest hrest r1 r2 hr1 hr2 S0
    (by rw [hS0n]; exact hS1) (by rw [hS0n]; exact hS2) (S uTmp) (S uCnt) hS0Tmp hS0Cnt [] n hn
  have hst0 : ustLoop N0 w blks rest S0 blks.length = S0 := by
    funext k
    simp only [ustLoop, Nat.sub_self, List.drop_zero, List.take_zero, outU, List.map_nil,
      List.flatten_nil, List.reverse_nil, FramePassRAux.arrSyms_nil, List.nil_append,
      Function.update_apply]
    split_ifs with h1 h2
    · subst h1
      rfl
    · subst h2
      show carrSyms w blks.flatten ++ rest = S0 (.inl 0)
      rw [hS0n]
      exact hS0.symm
    · rfl
  have h0 : RunsIn [] (peekR uA) S0 (ustLoop N0 w blks rest S0 blks.length)
      (fun v => isRecSym v = decide (0 < blks.length)) 1 := by
    rw [hst0]
    refine RunsIn.mono (runsIn_peekRU uA S0 []) (fun v hv => ?_) le_rfl
    rw [hv]
    show isRecSym (S0 (.inl 0)).head? = _
    rw [hS0n]
    show isRecSym (S uA).head? = _
    rw [hS0]
    rcases hN with hN | hN
    · exact isRecSym_head (N0 + Npad) w hN blks hblk rest hrest
    · subst hN
      exact isRecSym_head 1 w le_rfl [] (by simp) rest hrest
  have hloop := RunsIn.seq_loop h0 hstep
  have hL0A : ustLoop N0 w blks rest S0 0 uA = rest := by
    simp +decide [ustLoop, carrSyms_nil]
  have hL0Y : ustLoop N0 w blks rest S0 0 uY =
      arrSyms (outU N0 w blks).reverse ++ Sym.mark :: S uY := by
    simp +decide [ustLoop, hS0Y]
  have hL0Tmp : ustLoop N0 w blks rest S0 0 uTmp = Sym.mark :: S uTmp := by
    simp +decide [ustLoop, hS0Tmp]
  have hpR := RunsIn.of_runs (runs_passR (g := Sym.mark) (gt := Sym.mark) (src := uY)
    (tmp := uTmp) (dst := uA) (by decide) (by decide) (by decide) rfl (by decide) rfl
    (outU N0 w blks).reverse (S uY) (S uTmp) (ustLoop N0 w blks rest S0 0) hL0Y hL0Tmp)
    (closed_passR _ _ _ _ _) []
  set S5 := Function.update (Function.update (ustLoop N0 w blks rest S0 0) uY
    (Sym.mark :: S uY)) uA (arrSyms (outU N0 w blks).reverse.reverse ++
      ustLoop N0 w blks rest S0 0 uA) with hS5
  have hS5v : ∀ k : UK, k ≠ uA → k ≠ uY → S5 k = S0 k := by
    intro k k1 k2
    simp only [hS5, ustLoop, Function.update_apply, k1, k2, ↓reduceIte]
  have u1 := runsIn_popRU uY S5 Sym.mark (S uY) (by simp +decide [hS5]) []
  have u2 := runsIn_popRU uTmp (Function.update S5 uY (S uY)) Sym.mark (S uTmp)
    (by rw [Function.update_of_ne (by decide), hS5v _ (by decide) (by decide), hS0Tmp]) []
  have u3 := runsIn_popRU uCnt (Function.update (Function.update S5 uY (S uY)) uTmp (S uTmp))
    Sym.mark (S uCnt) (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hS5v _ (by decide) (by decide), hS0Cnt]) []
  have hall := RunsIn.seq f1 (RunsIn.seq hloop (RunsIn.seq hpR (RunsIn.seq u1
    (RunsIn.seq u2 u3))))
  refine RunsIn.iff_runs.mp (RunsIn.mono (RunsIn.congr hall ?_ ?_) (fun _ _ => trivial) le_rfl)
  · funext k
    by_cases k1 : k = uA
    · subst k1
      simp +decide only [Function.update_apply, ↓reduceIte, hS5, List.reverse_reverse, hL0A]
      rfl
    by_cases k2 : k = uY
    · subst k2
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k3 : k = uTmp
    · subst k3
      simp +decide only [Function.update_apply, ↓reduceIte]
    by_cases k4 : k = uCnt
    · subst k4
      simp +decide only [Function.update_apply, ↓reduceIte]
    simp only [Function.update_apply, k1, k2, k3, k4, ↓reduceIte]
    rw [hS5v k k1 k2, hS0def]
    simp only [ufloorSt, Function.update_apply, k2, k3, k4, ↓reduceIte]
  · have hlc := loopCost_telescope (upot w blks) (upot_step w blks)
      (7 * bitLen N0 + 7 * bitLen Npad + 19) blks.length
    have hP0 : upot w blks 0 = 0 := by
      simp [upot, carrSyms_nil]
    have hPB : upot w blks blks.length = 24 * cvol w blks.flatten := by
      simp [upot, cvol]
    have hrev : (arrSyms (outU N0 w blks).reverse).length ≤ cvol w blks.flatten := by
      rw [length_arrSyms, List.map_reverse, List.sum_reverse, ← length_arrSyms]
      exact length_outU_le N0 w blks
    rw [hlc, hP0, hPB]
    have hXY : (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length ≤
        20 * ((blks.length + 1) * (bitLen N0 + bitLen Npad + 1)) := by
      calc (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length
          ≤ (20 * (bitLen N0 + bitLen Npad + 1)) * (blks.length + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
        _ = 20 * ((blks.length + 1) * (bitLen N0 + bitLen Npad + 1)) := by ring
    have hY1 : 1 ≤ (blks.length + 1) * (bitLen N0 + bitLen Npad + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    generalize (7 * bitLen N0 + 7 * bitLen Npad + 19 + 1) * blks.length = X at hXY ⊢
    generalize (blks.length + 1) * (bitLen N0 + bitLen Npad + 1) = Y at hXY hY1 ⊢
    omega

end SubNLogN.Machine.Layer.DrvPadDescAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Calculus DrvPadDescAux

/-- **Unpadding kernel** (`DrvUnpadStmt`, Section A.6 (`sec:transfer-layer`)): proved. -/
theorem drvUnpad_holds : DrvUnpadStmt := by
  refine ⟨40, fun _ => ⟨UE, inferInstance, inferInstance, Option Sym, unpadProg, inferInstance,
    ⟨none⟩, closed_unpadProg, ?_⟩⟩
  intro N0 Npad w blks rest r1 r2 S hblk hrest hr1 hr2 hS0 hS1 hS2
  by_cases hN : 1 ≤ N0 + Npad
  · exact runs_unpadProg N0 Npad w blks (Or.inl hN) hblk rest r1 r2 hrest hr1 hr2 S hS0 hS1 hS2
  · -- every block is empty: the input and the output are both `rest`
    have hb0 : ∀ b ∈ blks, b = [] := fun b hb =>
      List.eq_nil_of_length_eq_zero (by rw [hblk b hb]; omega)
    have hflat : blks.flatten = [] := List.flatten_eq_nil_iff.2 hb0
    have hflat2 : (blks.map (List.take N0)).flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hl
      rw [hb0 b hb, List.take_nil]
    have h := runs_unpadProg N0 Npad w [] (Or.inr rfl) (by simp) rest r1 r2 hrest hr1 hr2 S
      (by rw [hS0, hflat]; rfl) hS1 hS2
    rw [hflat2]
    refine RunsIn.iff_runs.mp (RunsIn.mono (RunsIn.iff_runs.mpr h) (fun _ _ => trivial) ?_)
    simp only [List.flatten_nil, List.length_nil, hflat]
    nlinarith

end SubNLogN.Machine.Layer
