import WP.W9a.LevelBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WP.W9a.LevelPost — the POST level program (`W9_postLevelProg`)

`postProg hm fl swp`:
1. `hdrT1`: move `symPost` and the header `postFields` from `TR` to `TL`, copy the header onto `C0`
   (above `symGuard`), and copy `t1` (header field 2) onto `C2` (above a `mark`): the group size;
2. `fl` (the embedded `W9_retFlip`): the level's RET segment becomes the FIFO `blkE alts` on RQ;
3. the sweep `swp` (`g = t1`) with the embedded `W9_postNode` kernel (each node pops its `alt_q`);
4. skip the POST body (one `‖`-terminated chunk), pop `pSub` from `C1`, drop `C2` and the header.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

section Prog

variable {m : ℕ} {Rs Rx : Type}

/-- Read the POST header and set the group size `g = t1` (header field 2) on `C2`. -/
def hdrT1 (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (readHdr 8 (.inl .TR) (.inl .TL) (.inl .C0) (tA hm))
    (.seq (pushC (.inl .C2) .mark) (copyFieldAt 2 (.inl .C0) (.inl .C2) (tA hm) (.tag 1)))

/-- Skip the POST body, pop `pSub` from `C1`, drop `C2` and the header. -/
def postTail : SProg (BLoc m) :=
  .seq (moveChunk (.inl .TR) (.inl .TL) symSub) (.seq (dropUntil (.inl .C1) (isSym .mark)) cleanup)

/-- **The POST level program.** -/
def postProg (hm : 4 ≤ m) (fl : Prog (BLoc m) (fun _ => Sym) Rx)
    (swp : Prog (BLoc m) (fun _ => Sym) Rs) : Prog (BLoc m) (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  .seq (liftG3 (hdrT1 hm)) (.seq (liftX3 fl) (.seq (liftS3 swp) (liftG3 postTail)))

theorem closed_hdrT1 (hm : 4 ≤ m) : (hdrT1 hm).Closed :=
  ⟨closed_readHdr _ _ _ _ _, ⟨trivial, closed_copyFieldAt _ _ _ _ _⟩⟩

theorem closed_postTail : (postTail : SProg (BLoc m)).Closed :=
  ⟨closed_moveChunk _ _ _, ⟨closed_dropUntil _ _, closed_cleanup⟩⟩

theorem closed_postProg (hm : 4 ≤ m) {fl : Prog (BLoc m) (fun _ => Sym) Rx}
    {swp : Prog (BLoc m) (fun _ => Sym) Rs} (hf : fl.Closed) (hs : swp.Closed) :
    (postProg hm fl swp).Closed :=
  closed_seq (closed_liftG3 (closed_hdrT1 hm)) (closed_seq (closed_liftX3 hf)
    (closed_seq (closed_liftS3 hs) (closed_liftG3 closed_postTail)))

end Prog

/-- The POST header with `t1` on `C2`, exact. -/
theorem hdrT1_eval {m : ℕ} (hm : 4 ≤ m) (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (rest : List Sym)
    (S0 : BLoc m → List Sym) (v : Option Sym)
    (hTR : S0 (.inl .TR) = symPost :: (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ rest)) :
    Eval [] (hdrT1 hm) ⟨v, S0⟩
      ⟨some (.tag 1), Function.update (Function.update (Function.update (Function.update S0
        (.inl .TR) rest) (.inl .TL) ((hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).reverse ++
          symPost :: S0 (.inl .TL))) (.inl .C0) (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++
          symGuard :: S0 (.inl .C0))) (.inl .C2) (natSyms h.t1 ++ Sym.mark :: S0 (.inl .C2))⟩
      (7 * (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length +
        6 * (hdrSyms [h.p, h.pSub]).length + 7 * bitLen h.t1 + 19) := by
  have e1 := readHdr_eval (TR := (.inl .TR : BLoc m)) (TL := .inl .TL) (C0 := .inl .C0)
    (tA := tA hm) (by simp) (by simp) (by simp [tA]) (by simp) (by simp [tA]) (by simp [tA])
    symPost (postFields h.p h.pSub h.t1 h.r h.pChild) rest S0 v hTR
  generalize hS1 : Function.update (Function.update (Function.update S0 (.inl .TR) rest) (.inl .TL)
      ((hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).reverse ++ symPost :: S0 (.inl .TL)))
      (.inl .C0) (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ symGuard :: S0 (.inl .C0))
      = S1 at e1
  have e2 : Eval [] (pushC (.inl .C2) .mark) ⟨some symLevel, S1⟩
      ⟨some symLevel, Function.update S1 (.inl .C2) (.mark :: S1 (.inl .C2))⟩ 1 :=
    Eval.push _ _ _ _ _
  have hC0 : Function.update S1 (.inl .C2) (.mark :: S1 (.inl .C2)) (.inl .C0) =
      hdrSyms [h.p, h.pSub] ++ natSyms h.t1 ++ Sym.mark :: (hdrSyms [h.r, natLog2Fuel h.t1 h.t1,
        natLog2Fuel h.r h.r, h.pChild, barrettH h.pSub] ++ symGuard :: S0 (.inl .C0)) := by
    rw [Function.update_of_ne (by simp), ← hS1, Function.update_self, postFields]
    simp only [hdrSyms_cons, hdrSyms_nil, List.append_assoc, List.cons_append, List.nil_append]
  have e3 := copyFieldAt_eval (src := (.inl .C0 : BLoc m)) (dst := .inl .C2) (tmp := tA hm)
    (by simp) (by simp [tA]) (by simp [tA]) 1 [h.p, h.pSub] h.t1 _ _ (some symLevel) hC0
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_
  · rw [Function.update_self, Function.update_idem, ← hS1]
    congr 2
  · omega

/-- The POST tail, exact. -/
theorem postTail_eval {m : ℕ} (S0 : BLoc m → List Sym) (v : Option Sym) (h : PostHdr)
    (c0T c1T : Array (ℤ × ℤ)) (restT r1 c2 c0 : List Sym)
    (hTR : S0 (.inl .TR) = postBody h.pSub h.r c0T c1T ++ restT)
    (hC1 : S0 (.inl .C1) = hdrSyms [h.pSub] ++ r1)
    (hC2 : S0 (.inl .C2) = natSyms h.t1 ++ Sym.mark :: c2)
    (hC0 : S0 (.inl .C0) = hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ symGuard :: c0) :
    Eval [] postTail ⟨v, S0⟩
      ⟨some symGuard, Function.update (Function.update (Function.update (Function.update
        (Function.update S0 (.inl .TR) restT) (.inl .TL)
        ((postBody h.pSub h.r c0T c1T).reverse ++ S0 (.inl .TL))) (.inl .C1) r1) (.inl .C2) c2)
        (.inl .C0) c0⟩
      (3 * (postBody h.pSub h.r c0T c1T).length + 2 * bitLen h.pSub + 2 * bitLen h.t1 +
        2 * (hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild)).length + 6) := by
  have hrecs : symSub ∉ (List.range h.r).flatMap (fun u2 => postRecOf h.pSub h.r u2 c0T c1T) := by
    intro hm
    obtain ⟨u2, -, hu⟩ := List.mem_flatMap.1 hm
    simp only [postRecOf, postRecSyms, List.mem_append, List.mem_cons] at hu
    rcases hu with hu | hu | hu | hu | hu | hu
    · have := entrySym_intSyms _ _ hu
      simp [EntrySym, isTagSym, symSub] at this
    · exact absurd hu (by decide)
    · have := entrySym_intSyms _ _ hu
      simp [EntrySym, isTagSym, symSub] at this
    · exact absurd hu (by decide)
    · simp only [natSyms, List.mem_map] at hu
      obtain ⟨b, -, hb⟩ := hu
      cases hb
    · exact absurd hu (by decide)
  have e1 := moveChunk_eval (src := (.inl .TR : BLoc m)) (dst := .inl .TL) (by simp) symSub v
    ((List.range h.r).flatMap (fun u2 => postRecOf h.pSub h.r u2 c0T c1T)) restT S0 hrecs
    (by rw [hTR, postBody, List.append_assoc]; rfl)
  have hg : ∀ x ∈ natSyms h.pSub, isSym .mark (some x) = false := by
    intro x hx
    simp only [natSyms, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact isSym_some_of_ne (fun h => by cases h)
  have e2 := dropUntil_eval (src := (.inl .C1 : BLoc m)) (isSym .mark) (some symSub)
    (natSyms h.pSub) (Sym.mark :: r1) (Function.update (Function.update S0 (.inl .TR) restT)
      (.inl .TL) (((List.range h.r).flatMap (fun u2 => postRecOf h.pSub h.r u2 c0T c1T) ++
        [symSub]).reverse ++ S0 (.inl .TL))) hg (isSym_some_self _)
    (by rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), hC1, hdrSyms_cons,
      hdrSyms_nil]; simp)
  have e3 := cleanup_eval (Function.update (Function.update (Function.update S0 (.inl .TR) restT)
    (.inl .TL) (((List.range h.r).flatMap (fun u2 => postRecOf h.pSub h.r u2 c0T c1T) ++
      [symSub]).reverse ++ S0 (.inl .TL))) (.inl .C1) (Sym.mark :: r1).tail) (some Sym.mark) h.t1
    (postFields h.p h.pSub h.t1 h.r h.pChild) c2 c0
    (by simp only [Function.update_apply]; simp [hC2])
    (by simp only [Function.update_apply]; simp [hC0])
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq rfl ?_
  rw [length_natSyms, postBody, List.length_append]
  simp only [List.length_singleton]
  omega

theorem postNodeV_size (p pSub t1 r : ℕ) (c0T c1T : Array (ℤ × ℤ)) (pChild : ℕ) (alt : ℤ × ℤ)
    (qHat : Array (Array (ℤ × ℤ))) : (postNodeV p pSub t1 r c0T c1T pChild alt qHat).size = t1 * r :=
  size_runSequentialScanSteps _ _

theorem groupAt_succ (g i : ℕ) (ys : List (Array (ℤ × ℤ))) :
    groupAt g ys (i + 1) = groupAt g (ys.drop g) i := by
  simp only [groupAt, List.drop_drop]
  congr 2
  rw [Nat.succ_mul, Nat.add_comm]

/-- `postLevel` as a map over the node indices. -/
theorem postLevel_eq_map (f : ℤ × ℤ → Array (Array (ℤ × ℤ)) → Array (ℤ × ℤ)) (t1 : ℕ) :
    ∀ (alts : List (ℤ × ℤ)) (ys : List (Array (ℤ × ℤ))), postLevel f t1 alts ys =
      (List.range alts.length).map (fun i => f (alts.getD i (0, 0)) (groupAt t1 ys i).toArray)
  | [], _ => rfl
  | a :: as, ys => by
    rw [postLevel, postLevel_eq_map f t1 as (ys.drop t1), List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · simp [groupAt]
    · refine List.map_congr_left (fun i _ => ?_)
      simp [groupAt_succ]

/-- The POST level's output stream. -/
theorem post_out_eq (f : ℤ × ℤ → Array (Array (ℤ × ℤ)) → Array (ℤ × ℤ)) (t1 : ℕ)
    (alts : List (ℤ × ℤ)) (ys : List (Array (ℤ × ℤ))) (restS : List Sym) :
    (List.range alts.length).flatMap (fun i => nodeSyms (f (alts.getD i (0, 0))
      (groupAt t1 ys i).toArray)) ++ symLevel :: restS = streamSyms (postLevel f t1 alts ys) ++ restS := by
  rw [postLevel_eq_map, streamSyms, flatMap_map', List.append_assoc]
  rfl

/-- Cost arithmetic of the POST level (`A + Cc + B + D + 1` is `postLevelBound`). -/
theorem post_cost (Ck Cs Cf A B Cc D hdr body hp bt1 bps tfl tsw : ℕ)
    (htfl : tfl ≤ Cf * (2 * (D + 1))) (htsw : tsw ≤ Ck * A + Cs * (2 * (Cc + B + D + 1)))
    (hhp : hp ≤ hdr) (hbt1 : bt1 ≤ hdr) (hbps : bps ≤ hdr) :
    7 * hdr + 6 * hp + 7 * bt1 + 19 + (tfl + (tsw + (3 * body + 2 * bps + 2 * bt1 + 2 * hdr + 6))) ≤
      (Ck + 2 * Cs + 2 * Cf + 64) * ((A + Cc + B + D + 1) + (hdr + body + 1)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (A + Cc + B + D + 1) + (hdr + body + 1) := ⟨_, rfl⟩
  rw [← hX]
  have h1 : Ck * A ≤ Ck * X := Nat.mul_le_mul_left _ (by omega)
  have h2 : Cs * (2 * (Cc + B + D + 1)) ≤ 2 * Cs * X := by
    calc Cs * (2 * (Cc + B + D + 1)) ≤ Cs * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cs * X := by ring
  have h3 : Cf * (2 * (D + 1)) ≤ 2 * Cf * X := by
    calc Cf * (2 * (D + 1)) ≤ Cf * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Cf * X := by ring
  have h4 : (Ck + 2 * Cs + 2 * Cf + 64) * X = Ck * X + 2 * Cs * X + 2 * Cf * X + 64 * X := by ring
  rw [h4]
  omega

#assert_std_axioms hdrT1_eval postTail_eval postNodeV_size groupAt_succ postLevel_eq_map
  post_out_eq post_cost

end WP.W9a
