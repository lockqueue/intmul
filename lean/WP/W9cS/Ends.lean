import WP.W9cS.Loop

/-!
# WP.W9cS.Ends — prologue and epilogue of the spread driver

* `prologue e`: mark `IN T OUT RS Q TMP`; copy the row length `r` (4th header field of `C0`) onto
  `RS`; move the matrix `W0 → T → IN` (so `IN = blkE all ++ mark :: _`, `W0 = []`).
* `epilogue e`: move the results `OUT → W0`; move the final `symSub` `TR → TL`; drop the marks
  (draining the counter `RS`).
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 Computability

variable {K : Type}

/-- Mark the six private stacks. -/
def marks (e : DS → K) : SProg K :=
  .seq (pushC (e .IN) .mark) (.seq (pushC (e .T) .mark) (.seq (pushC (e .OUT) .mark)
    (.seq (pushC (e .RS) .mark) (.seq (pushC (e .Q) .mark) (pushC (e .TMP) .mark)))))

/-- Prologue. -/
def prologue (e : DS → K) : SProg K :=
  .seq (marks e) (.seq (getF4 (e .C0) (e .RS) (e .TMP) (e .Q))
    (.seq (moveAll (e .W0) (e .T)) (moveBlk (e .T) (e .IN))))

/-- Pop a bit block and its terminator. -/
def drain (k : K) : SProg K := .seq (popR k) (.loop optIsBit (popR k))

/-- Move the top symbol of `src` onto `dst`. -/
def xferTop (src dst : K) : SProg K := .seq (popR src) (pushR dst)

/-- Epilogue. -/
def epilogue (e : DS → K) : SProg K :=
  .seq (moveBlk (e .OUT) (e .W0)) (.seq (xferTop (e .TR) (e .TL))
    (.seq (popR (e .IN)) (.seq (popR (e .T)) (.seq (popR (e .OUT)) (.seq (popR (e .Q))
      (.seq (popR (e .TMP)) (drain (e .RS))))))))

theorem prologue_closed (e : DS → K) : (prologue e).Closed := by
  have h1 := getF4_closed (e .C0) (e .RS) (e .TMP) (e .Q)
  have h2 := moveAll_closed (e .W0) (e .T)
  have h3 := moveBlk_closed (e .T) (e .IN)
  simp only [Prog.Closed] at h1 h2 h3 ⊢
  simp [prologue, marks, Prog.FreeBelow, pushC, h1, h2, h3]

theorem epilogue_closed (e : DS → K) : (epilogue e).Closed := by
  have h1 := moveBlk_closed (e .OUT) (e .W0)
  simp only [Prog.Closed] at h1 ⊢
  simp [epilogue, drain, xferTop, Prog.FreeBelow, pushR, popR, h1]

variable [DecidableEq K]

theorem pushC_runs' (k : K) (x : Sym) (S : K → List Sym) :
    RunsIn [] (pushC k x) S (Function.update S k (x :: S k)) 1 :=
  RunsIn.of_evLe (fun r => r) fun r => pushC_evLe [] k x r S

theorem popR_runs' (k : K) (S : K → List Sym) :
    RunsIn [] (popR k) S (Function.update S k (S k).tail) 1 :=
  RunsIn.of_evLe (fun _ => (S k).head?) fun r => popR_evLe [] k r S

theorem drain_loop (k : K) (ρ : List (SProg K)) (rest : List Sym) :
    ∀ (bs : List Bool) (S : K → List Sym) (b : Bool), S k = bs.map Sym.bit ++ Sym.mark :: rest →
      EvLe ρ (.loop optIsBit (popR k)) (some (.bit b)) S (some .mark)
        (Function.update S k rest) (2 * bs.length + 3)
  | [], S, b, hS => by
    have e1 := popR_evLe ρ k (some (.bit b)) S
    rw [hS] at e1
    simp only [List.map_nil, List.nil_append, List.head?_cons, List.tail_cons] at e1
    exact (EvLe.loop_true (by rfl) e1 (EvLe.loop_false (by rfl))).mono (by simp)
  | c :: bs, S, b, hS => by
    have e1 := popR_evLe ρ k (some (.bit b)) S
    rw [hS] at e1
    simp only [List.map_cons, List.cons_append, List.head?_cons, List.tail_cons] at e1
    have ih := drain_loop k ρ rest bs (Function.update S k (bs.map Sym.bit ++ Sym.mark :: rest)) c
      (Function.update_self _ _ _)
    refine (EvLe.loop_true (by rfl) e1 ih).of_eq rfl ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

theorem drain_spec (k : K) (ρ : List (SProg K)) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S k = natSyms n ++ Sym.mark :: rest) :
    RunsIn ρ (drain k) S (Function.update S k rest) (2 * bitLen n + 2) := by
  refine RunsIn.of_evLe (fun _ => some .mark) fun v => ?_
  have e1 := popR_evLe ρ k v S
  rw [hS] at e1
  cases h : encodeNat n with
  | nil =>
    simp only [natSyms, h, List.map_nil, List.nil_append, List.head?_cons, List.tail_cons] at e1
    exact (e1.seq (EvLe.loop_false (by rfl))).mono (by omega)
  | cons b bs =>
    simp only [natSyms, h, List.map_cons, List.cons_append, List.head?_cons,
      List.tail_cons] at e1
    have e2 := drain_loop k ρ rest bs (Function.update S k (bs.map Sym.bit ++ Sym.mark :: rest)) b
      (Function.update_self _ _ _)
    refine (e1.seq e2).of_eq rfl (by rw [Function.update_idem]) ?_
    simp only [bitLen, h, List.length_cons]
    omega

theorem xferTop_spec {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (x : Sym)
    (rest : List Sym) (S : K → List Sym) (hS : S src = x :: rest) :
    RunsIn ρ (xferTop src dst) S (Function.update (Function.update S src rest) dst (x :: S dst))
      2 := by
  refine RunsIn.of_evLe (fun _ => some x) fun v => ?_
  have e1 := popR_evLe ρ src v S
  rw [hS] at e1
  simp only [List.head?_cons, List.tail_cons] at e1
  have e2 : EvLe ρ (pushR dst) (some x) (Function.update S src rest) (some x)
      (Function.update (Function.update S src rest) dst
        (x :: Function.update S src rest dst)) 1 :=
    ⟨1, (Eval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq rfl rfl, le_rfl⟩
  refine (e1.seq e2).of_eq rfl ?_ le_rfl
  rw [Function.update_of_ne (Ne.symm hne)]

#assert_std_axioms prologue_closed epilogue_closed pushC_runs' popR_runs' drain_loop drain_spec
  xferTop_spec

end WP.W9c
