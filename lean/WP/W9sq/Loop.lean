import WP.W9sq.Host

/-!
# WP.W9sq.Loop — the two loops of the stage (generic host)

* `peekLoop lS k stop body`: `peek k; while top(k) ≠ stop do (body; peek k)`. Rule
  `HT.peekLoop`: for a state family `St i` (`i` = entries processed) whose `k`-top is `stop`
  exactly at `i = N`, and a body taking `St i` to `St (i+1)` for `i < N`, the loop goes from
  `St 0` to `St N`.
* `xferLoop lS src dst stop`: `pop src; while popped ≠ stop do (push dst; pop src)`. Rule
  `HT.xferLoop`: `src = M ++ stop :: r` (`stop ∉ M`) becomes `src = r`, `dst += M.reverse`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2

variable {a b : ℕ} {σ : Type}

/-! ## The entry loop -/

/-- `peek k; while top(k) ≠ stop do (body; peek k)`. -/
def peekLoop (lS : Lens σ (Option Sym)) (k : Loc a b) (stop : Sym)
    (body : Prog (Loc a b) (fun _ => Sym) σ) : Prog (Loc a b) (fun _ => Sym) σ :=
  (Prog.peek k (fun v o => lS.set v o)).seq
    (Prog.loop (fun v => decide (lS.get v ≠ some stop))
      (body.seq (Prog.peek k (fun v o => lS.set v o))))

theorem peekLoop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (stop : Sym)
    (body : Prog (Loc a b) (fun _ => Sym) σ) (hb : body.Closed) :
    (peekLoop lS k stop body).Closed := ⟨trivial, hb, trivial⟩

theorem peek_triple (lS : Lens σ (Option Sym)) (k : Loc a b) (B : Loc a b → List Sym) :
    Triple [] (fun s => s.stk = B) (.peek k (fun v o => lS.set v o))
      (fun s => s.stk = B ∧ lS.get s.var = (B k).head?) 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, 1, Eval.peek [] k (fun v o => lS.set v o) v S, ⟨rfl, lS.get_set _ _⟩, le_rfl⟩

theorem HT.peekLoop (lS : Lens σ (Option Sym)) (k : Loc a b) (stop : Sym)
    (body : Prog (Loc a b) (fun _ => Sym) σ) (St : ℕ → Loc a b → List Sym) (N cb : ℕ)
    (hgo : ∀ i, i < N → (St i k).head? ≠ some stop) (hstop : (St N k).head? = some stop)
    (hbody : ∀ i, i < N → HT [] (St i) body (St (i + 1)) cb) :
    HT [] (St 0) (peekLoop lS k stop body) (St N) (1 + (N * (cb + 1 + 1) + 1)) := by
  refine Triple.seq (R := fun s => N ≤ N ∧ s.stk = St (N - N) ∧
      lS.get s.var = (St (N - N) k).head?)
    (Triple.conseq (peek_triple lS k (St 0)) (fun s hs => hs)
      (fun s hs => ⟨le_refl N, by simpa using hs⟩) le_rfl) ?_
  have hloop := Triple.loop (ρ := []) (c := fun v => decide (lS.get v ≠ some stop))
    (p := body.seq (.peek k (fun v o => lS.set v o)))
    (I := fun n s => n ≤ N ∧ s.stk = St (N - n) ∧ lS.get s.var = (St (N - n) k).head?)
    (B := fun _ => cb + 1) ?_ ?_ ?_ N
  · refine Triple.conseq hloop (fun s hs => hs) (fun s hs => ?_) ?_
    · simpa using hs.2.1
    · rw [loopCost_const]
  · intro n
    by_cases hn : n + 1 ≤ N
    · have e : N - n = (N - (n + 1)) + 1 := by omega
      have h1 := Triple.seq (hbody (N - (n + 1)) (by omega)) (peek_triple lS k (St (N - (n + 1) + 1)))
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, ?_, ?_⟩) le_rfl
      · rw [e]
        exact hs.1
      · rw [e]
        exact hs.2
    · intro s hs
      exact absurd hs.1 hn
  · intro n s hs
    have hgo' := hgo (N - (n + 1)) (by omega)
    show decide (lS.get s.var ≠ some stop) = true
    rw [hs.2.2]
    simpa using hgo'
  · intro s hs
    show decide (lS.get s.var ≠ some stop) = false
    rw [hs.2.2]
    simpa using hstop

/-! ## The transfer loop -/

/-- `pop src; while popped ≠ stop do (push dst; pop src)`. -/
def xferLoop (lS : Lens σ (Option Sym)) (src dst : Loc a b) (stop : Sym) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (popR' lS src).seq (.loop (fun v => decide (lS.get v ≠ some stop))
    ((Prog.push dst (fun v => (lS.get v).getD .sep)).seq (popR' lS src)))

theorem xferLoop_closed (lS : Lens σ (Option Sym)) (src dst : Loc a b) (stop : Sym) :
    (xferLoop lS src dst stop).Closed := ⟨trivial, trivial, trivial⟩

theorem xferLoop_loop_eval (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst)
    (stop : Sym) (r : List Sym) :
    ∀ (M : List Sym) (S : Loc a b → List Sym) (v : σ), stop ∉ M →
      lS.get v = (M ++ stop :: r).head? → S src = (M ++ stop :: r).tail →
      ∃ v', Eval [] (.loop (fun v => decide (lS.get v ≠ some stop))
          ((Prog.push dst (fun v => (lS.get v).getD .sep)).seq (popR' lS src))) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src r) dst (M.reverse ++ S dst)⟩
        (3 * M.length + 1)
  | [], S, v, _, hv, hS => by
    refine ⟨v, (Eval.loop_false ?_).of_eq ?_ rfl⟩
    · show decide (lS.get v ≠ some stop) = false
      rw [hv]
      simp
    · have hS' : S src = r := hS
      congr 1
      rw [List.reverse_nil, List.nil_append, ← hS', Function.update_eq_self,
        Function.update_eq_self]
  | y :: M, S, v, hM, hv, hS => by
    have hy : y ≠ stop := fun e => hM (e ▸ List.mem_cons_self ..)
    have hM' : stop ∉ M := fun e => hM (List.mem_cons_of_mem _ e)
    have hS' : S src = M ++ stop :: r := hS
    have hv' : lS.get v = some y := hv
    have e1 := Eval.push ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) dst
      (fun v => (lS.get v).getD .sep) v S
    have e2 := Eval.pop ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) src
      (fun v o => lS.set v o) v (Function.update S dst ((lS.get v).getD .sep :: S dst))
    have hsrc : Function.update S dst ((lS.get v).getD .sep :: S dst) src = M ++ stop :: r := by
      rw [Function.update_of_ne hne, hS']
    obtain ⟨v', ih⟩ := xferLoop_loop_eval lS hne stop r M
      (Function.update (Function.update S dst ((lS.get v).getD .sep :: S dst)) src
        (Function.update S dst ((lS.get v).getD .sep :: S dst) src).tail)
      (lS.set v (Function.update S dst ((lS.get v).getD .sep :: S dst) src).head?) hM'
      (by rw [lS.get_set, hsrc]) (by rw [Function.update_self, hsrc])
    refine ⟨v', (Eval.loop_true ?_ (Eval.seq e1 e2) ih).of_eq ?_ ?_⟩
    · show decide (lS.get v ≠ some stop) = true
      rw [hv']
      simpa using hy
    · rw [hv']
      congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append,
        Option.getD_some]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem HT.xferLoop (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst) (stop : Sym)
    (B : Loc a b → List Sym) (M r : List Sym) (hM : stop ∉ M) (hB : B src = M ++ stop :: r) :
    HT [] B (xferLoop lS src dst stop)
      (Function.update (Function.update B src r) dst (M.reverse ++ B dst)) (3 * M.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.pop ([] : List (Prog (Loc a b) (fun _ => Sym) σ)) src (fun v o => lS.set v o) v S
  obtain ⟨v', e2⟩ := xferLoop_loop_eval lS hne stop r M (Function.update S src (S src).tail)
    (lS.set v (S src).head?) hM (by rw [lS.get_set, hB]) (by rw [Function.update_self, hB])
  refine ⟨_, _, Eval.seq e1 e2, ?_, by omega⟩
  show Function.update (Function.update (Function.update S src (S src).tail) src r) dst
    (M.reverse ++ Function.update S src (S src).tail dst) = _
  rw [Function.update_idem, Function.update_of_ne (Ne.symm hne)]

#assert_std_axioms peekLoop_closed peek_triple HT.peekLoop xferLoop_closed xferLoop_loop_eval
  HT.xferLoop

end WP.W9sq
