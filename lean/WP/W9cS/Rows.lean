import WP.W9cS.Hdr
import WP.W9cS.Kernel
import Contracts.W9.Common

/-!
# WP.W9cS.Rows — one row of the spread driver

Driver stacks are named by `DS` through an injective `e : DS → K`. Registers are
`Option Sym × R`: the symbol register of the library macros (`lf`) and the row kernel's registers.

`rowWork e kerP`: copy the row length `r` (`RS → Q`), move `r` entries `IN → T` (counted), move
them `T → W0` (now `W0 = blkE row` exactly), run the kernel, move its output `W0 → OUT`.
The kernel is abstract: `KerOK` is its triple on `W0`, `TR`, `TL` for one row.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 Computability

/-- Stacks of the driver. -/
inductive DS
  | W0 | TR | TL | C0 | C1 | IN | T | OUT | RS | Q | TMP
  deriving DecidableEq

variable {K R : Type}

/-- Driver programs. -/
abbrev BProg (K R : Type) := Prog K (fun _ => Sym) (Option Sym × R)

/-- An `SProg` on the symbol register. -/
def lf (p : SProg K) : BProg K R := p.liftRegs (Lens.fst (Option Sym) R)

/-- Fetch one row: `W0 := blkE row`, taken from the top of `IN`. -/
def fetchRow (e : DS → K) : SProg K :=
  .seq (copyBlock (e .RS) (e .Q) (e .TMP))
    (.seq (cntLoop (e .Q) (e .TMP) (e .IN) (e .T)) (moveBlk (e .T) (e .W0)))

/-- One row: fetch, kernel, stash the result on `OUT`. -/
def rowWork (e : DS → K) (kerP : BProg K R) : BProg K R :=
  .seq (lf (fetchRow e)) (.seq kerP (lf (moveAll (e .W0) (e .OUT))))

theorem lf_closed {p : SProg K} (h : p.Closed) : (lf (R := R) p).Closed :=
  (freeBelow_liftRegs' _ p 0).2 h

theorem fetchRow_closed (e : DS → K) : (fetchRow e).Closed := by
  have h1 := cntLoop_closed (e .Q) (e .TMP) (e .IN) (e .T)
  have h2 := moveBlk_closed (e .T) (e .W0)
  simp only [Prog.Closed] at h1 h2 ⊢
  simp [fetchRow, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, skip, pushC, pushR, popR, h1, h2]

theorem rowWork_closed (e : DS → K) {kerP : BProg K R} (hk : kerP.Closed) :
    (rowWork e kerP).Closed :=
  ⟨lf_closed (fetchRow_closed e), hk, lf_closed (moveAll_closed (e .W0) (e .OUT))⟩

variable [DecidableEq K]

theorem lf_runs {p : SProg K} {S S' : K → List Sym} {T : ℕ} (h : RunsIn [] p S S' T) :
    RunsIn [] (lf (R := R) p) S S' T :=
  RunsIn.liftRegs (Lens.fst (Option Sym) R) h

theorem lf_peek (k : K) (v : Option Sym × R) (S : K → List Sym) :
    Eval [] (lf (R := R) (peekR k)) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 :=
  Eval.liftRegs (Lens.fst (Option Sym) R) (Eval.peek [] k (fun _ o => o) v.1 S) v rfl

theorem blkE_append (a b : List (ℤ × ℤ)) : blkE (a ++ b) = blkE a ++ blkE b := by
  simp [blkE, blk]

theorem blkE_eq_flatten (v : List (ℤ × ℤ)) : blkE v = (v.map entrySyms).flatten := rfl

theorem recOK_of_mem_map {v : List (ℤ × ℤ)} : ∀ x ∈ v.map entrySyms, RecOK x := by
  intro x hx
  obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx
  exact entrySyms_recOK z

theorem fetchRow_spec {e : DS → K} (he : Function.Injective e) (r : ℕ) (row : List (ℤ × ℤ))
    (hrow : row.length = r) (restIN Q0 T0 RS0 : List Sym) (S : K → List Sym)
    (hIN : S (e .IN) = blkE row ++ restIN) (hW : S (e .W0) = []) (hT : S (e .T) = Sym.mark :: T0)
    (hQ : S (e .Q) = Sym.mark :: Q0) (hRS : S (e .RS) = natSyms r ++ Sym.mark :: RS0) :
    RunsIn [] (fetchRow e) S
      (Function.update (Function.update S (e .IN) restIN) (e .W0) (blkE row))
      (7 * bitLen r + 16 * r + 6 * (blkE row).length + 13) := by
  have r1 : RunsIn [] (copyBlock (e .RS) (e .Q) (e .TMP)) S
      (Function.update S (e .Q) ((encodeNat r).map Sym.bit ++ S (e .Q))) (7 * bitLen r + 7) :=
    RunsIn.of_eval (f := fun _ => some Sym.mark) (fun v => copyBlock_eval (he.ne (by decide))
      (he.ne (by decide)) (he.ne (by decide)) [] v (encodeNat r) (Sym.mark :: RS0) S
      (TermOK.cons (by rfl) _) hRS) (le_of_eq rfl)
  set S1 := Function.update S (e .Q) ((encodeNat r).map Sym.bit ++ S (e .Q)) with hS1
  set A := row.map entrySyms with hA
  have hAl : A.length = r := by rw [hA, List.length_map, hrow]
  have r2 := cntLoop_spec (Q := e .Q) (TMP := e .TMP) (IN := e .IN) (T := e .T)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) [] A restIN
    (Sym.mark :: Q0) S1 recOK_of_mem_map (TermOK.cons (by rfl) _)
    (by rw [hS1, Function.update_self, hQ, hAl]; rfl)
    (by rw [hS1, Function.update_of_ne (he.ne (by decide)), hIN, blkE_eq_flatten])
  set S2 := Function.update (Function.update (Function.update S1 (e .Q) (Sym.mark :: Q0))
    (e .IN) restIN) (e .T) (A.flatten.reverse ++ S1 (e .T)) with hS2
  have hS2T : S2 (e .T) = A.flatten.reverse ++ Sym.mark :: T0 := by
    rw [hS2, Function.update_self, hS1, Function.update_of_ne (he.ne (by decide)), hT]
  have r3 : RunsIn [] (moveBlk (e .T) (e .W0)) S2
      (Function.update (Function.update S2 (e .T) (Sym.mark :: T0)) (e .W0)
        (A.flatten.reverse.reverse ++ S2 (e .W0))) (3 * A.flatten.length + 4) :=
    RunsIn.of_eval (f := fun _ => (Sym.mark :: T0).head?) (fun v => moveBlk_eval
      (he.ne (by decide)) [] v A.flatten.reverse (Sym.mark :: T0) S2
      (isRecSym_of_mem_reverse_flatten recOK_of_mem_map) (RecTerm.mark T0) hS2T)
      (by simp)
  refine RunsIn.of_eq (r1.seq (r2.seq r3)) ?_ ?_
  · funext k
    simp only [hS2, hS1, Function.update_apply, List.reverse_reverse, blkE_eq_flatten]
    split_ifs <;> simp_all [he.eq_iff]
  · rw [hAl, ← blkE_eq_flatten]
    omega

/-- The kernel's triple for one row `x = (row, out, filter-row symbols)`. -/
def KerOK (e : DS → K) (kerP : BProg K R) (c0 c1 : List Sym) (Ck : ℕ)
    (x : List (ℤ × ℤ) × List (ℤ × ℤ) × List Sym) : Prop :=
  ∀ (B : K → List Sym) (restT : List Sym), B (e .W0) = blkE x.1 → B (e .TR) = x.2.2 ++ restT →
    B (e .C0) = c0 → B (e .C1) = c1 →
    RunsIn [] kerP B (Function.update (Function.update (Function.update B (e .W0) (blkE x.2.1))
      (e .TR) restT) (e .TL) (x.2.2.reverse ++ B (e .TL))) Ck

theorem rowWork_spec {e : DS → K} (he : Function.Injective e) (kerP : BProg K R)
    (c0 c1 : List Sym) (Ck r : ℕ) (x : List (ℤ × ℤ) × List (ℤ × ℤ) × List Sym)
    (hx : x.1.length = r) (hker : KerOK e kerP c0 c1 Ck x) (restIN restT Q0 T0 RS0 : List Sym)
    (S : K → List Sym) (hIN : S (e .IN) = blkE x.1 ++ restIN) (hW : S (e .W0) = [])
    (hT : S (e .T) = Sym.mark :: T0) (hQ : S (e .Q) = Sym.mark :: Q0)
    (hRS : S (e .RS) = natSyms r ++ Sym.mark :: RS0) (hTR : S (e .TR) = x.2.2 ++ restT)
    (hC0 : S (e .C0) = c0) (hC1 : S (e .C1) = c1) :
    RunsIn [] (rowWork e kerP) S
      (Function.update (Function.update (Function.update (Function.update S (e .IN) restIN)
        (e .OUT) ((blkE x.2.1).reverse ++ S (e .OUT))) (e .TR) restT) (e .TL)
        (x.2.2.reverse ++ S (e .TL)))
      (Ck + 7 * bitLen r + 16 * r + 6 * (blkE x.1).length + 3 * (blkE x.2.1).length + 15) := by
  have r1 := lf_runs (R := R) (fetchRow_spec he r x.1 hx restIN Q0 T0 RS0 S hIN hW hT hQ hRS)
  set S1 := Function.update (Function.update S (e .IN) restIN) (e .W0) (blkE x.1) with hS1
  have r2 := hker S1 restT (by rw [hS1, Function.update_self])
    (by rw [hS1, Function.update_of_ne (he.ne (by decide)), Function.update_of_ne
      (he.ne (by decide)), hTR])
    (by rw [hS1, Function.update_of_ne (he.ne (by decide)), Function.update_of_ne
      (he.ne (by decide)), hC0])
    (by rw [hS1, Function.update_of_ne (he.ne (by decide)), Function.update_of_ne
      (he.ne (by decide)), hC1])
  set S2 := Function.update (Function.update (Function.update S1 (e .W0) (blkE x.2.1))
    (e .TR) restT) (e .TL) (x.2.2.reverse ++ S1 (e .TL)) with hS2
  have hS2W : S2 (e .W0) = blkE x.2.1 ++ [] := by
    rw [hS2, Function.update_of_ne (he.ne (by decide)), Function.update_of_ne (he.ne (by decide)),
      Function.update_self, List.append_nil]
  have r3 : RunsIn [] (lf (R := R) (moveAll (e .W0) (e .OUT))) S2
      (Function.update (Function.update S2 (e .W0) ([] : List Sym).tail) (e .OUT)
        ((blkE x.2.1).reverse ++ S2 (e .OUT))) (3 * (blkE x.2.1).length + 2) :=
    lf_runs (RunsIn.of_eval (f := fun _ => ([] : List Sym).head?) (fun v => moveAll_eval
      (he.ne (by decide)) [] v (blkE x.2.1) [] S2
      (isRecSym_of_mem_flatten recOK_of_mem_map) (fun d hd => by simp at hd) hS2W) le_rfl)
  refine RunsIn.of_eq (r1.seq (r2.seq r3)) ?_ (by omega)
  funext k
  simp only [hS2, hS1, Function.update_apply, List.tail_nil]
  split_ifs <;> simp_all [he.eq_iff]

#assert_std_axioms lf_closed fetchRow_closed rowWork_closed lf_runs lf_peek blkE_append
  blkE_eq_flatten recOK_of_mem_map fetchRow_spec rowWork_spec

end WP.W9c
