/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelKit

/-!
# C-core phase leaf, record-wise sign selection: the select loop (interface)

**Scope (honest summary).** Program definitions and one named statement, `SelLoopStmt`; nothing is
proved here. This is phase 3 of the kernel of `MaskSelStmt` (`LeafPhaseMaskSelDefs.lean`). The
parity table `G` is on `Tb` (entry `0` on top), `Gu` holds the used entries (reversed), `Sc`/`Su`
hold `S` `0` bits in total (a unary counter of the records of the current table entry). Per record
(`selBody`): read the current entry `g` (top of `Tb`); move the record of `Vn` (if `g`) or of `V`
(else) onto `Out` (`msMvRec`: it arrives as `sep :: bits.reverse`) and drop the other one; move one
bit `Sc → Su`; if `Sc` became empty, move the bits back (`Su → Sc`) and advance the table
(`Tb → Gu`), resetting it (`Gu → Tb`) when it is exhausted. The loop runs while `V` holds a record.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP

variable {K : Type}

/-- The symbol starts a record (a bit or `sep`). -/
def isRecO : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

/-- One record of the select loop. -/
def selBody (V Vn Out Tb Gu Sc Su : K) : PProg K :=
  .seq (.seq (peekT Tb) (.ite (fun v => bitOf v.t)
      (.seq (msMvRec Vn Out) (msDropRec V)) (.seq (msMvRec V Out) (msDropRec Vn))))
    (.seq (msLift (moveSym Sc Su))
      (.seq (peekT Sc) (.ite (fun v => isBitO v.t) msSkip
        (.seq (msLift (moveBlock Su Sc))
          (.seq (msLift (moveSym Tb Gu))
            (.seq (peekT Tb) (.ite (fun v => isBitO v.t) msSkip (msLift (moveBlock Gu Tb)))))))))

/-- **The select loop**: one `selBody` per record of `V`. -/
def selLoop (V Vn Out Tb Gu Sc Su : K) : PProg K :=
  .seq (peekT V) (.loop (fun v => isRecO v.t) (.seq (selBody V Vn Out Tb Gu Sc Su) (peekT V)))

/-- The content of `Out` after the select loop on the pairs `ps = v.zip vn`: record `j` is `vn_j`
if the table entry `(j div S) mod |G|` is set, else `v_j`; it is stored as `sep :: bits.reverse`,
the last record on top. -/
def selOut (G : List Bool) (S : ℕ) (ps : List (List Bool × List Bool)) : List Sym :=
  (ps.mapIdx fun j pr => Sym.sep ::
    ((if G.getD ((j / S) % G.length) false then pr.2 else pr.1).reverse.map Sym.bit)).reverse.flatten

/-- **[CONTRACT, machine] The select loop**, as `Runs`: `V`, `Vn` are consumed down to their
`BlkTerm` tails, `Out` (empty) receives `selOut G S (v.zip vn)`, the table and the counter are
left at position `N = |v|` (entry `(N div S) mod |G|` on top of `Tb`, `N mod S` bits on `Su`). -/
def SelLoopStmt : Prop :=
  ∀ {K : Type} [DecidableEq K] (V Vn Out Tb Gu Sc Su : K),
    List.Pairwise (· ≠ ·) [V, Vn, Out, Tb, Gu, Sc, Su] →
    ∀ (G : List Bool) (S : ℕ) (v vn : List (List Bool)) (rx rxn : List Sym) (St : K → List Sym),
      G ≠ [] → 1 ≤ S → v.length = vn.length → BlkTerm rx → BlkTerm rxn →
      St V = arrSyms v ++ rx → St Vn = arrSyms vn ++ rxn → St Out = [] →
      St Tb = G.map Sym.bit → St Gu = [] → St Sc = List.replicate S (Sym.bit false) →
      St Su = [] →
      Runs (selLoop V Vn Out Tb Gu Sc Su) St
        (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update St V rx) Vn rxn) Out (selOut G S (v.zip vn)))
          Tb ((G.drop ((v.length / S) % G.length)).map Sym.bit))
          Gu ((G.take ((v.length / S) % G.length)).reverse.map Sym.bit))
          Sc (List.replicate (S - v.length % S) (Sym.bit false)))
          Su (List.replicate (v.length % S) (Sym.bit false)))
        (fun _ => True) (4 * ((arrSyms v).length + (arrSyms vn).length) + 50 * v.length + 2)

end SubNLogN.Machine.CCore.PhaseMaskAux
