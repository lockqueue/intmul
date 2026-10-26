/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimGate
import SubNLogN.Math.Networks.AppCCounts

/-!
# Proposition A.7 network simulation, part 5: the network data (`AppC/C5NetSimData.lean`)

* `RawOp`: a schedule entry with its data inline (one stream op on a role, an XOR gate, a pivot call);
  `mkData` turns a raw schedule into the machine-level `NetData` (one singleton macro per stream entry, one
  gate per gate entry, plus the `pre`/`post` macros), and the list-level `runSched` of it is the fold of
  `RawOp.run` (`runSched_mkData`); call counts, validity of the macros and distinctness of the XOR
  ends transfer (`mkData_calls`, `mkData_ops_valid`, `mkData_gates_ne`).
* `mkData_pre` and `mkData_post` identify the outer `pre`/`post` macros of `mkData`, and `raws_eq_map`
  rewrites a raw schedule over `List.finRange` for `runSched_mkData` and `mkData_calls`.
* Node schedule and validity (split into `AppC/C5NetSimShape.lean` and `AppC/C5NetSimShape2.lean`):
  `rawMain fac` mirrors `bitNodeOps` (`forall₂_main` in `AppC/C5NetSimShape.lean`), and `rawMain_calls`
  (`tripleSb 100` calls under `InterchangeCallCountStmt`), `rawMain_valid` (`FacData.Valid`), and
  `rawMain_gates_ne` are proved in `AppC/C5NetSimShape2.lean`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp Op ProcK)

/-- A raw schedule entry. -/
inductive RawOp (W m : ℕ) where
  | stream (w : Fin W) (op : StreamOp m)
  | gate (xs : List (Fin W × Fin W))
  | call (w : Fin W) (i j : Fin m)

namespace RawOp

variable {W m : ℕ}

/-- Semantics of a raw entry (stream maps `sm`, child interchange maps `cm`). -/
def run (sm : StreamOp m → ℕ → ℕ) (cm : Fin m → Fin m → ℕ → ℕ) :
    RawOp W m → (Fin W → List (List Bool)) → Fin W → List (List Bool)
  | .stream w op, us => Function.update us w (permByInv (sm op) (us w))
  | .gate xs, us => gateApply xs us
  | .call w i j, us => Function.update us w (permByInv (cm i j) (us w))

def isCall : RawOp W m → Bool
  | .call .. => true
  | _ => false

def opsOf : RawOp W m → List (StreamOp m)
  | .stream _ op => [op]
  | _ => []

def gatesOf : RawOp W m → List (Fin W × Fin W)
  | .gate xs => xs
  | _ => []

def toSched {n : ℕ} (t : Fin n) : RawOp W m → SchedOp W m (Fin (n + 2)) (Fin n)
  | .stream w _ => .stream w ⟨t.val, by omega⟩
  | .gate _ => .gate t
  | .call w i j => .call w i j

end RawOp

/-- Machine-level network data of a raw schedule. -/
def mkData {W m : ℕ} (raws : List (RawOp W m)) (pre post : List (StreamOp m))
    (ρ : Equiv.Perm (Fin W)) : NetData W m where
  nOps := raws.length + 2
  ops o := if o.val < raws.length then (raws.getD o.val (.gate [])).opsOf
    else if o.val = raws.length then pre else post
  nG := raws.length
  gates g := (raws.getD g.val (.gate [])).gatesOf
  sched := (List.finRange raws.length).map fun t => (raws.getD t.val (.gate [])).toSched t
  pre := ⟨raws.length, by omega⟩
  post := ⟨raws.length + 1, by omega⟩
  ρ := ρ

section MkData

variable {W m : ℕ} (raws : List (RawOp W m)) (pre post : List (StreamOp m))
  (ρ : Equiv.Perm (Fin W))

theorem raws_eq_map : raws = (List.finRange raws.length).map fun t => raws.getD t.val (.gate []) := by
  conv_lhs => rw [← List.map_getElem_finRange raws]
  exact List.map_congr_left fun t _ => (List.getD_eq_getElem _ _ t.isLt).symm

theorem mkData_pre : (mkData raws pre post ρ).ops (mkData raws pre post ρ).pre = pre := by
  show (if raws.length < raws.length then _ else if raws.length = raws.length then pre else post) = _
  rw [if_neg (lt_irrefl _), if_pos rfl]

theorem mkData_post : (mkData raws pre post ρ).ops (mkData raws pre post ρ).post = post := by
  show (if raws.length + 1 < raws.length then _ else
    if raws.length + 1 = raws.length then pre else post) = _
  rw [if_neg (by omega), if_neg (by omega)]

theorem foldl_map_congr {α β γ : Type} (F : α → β → α) (G : α → γ → α) (f : γ → β) :
    ∀ (l : List γ) (a : α), (∀ a c, c ∈ l → F a (f c) = G a c) →
      List.foldl F a (l.map f) = List.foldl G a l
  | [], _, _ => rfl
  | c :: l, a, h => by
    simp only [List.map_cons, List.foldl_cons]
    rw [h a c (List.mem_cons_self ..)]
    exact foldl_map_congr F G f l _ fun a' c' hc' => h a' c' (List.mem_cons_of_mem _ hc')

theorem runSched_mkData (q k N1 G B : ℕ) (us : Fin W → List (List Bool)) :
    runSched q ((mkData raws pre post ρ).toNet q) k N1 G B (mkData raws pre post ρ).sched us =
      raws.foldl (fun us o => o.run (fun op => streamMap q m op k N1 G B)
        (fun i j => swapMap q m (k - 1) (cG q m k G i j) (cB q m k B j)) us) us := by
  unfold runSched
  conv_rhs => rw [raws_eq_map raws, List.foldl_map]
  show List.foldl _ us (List.map _ (List.finRange raws.length)) = _
  refine foldl_map_congr _ _ _ _ _ fun acc t _ => ?_
  obtain ⟨o, ho⟩ : ∃ o, raws.getD t.val (.gate []) = o := ⟨_, rfl⟩
  rw [ho]
  cases o with
  | stream w op =>
    have hops : (mkData raws pre post ρ).ops ⟨t.val, by show t.val < raws.length + 2; omega⟩ =
        [op] := by
      show (if t.val < raws.length then (raws.getD t.val (.gate [])).opsOf else _) = _
      rw [if_pos t.isLt, ho]
      rfl
    show Function.update acc w (permByInv (macroMap q m ((mkData raws pre post ρ).ops
      ⟨t.val, by show t.val < raws.length + 2; omega⟩) k N1 G B) (acc w)) = _
    rw [hops]
    rfl
  | gate xs =>
    show gateApply ((raws.getD t.val (.gate [])).gatesOf) acc = _
    rw [ho]
    rfl
  | call w i j => rfl

theorem mkData_calls :
    ((mkData raws pre post ρ).sched.filter SchedOp.isCall).length =
      (raws.filter RawOp.isCall).length := by
  show (((List.finRange raws.length).map fun t => (raws.getD t.val (.gate [])).toSched t).filter
    SchedOp.isCall).length = _
  conv_rhs => rw [raws_eq_map raws]
  rw [List.filter_map, List.length_map, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun t _ => ?_
  show SchedOp.isCall ((raws.getD t.val (.gate [])).toSched t) =
    RawOp.isCall (raws.getD t.val (.gate []))
  cases raws.getD t.val (.gate []) <;> rfl

theorem getD_mem_of_lt {n : ℕ} (h : n < raws.length) : raws.getD n (.gate []) ∈ raws := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem mkData_ops_valid (P : StreamOp m → Prop) (hraw : ∀ r ∈ raws, ∀ op ∈ r.opsOf, P op)
    (hpre : ∀ op ∈ pre, P op) (hpost : ∀ op ∈ post, P op) :
    ∀ o, ∀ op ∈ (mkData raws pre post ρ).ops o, P op := by
  intro o op hop
  change op ∈ (if o.val < raws.length then (raws.getD o.val (.gate [])).opsOf
    else if o.val = raws.length then pre else post) at hop
  split_ifs at hop with h1 h2
  · exact hraw _ (getD_mem_of_lt raws h1) op hop
  · exact hpre op hop
  · exact hpost op hop

theorem mkData_gates_ne (hraw : ∀ r ∈ raws, ∀ p ∈ r.gatesOf, p.1 ≠ p.2) :
    ∀ g, ∀ p ∈ (mkData raws pre post ρ).gates g, p.1 ≠ p.2 := fun g p hp =>
  hraw _ (getD_mem_of_lt raws g.isLt) p hp

end MkData

end SubNLogN.Machine.C5.NetAux
