/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseBase

/-!
# C-core leaves 8/10: reading the descriptor (`CCore/LeafPhaseHdr.lean`)

**Scope (honest summary).** Scratch-only programs on the work layout `Lw` (`LeafPhaseBase.lean`)
with exact `Runs` facts, everything proved:
* `readHdr`: copy the call descriptor `t.hdr` (on top of `desc`, `CCoreRT.hdr`,
  `Contracts/CCore.lean:152`) to the scratch stack `H` with `Calculus.copyHdr 12`, then process its
  twelve fields in order (`rdFields hdrActs`): eight go to counter stacks (`natSyms f ++ [mark]`),
  four are dropped — count-controlled, field by field, never a header-wide mark scan; `desc` is
  restored. Its exact run `runs_readHdr` is in `LeafPhaseCore.lean`.
* `runs_rdFields`: the generic field-distribution lemma (`storeF`, `rdCost`).
-/
namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

/-! ## Fields and actions -/

/-- The descriptor fields of a call, in descriptor order (`CCoreRT.hdr`). -/
def hdrFields (t : CCoreRT) : List ℕ := [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ]

theorem hdr_eq (t : CCoreRT) : t.hdr = W9.hdrSyms (hdrFields t) := rfl

/-- Where each field goes: `P ↦ cP`, `Δ ↦ cDl`, `K ↦ cK`, `D ↦ cDD`, `S ↦ cS`, `j0 ↦ cJ`,
`k ↦ cKk`, `ρ ↦ cRho`; `d, r, A, R` are dropped. -/
def hdrActs : List (Option PS) :=
  [some .cP, none, none, some .cDl, none, none, some .cK, some .cDD, some .cS, some .cJ, some .cKk,
    some .cRho]

variable {Er : Type}

/-- Process one field of the header copy on `H`: drop it, or move it to the counter `c`. -/
def rdField (a : Option PS) : SProg (Lw Er) :=
  match a with
  | none => dropField (wS .H)
  | some c => .seq (moveFieldTo (wS .H) (wS .Ht)) (moveFieldBack (wS .Ht) (wS c))

/-- Process fields in order. -/
def rdFields : List (Option PS) → SProg (Lw Er)
  | [] => skip
  | a :: as => .seq (rdField a) (rdFields as)

/-- **Read the descriptor**: copy it to `H`, then distribute its fields. -/
def readHdr : SProg (Lw Er) := .seq (copyHdr 12 wD (wS .H) (wS .Ht)) (rdFields hdrActs)

theorem closed_rdField (a : Option PS) : (rdField (Er := Er) a).Closed := by
  cases a with
  | none => exact closed_dropField _
  | some c => exact ⟨closed_moveFieldTo _ _, closed_moveFieldBack _ _⟩

theorem closed_rdFields : ∀ as : List (Option PS), (rdFields (Er := Er) as).Closed
  | [] => by simp [rdFields, skip, Prog.Closed, Prog.FreeBelow]
  | a :: as => ⟨closed_rdField a, closed_rdFields as⟩

theorem closed_readHdr : (readHdr (Er := Er)).Closed :=
  ⟨closed_copyHdr _ _ _ _, closed_rdFields _⟩

/-- The counters after storing fields. -/
def storeF (sc : PS → List Sym) : List (Option PS) → List ℕ → PS → List Sym
  | a :: as, f :: fs => storeF (match a with
      | none => sc
      | some c => Function.update sc c (natSyms f ++ Sym.mark :: sc c)) as fs
  | _, _ => sc

/-- The cost of `rdFields`. -/
def rdCost : List (Option PS) → List ℕ → ℕ
  | a :: as, f :: fs => (match a with
      | none => 2 * bitLen f + 5
      | some _ => 6 * bitLen f + 12) + rdCost as fs
  | _, _ => 1

theorem storeF_update_ne (p : PS) (v : List Sym) :
    ∀ (as : List (Option PS)) (fs : List ℕ) (sc : PS → List Sym), (∀ c, some c ∈ as → c ≠ p) →
      storeF (Function.update sc p v) as fs = Function.update (storeF sc as fs) p v
  | [], _, _, _ => by simp [storeF]
  | _ :: _, [], _, _ => by simp [storeF]
  | none :: as, f :: fs, sc, h => by
    simp only [storeF]
    exact storeF_update_ne p v as fs sc (fun c hc => h c (List.mem_cons_of_mem _ hc))
  | some c :: as, f :: fs, sc, h => by
    simp only [storeF]
    have hcp : c ≠ p := h c List.mem_cons_self
    rw [Function.update_of_ne hcp, Function.update_comm (Ne.symm hcp)]
    exact storeF_update_ne p v as fs _ (fun c hc => h c (List.mem_cons_of_mem _ hc))

variable [DecidableEq Er]

theorem runs_rdFields (d : List Sym) (er : Er → List Sym) :
    ∀ (as : List (Option PS)) (fs : List ℕ) (sc : PS → List Sym) (tl : List Sym),
      as.length = fs.length → (∀ c, some c ∈ as → c ≠ .H ∧ c ≠ .Ht) →
      sc .H = W9.hdrSyms fs ++ tl → TermOK (sc .Ht) →
      Runs (rdFields as) (wst d sc er) (wst d (Function.update (storeF sc as fs) .H tl) er)
        (fun _ => True) (rdCost as fs)
  | [], [], sc, tl, _, _, hH, _ => by
    have hH' : sc .H = tl := by simpa [Calculus.HdrAux.hdrSyms_nil] using hH
    have : Function.update (storeF sc [] []) .H tl = sc := by
      simp only [storeF]; rw [← hH', Function.update_eq_self]
    rw [this]
    refine Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v _, trivial, le_rfl⟩
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | a :: as, f :: fs, sc, tl, hlen, hne, hH, hHt => by
    have hlen' : as.length = fs.length := by simpa using hlen
    have hne' : ∀ c, some c ∈ as → c ≠ .H ∧ c ≠ .Ht := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    have hH1 : sc .H = natSyms f ++ Sym.mark :: (W9.hdrSyms fs ++ tl) := by
      rw [hH, Calculus.HdrAux.hdrSyms_cons, List.append_assoc]; rfl
    cases a with
    | none =>
      have h1 := runs_dropField (wS (Er := Er) .H) f (W9.hdrSyms fs ++ tl) (wst d sc er) hH1
      rw [update_wst_S] at h1
      have h2 := runs_rdFields d er as fs (Function.update sc .H (W9.hdrSyms fs ++ tl)) tl hlen'
        hne' (by simp) (by simpa [Function.update_apply] using hHt)
      rw [storeF_update_ne .H _ as fs sc (fun c hc => (hne' c hc).1), Function.update_idem] at h2
      exact WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ h => h)
        (by simp only [rdCost]; omega)
    | some c =>
      obtain ⟨hcH, hcHt⟩ := hne c List.mem_cons_self
      have h1 := runs_moveFieldTo (d := wS (Er := Er) .H) (t := wS .Ht) (by simp) f
        (W9.hdrSyms fs ++ tl) (wst d sc er) hH1
      rw [update_wst_S, update_wst_S] at h1
      have hne2 : wS (Er := Er) .Ht ≠ wS c := by
        intro h; apply hcHt; simp only [wS, Sum.inl.injEq, Option.some.injEq] at h; exact h.symm
      have h2 := runs_moveFieldBack (t := wS (Er := Er) .Ht) (d := wS c) hne2 f
        (sc .Ht) (wst d (Function.update (Function.update sc .H (W9.hdrSyms fs ++ tl)) .Ht
          (fieldRev f ++ sc .Ht)) er) hHt (by simp [Function.update_apply])
      simp only [update_wst_S, wst_S] at h2
      rw [Function.update_of_ne hcHt, Function.update_of_ne hcH] at h2
      have h3 := runs_rdFields d er as fs
        (Function.update (Function.update (Function.update (Function.update sc .H
          (W9.hdrSyms fs ++ tl)) .Ht (fieldRev f ++ sc .Ht)) .Ht (sc .Ht)) c
          (natSyms f ++ Sym.mark :: sc c)) tl hlen' hne'
        (by simp [Function.update_apply, Ne.symm hcH])
        (by simpa [Function.update_apply, Ne.symm hcHt] using hHt)
      have e : Function.update (storeF (Function.update (Function.update (Function.update
          (Function.update sc .H (W9.hdrSyms fs ++ tl)) .Ht (fieldRev f ++ sc .Ht)) .Ht (sc .Ht)) c
          (natSyms f ++ Sym.mark :: sc c)) as fs) .H tl =
          Function.update (storeF sc (some c :: as) (f :: fs)) .H tl := by
        simp only [storeF]
        have k1 : Function.update (Function.update (Function.update sc .H (W9.hdrSyms fs ++ tl))
            .Ht (fieldRev f ++ sc .Ht)) .Ht (sc .Ht) = Function.update sc .H (W9.hdrSyms fs ++ tl) := by
          rw [Function.update_idem, Function.update_eq_self_iff,
            Function.update_of_ne (by decide : PS.Ht ≠ PS.H)]
        rw [k1, Function.update_comm (Ne.symm hcH),
          storeF_update_ne .H _ as fs _ (fun c hc => (hne' c hc).1), Function.update_idem]
      rw [e] at h3
      exact WP.W9comp.runs_mono (WP.W9comp.runs_seq (WP.W9comp.runs_seq h1 h2) h3) (fun _ h => h)
        (by simp only [rdCost]; omega)

end SubNLogN.Machine.CCore.LeafScalarAux
