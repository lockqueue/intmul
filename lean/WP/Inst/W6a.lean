import WP.Inst.W3
import WP.W6a.DivRound

/-!
# WP.Inst.W6a — concrete instances of the W6a long-division contracts

Same convention as `WP.Inst.W3`. The dividers are W6a's programs over the W3 subtractor `WP.Inst.subNat`:

| contract | program | `m` | `R` | `C` |
|---|---|---|---|---|
| `W6a_divModNat` | `WP.W6a.divModProg subNat.prog` | 3 | `DReg subNat.R` | `2·20 + 70` |
| `W6a_divRound` | `WP.W6a.divRoundProg subNat.prog` | 4 | `RReg subNat.R` | `2·20 + 140` |

`subNat.subSpec` is the body of `W3_subNat` for `subNat.prog` (W6a's `SubSpec`); the `ok` theorems use it,
so they are proved for exactly these programs.
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts Computability

open WP.W3 in
/-- The `W3_subNat` body for `subNat.prog`, with `C = 20`. -/
theorem subNat.subSpec : WP.W6a.SubSpec 20 subNat.prog := by
  intro a b rx ry S hrx hry hab hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := addSubProg_eval subBit (encodeNat a) (encodeNat b) rx ry hrx hry S hx
    hy v
  have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
    rw [bitsVal_encodeNat, bitsVal_encodeNat]
    exact hab
  have hval : bitsVal (rip subBit (max (encodeNat a).length (encodeNat b).length) false
      (encodeNat a) (encodeNat b)) = a - b := by
    rw [bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

namespace divModNat
abbrev m : ℕ := 3
abbrev R : Type := WP.W6a.DReg subNat.R
def r0 : R := (none, false, (none, none, .eq), subNat.r0)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 4 m) (fun _ => Sym) R := WP.W6a.divModProg subNat.prog
theorem closed : prog.Closed := WP.W6a.divModProg_closed _ subNat.closed
end divModNat

theorem divModNat.ok : W6a_divModNat := by
  refine ⟨2 * 20 + 70, fun _ => ⟨3, WP.W6a.DReg subNat.R, fun _ => (), divModNat.prog, by decide,
    inferInstance, ⟨divModNat.r0⟩, divModNat.closed, ?_⟩⟩
  intro a b ra rb S hb hra hrb hA hB
  exact WP.W6a.divModProg_spec (by decide) subNat.subSpec a b ra rb S hb hra hrb hA hB

namespace divRound
abbrev m : ℕ := 4
abbrev R : Type := WP.W6a.RReg subNat.R
def r0 : R := (none, none, (none, none, .eq), (none, false, (none, none, .eq), subNat.r0))
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 3 m) (fun _ => Sym) R := WP.W6a.divRoundProg subNat.prog
theorem closed : prog.Closed := WP.W6a.divRoundProg_closed _ subNat.closed
end divRound

theorem divRound.ok : W6a_divRound := by
  refine ⟨2 * 20 + 140, fun _ => ⟨4, WP.W6a.RReg subNat.R, fun _ => (), divRound.prog, by decide,
    inferInstance, ⟨divRound.r0⟩, divRound.closed, ?_⟩⟩
  intro num den ra rb S hd hra hrb hN hD
  exact WP.W6a.divRoundProg_spec (by decide) subNat.subSpec num den ra rb S hd hra hrb hN hD

end WP.Inst
