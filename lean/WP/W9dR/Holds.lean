import WP.W9dR.Proof

/-!
# WP.W9dR.Holds — the contract `W9d_roundShift`

From the open W3 operations `addNat`, `subNat` (through `TMFw.W3b.W3_addInt_holds`), `shlVar`,
`shrVar`, `shrConst`, `dropNat` (hypotheses; discharged by the integrator). The proved contract
instances `w3_natToInt`, `w3_splitSign`, `w3_decNat`, `w3_incNat`, `w3_copyNat` are used
directly. The cost constant is `30·(C+1)` with `C` the sum of the instance constants.
-/

namespace WP.W9dR

open TMFw TMFw.Contracts Computability WP.W7k2

/-- **`W9d_roundShift` holds.** -/
theorem w9d_roundShift (haddN : W3_addNat) (hsubN : W3_subNat) (hshl : W3_shlVar)
    (hshr : W3_shrVar) (hshr1 : W3_shrConst) (hdrop : W3_dropNat) : W9d_roundShift := by
  obtain ⟨Cv, hv⟩ := exists_inst hshl
  obtain ⟨Iv, hIv⟩ := hv ()
  obtain ⟨Cr, hr⟩ := exists_inst hshr1
  obtain ⟨Ir, hIr⟩ := hr 1
  obtain ⟨Cn, hn⟩ := exists_inst w3_natToInt
  obtain ⟨In, hIn⟩ := hn ()
  obtain ⟨Ca, ha⟩ := exists_inst (TMFw.W3b.W3_addInt_holds haddN hsubN)
  obtain ⟨Ia, hIa⟩ := ha ()
  obtain ⟨Cg, hg⟩ := exists_inst w3_splitSign
  obtain ⟨Ig, hIg⟩ := hg ()
  obtain ⟨Cw, hw⟩ := exists_inst hshr
  obtain ⟨Iw, hIw⟩ := hw ()
  obtain ⟨Cd, hd⟩ := exists_inst w3_decNat
  obtain ⟨Id, hId⟩ := hd ()
  obtain ⟨Ci, hi⟩ := exists_inst w3_incNat
  obtain ⟨Ii, hIi⟩ := hi ()
  obtain ⟨Cc, hc⟩ := exists_inst w3_copyNat
  obtain ⟨Ic, hIc⟩ := hc ()
  obtain ⟨Cp, hp⟩ := exists_inst hdrop
  obtain ⟨Ip, hIp⟩ := hp ()
  obtain ⟨C, hC⟩ : ∃ C, C = Cv + Cr + Cn + Ca + Cg + Cw + Cd + Ci + Cc + Cp := ⟨_, rfl⟩
  have hJ : RSInst.Spec ⟨Iv, Ir, In, Ia, Ig, Iw, Id, Ii, Ic, Ip⟩ C :=
    ⟨fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (hIv a c rx rc S h1 h2 h3 h4)
        (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hIr a rx S h1 h2) (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hIn a rx S h1 h2) (by omega),
      fun a b rx ry S h1 h2 h3 h4 => Triple.cost_mono (hIa a b rx ry S h1 h2 h3 h4)
        (Nat.mul_le_mul_right _ (by omega)),
      fun z rx S h1 h2 => Triple.cost_mono (hIg z rx S h1 h2) (by omega),
      fun a c rx rc S h1 h2 h3 h4 => Triple.cost_mono (hIw a c rx rc S h1 h2 h3 h4)
        (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hId a rx S h1 h2) (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hIi a rx S h1 h2) (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hIc a rx S h1 h2) (Nat.mul_le_mul_right _ (by omega)),
      fun a rx S h1 h2 => Triple.cost_mono (hIp a rx S h1 h2) (Nat.mul_le_mul_right _ (by omega))⟩
  haveI := Iv.fin
  haveI := Ir.fin
  haveI := In.fin
  haveI := Ia.fin
  haveI := Ig.fin
  haveI := Iw.fin
  haveI := Id.fin
  haveI := Ii.fin
  haveI := Ic.fin
  haveI := Ip.fin
  haveI := Iv.ne
  haveI := Ir.ne
  haveI := In.ne
  haveI := Ia.ne
  haveI := Ig.ne
  haveI := Iw.ne
  haveI := Id.ne
  haveI := Ii.ne
  haveI := Ic.ne
  haveI := Ip.ne
  refine ⟨30 * (C + 1), fun _ => ⟨6, RSInst.Reg ⟨Iv, Ir, In, Ia, Ig, Iw, Id, Ii, Ic, Ip⟩,
    fun _ => (), rsProg ⟨Iv, Ir, In, Ia, Ig, Iw, Id, Ii, Ic, Ip⟩, le_rfl,
    (inferInstance : Finite (Iv.R × Ir.R × In.R × Ia.R × Ig.R × Iw.R × Id.R × Ii.R × Ic.R × Ip.R)),
    (inferInstance : Nonempty (Iv.R × Ir.R × In.R × Ia.R × Ig.R × Iw.R × Id.R × Ii.R × Ic.R ×
      Ip.R)), rsProg_closed _, ?_⟩⟩
  intro v s rx rc S hrx hrc ex ec
  exact HT.runs (rsProg_spec _ hJ v s rx rc S hrx hrc ex ec)

#assert_std_axioms w9d_roundShift

end WP.W9dR
