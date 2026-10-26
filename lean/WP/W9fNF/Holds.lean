import WP.W9fNF.Main
import WP.W9fOps.ShrFloor
import Contracts.W9.Pipeline

/-!
# WP.W9fNF.Holds — `W9f_nyqFinish` from the frozen W3 contracts

The subroutines come from `W3_all`: `subInt`, `addInt`, `negInt`, and `shrVar`, which gives
W9fOps' signed floor shift (`WP.W9fOps.shrFloor_holds`). No other hypothesis is used.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- **W9f.nyqFinish** (the Nyquist finish of S2) from `W3_all`. -/
theorem W9f_nyqFinish_holds (h3 : W3_all) : WP.W9f.W9f_nyqFinish := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hshr, _, _, _, _, _, _, _, _, hneg, _, hadd, hsub, _, _⟩ :=
    h3
  obtain ⟨Cs, hs⟩ := hsub
  obtain ⟨ms, Rs, _, Psub, hms, _, _, hcs, hspecs⟩ := hs ()
  obtain ⟨Ca, ha⟩ := hadd
  obtain ⟨ma, Ra, _, Padd, hma, _, _, hca, hspeca⟩ := ha ()
  obtain ⟨Cn, hn⟩ := hneg
  obtain ⟨mn, Rn, _, Pneg, hmn, _, _, hcn, hspecn⟩ := hn ()
  obtain ⟨Cf, mf, Rf, Pshr, hmf, _, _, hcf, hspecf⟩ := WP.W9fOps.shrFloor_holds hshr
  let κ : Kit := ⟨ms, ma, mn, mf, Rs, Ra, Rn, Rf, by omega, by omega, by omega, hmf, Psub, Padd,
    Pneg, Pshr⟩
  have hκ : κ.OK Cs Ca Cn Cf := ⟨hspecs, hspeca, hspecn, hspecf⟩
  refine ⟨24 * Cs + 32 * Ca + 8 * Cn + 32 * Cf + 1000, fun _ => ⟨24, κ.Reg, fun _ => (),
    finishProg κ, by norm_num, inferInstance, inferInstance, finishProg_closed κ hcs hca hcn hcf,
    ?_⟩⟩
  intro H k alt Z rZ r2 r3 S hsize hk hW halt hrZ hr2 hZ hK hAL
  exact finish_runs hκ H k alt Z rZ r2 r3 S hsize hk hW halt hrZ hr2 hZ hK hAL

#assert_std_axioms W9f_nyqFinish_holds

end WP.W9fNF
