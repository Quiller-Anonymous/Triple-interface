import Goldbach.Cert.SiegelWalfiszWeightedComplexAbsE

/-!
`MajorArcModules/PartialSummation` re-exports the discrete summation-by-parts infrastructure used
to turn ψ-bounds (or uniform `E(x)` bounds) into weighted exponential-sum bounds.

This is the “project-neutral” bridge: nothing here depends on σ, only on the AP partial sums.
-/

namespace Goldbach.Cert.MajorArcModules.PartialSummation

open Goldbach.Cert.SiegelWalfiszWeighted

noncomputable section

-- The main lemma we consume repeatedly (complex-valued weight, uniform `|E| ≤ M` on an interval).
abbrev norm_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform :=
  Goldbach.Cert.SiegelWalfiszWeighted.norm_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform

end

end Goldbach.Cert.MajorArcModules.PartialSummation

