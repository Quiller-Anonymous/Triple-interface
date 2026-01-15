import Goldbach.Cert.MajorArcNumericFacts

/-!
`MajorArcModules/NumericFacts` re-exports the tiny stable `Real.log` facts used by the
data-driven major-arc certificate route.
-/

namespace Goldbach.Cert.MajorArcModules.NumericFacts

export Goldbach.Cert.MajorArcNumericFacts
  (ten_le_log_X0 ten_le_log_of_X0_le thirteen_le_log_X0 thirteen_le_log_of_X0_le)

end Goldbach.Cert.MajorArcModules.NumericFacts
