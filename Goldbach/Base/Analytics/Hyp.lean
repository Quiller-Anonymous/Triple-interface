-- Goldbach/Analytic/Hyp.lean
-- Compatibility shim: re-export the canonical analytic hypothesis.
import Goldbach.AnalyticGlobal

namespace Goldbach.Analytic

abbrev AnalyticHyp (X0 H : ℕ) (S c0 ε : ℝ) :=
  Goldbach.AnalyticHyp X0 H S c0 ε

end Goldbach.Analytic
