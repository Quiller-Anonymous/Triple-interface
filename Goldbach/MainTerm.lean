import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Goldbach.SingularSeries

namespace Goldbach.MainTerm

open Goldbach.Singular

/-- Hardy–Littlewood main term using the singular series `sigma`. -/
noncomputable def M (C : C2Const) (n : ℕ) : ℝ :=
  sigma C n * (n : ℝ) / (Real.log (n : ℝ))^2

end Goldbach.MainTerm
