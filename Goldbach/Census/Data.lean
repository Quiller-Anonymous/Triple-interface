/-
  Goldbach/Census/Data.lean

  Canonical location for the analytic certificates produced by the AP census
  and the Gaussian completion analysis.  These numbers are currently recorded
  as Lean constants so that downstream projects (AltZeta, Goldbach, Twin) can
  share a single source of truth.  When the census pipeline emits data files,
  this module is the place where we parse/transfer those values.
-/
import Mathlib.Data.Real.Basic

namespace Goldbach
namespace Census

/-- Gaussian completion bound `C_Γ`.  Placeholder until the census pipeline
    emits the data file; sourced from the current analytic notes. -/
noncomputable def CGamma : ℝ := (1 : ℝ) / 4

@[simp] lemma CGamma_value : CGamma = (1 : ℝ) / 4 := rfl

lemma CGamma_nonneg : 0 ≤ CGamma := by
  simpa [CGamma_value] using (by norm_num : 0 ≤ (1 : ℝ) / 4)

/-- AP-census spectral envelope bound `S_cert`. -/
noncomputable def S_cert : ℝ := (1 : ℝ) / 10

@[simp] lemma S_cert_value : S_cert = (1 : ℝ) / 10 := rfl

lemma S_cert_nonneg : 0 ≤ S_cert := by
  simpa [S_cert_value] using (by norm_num : 0 ≤ (1 : ℝ) / 10)

end Census
end Goldbach
