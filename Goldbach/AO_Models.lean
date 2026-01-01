import Mathlib
import Goldbach.AO_SigmaPos
import Goldbach.AO_Major

namespace Goldbach.AO_Models

open Goldbach

/-- Reference model: infinite kernel, full Mellin, no smoothing. -/
noncomputable def M_infInf_raw (X N : ℕ) : ℝ :=
  Goldbach.AO_Major.sigma N * Goldbach.AO_Major.weight_mass X

/-- Infinite kernel, full Mellin, smoothed (placeholder for now). -/
noncomputable def M_infInf_sm (_X _N : ℕ) : ℝ := 0

/-- Infinite kernel, Mellin truncated at T, smoothed (placeholder for now). -/
noncomputable def M_infT_sm (_X _N : ℕ) : ℝ := 0

/-- Kernel truncated at H, Mellin truncated at T, smoothed (placeholder for now). -/
noncomputable def M_HT_sm (_X _N : ℕ) : ℝ := 0

end Goldbach.AO_Models
