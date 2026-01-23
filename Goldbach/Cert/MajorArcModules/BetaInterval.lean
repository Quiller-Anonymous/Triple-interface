import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Shared definitions for the β-interval used in the option-3 (TT*/Parseval) major-arc tail route.

Several modules (TT* interfaces, β-Fourier algebra, tail-energy bookkeeping) work on the fixed
interval `(-1/2, 1/2]` of length `1`.  To avoid proof-term mismatches (e.g. different `hab : a<b`
arguments to `fourierCoeffOn`), we centralize:

* `aβ = -1/2`, `bβ = 1/2`,
* `Iβ = Ioc aβ bβ`,
* basic algebraic facts: `aβ < bβ`, `bβ - aβ = 1`, `bβ = aβ + 1`.
-/

namespace Goldbach.Cert.MajorArcModules.BetaInterval

open scoped Interval

noncomputable section

abbrev aβ : ℝ := (-( (2 : ℝ)⁻¹) : ℝ)
abbrev bβ : ℝ := ((2 : ℝ)⁻¹ : ℝ)

abbrev Iβ : Set ℝ := Set.Ioc aβ bβ

lemma hab : aβ < bβ := by
  norm_num [aβ, bβ]

lemma hle : aβ ≤ bβ := le_of_lt hab

lemma measurableSet_Iβ : MeasurableSet Iβ := by
  simp [Iβ]

lemma bβ_eq_aβ_add_one : bβ = aβ + 1 := by
  norm_num [aβ, bβ]

lemma len_eq_one : (bβ - aβ : ℝ) = 1 := by
  norm_num [aβ, bβ]

lemma inv_len_eq_one : (bβ - aβ : ℝ)⁻¹ = 1 := by
  norm_num [aβ, bβ]

end

end Goldbach.Cert.MajorArcModules.BetaInterval
