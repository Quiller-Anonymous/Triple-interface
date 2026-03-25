import Goldbach.ClosureBridgeScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
`Q0MinorAsymptoticCalibration` records the paper-facing asymptotic replacement for the old
finite-threshold calibration.

The intended regime is:

* `H(X) = (log X)^A`,
* `Q(X) = H(X)^γ`,
* `A ≥ 10`,
* `0 < γ < 1/2`.

For fixed ledger constants `C2`, `C3`, the minor-variance envelope

`C2 * sqrt(H(X) / X) + C3 / (H(X) * Q(X)^2)`

tends to `0` as `X → ∞`. Therefore for every fixed closure tolerance `ε > 0`, there exists a
threshold `X₀(A,γ,C2,C3,ε)` beyond which the closure inequality is satisfied.

This is the asymptotic calibration statement that matches the paper. It is deliberately separate
from the repository's fixed-`H = 10^4` workbench route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration

open scoped Topology

open Filter Asymptotics

noncomputable section

/-- Polylogarithmic window width `H(X) = (log X)^A`. -/
def polylogH (A : ℕ) (X : ℝ) : ℝ :=
  Real.log X ^ A

/-- The paper-style minor variance envelope. -/
def asymptoticVarianceEnvelope (A : ℕ) (γ C2 C3 : ℝ) (X : ℝ) : ℝ :=
  C2 * Real.sqrt (polylogH A X / X) +
    C3 / (Real.log X) ^ ((A : ℝ) * (1 + 2 * γ))

/-- Natural-input version of the asymptotic variance envelope. -/
def asymptoticVarianceEnvelopeNat (A : ℕ) (γ C2 C3 : ℝ) (X : ℕ) : ℝ :=
  asymptoticVarianceEnvelope A γ C2 C3 X

/--
Asymptotic calibration target: beyond some scale `X₀`, the paper-style variance envelope is at
most the desired closure tolerance `ε`.
-/
def AsymptoticCalibrationTarget (A : ℕ) (γ C2 C3 ε : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X → asymptoticVarianceEnvelopeNat A γ C2 C3 X ≤ ε

private theorem tendsto_polylog_over_id_atTop_zero (A : ℕ) :
    Tendsto (fun x : ℝ => polylogH A x / x) atTop (𝓝 0) := by
  simpa [polylogH] using (Real.isLittleO_pow_log_id_atTop (n := A)).tendsto_div_nhds_zero

private theorem tendsto_sqrt_polylog_over_id_atTop_zero (A : ℕ) :
    Tendsto (fun x : ℝ => Real.sqrt (polylogH A x / x)) atTop (𝓝 0) := by
  simpa [polylogH] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_polylog_over_id_atTop_zero A))

private theorem tendsto_inverse_log_rpow_atTop_zero
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (-s)) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop hs).comp Real.tendsto_log_atTop

private theorem tendsto_scaled_inverse_log_rpow_atTop_zero
    {s C : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => C * (Real.log x) ^ (-s)) atTop (𝓝 0) := by
  simpa using Tendsto.const_mul C (tendsto_inverse_log_rpow_atTop_zero hs)

private theorem tendsto_div_log_rpow_atTop_zero
    {s C3 : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => C3 / (Real.log x) ^ s) atTop (𝓝 0) := by
  have hmul :
      Tendsto (fun x : ℝ => C3 * (Real.log x) ^ (-s)) atTop (𝓝 0) :=
    tendsto_scaled_inverse_log_rpow_atTop_zero (C := C3) hs
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog_nonneg : 0 ≤ Real.log x := le_of_lt (Real.log_pos hx)
  rw [div_eq_mul_inv, Real.rpow_neg hlog_nonneg]

/--
For fixed constants and a paper-style polylogarithmic regime, the minor variance envelope tends to
`0`.
-/
theorem tendsto_asymptoticVarianceEnvelopeNat_atTop_zero
    {A : ℕ} {γ C2 C3 : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (_hC2 : 0 ≤ C2)
    (_hC3 : 0 ≤ C3) :
    Tendsto (fun X : ℕ => asymptoticVarianceEnvelopeNat A γ C2 C3 X) atTop (𝓝 0) := by
  let _ := hγhalf
  have hApos_nat : 0 < A := by
    omega
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast hApos_nat
  have hexpo : 0 < (A : ℝ) * (1 + 2 * γ) := by
    have hfac : 0 < 1 + 2 * γ := by linarith
    nlinarith
  have hfirst :
      Tendsto
        (fun x : ℝ => C2 * Real.sqrt (polylogH A x / x))
        atTop
        (𝓝 0) := by
    simpa using Tendsto.const_mul C2 (tendsto_sqrt_polylog_over_id_atTop_zero A)
  have hsecond :
      Tendsto
        (fun x : ℝ => C3 / (Real.log x) ^ ((A : ℝ) * (1 + 2 * γ)))
        atTop
        (𝓝 0) :=
    tendsto_div_log_rpow_atTop_zero (s := (A : ℝ) * (1 + 2 * γ)) (C3 := C3) hexpo
  have hsum :
      Tendsto (fun x : ℝ => asymptoticVarianceEnvelope A γ C2 C3 x) atTop (𝓝 0) := by
    simpa [asymptoticVarianceEnvelope] using hfirst.add hsecond
  exact hsum.comp tendsto_natCast_atTop_atTop

/--
Asymptotic calibration theorem: for every fixed closure tolerance `ε > 0`, there is a scale
threshold beyond which the paper-style variance envelope is below `ε`.
-/
theorem asymptoticCalibrationTarget_of_polylog_regime
    {A : ℕ} {γ C2 C3 ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hε : 0 < ε) :
    AsymptoticCalibrationTarget A γ C2 C3 ε := by
  have ht :
      Tendsto (fun X : ℕ => asymptoticVarianceEnvelopeNat A γ C2 C3 X) atTop (𝓝 0) :=
    tendsto_asymptoticVarianceEnvelopeNat_atTop_zero
      hA hγ0 hγhalf hC2 hC3
  have hEvent :
      ∀ᶠ X : ℕ in atTop, asymptoticVarianceEnvelopeNat A γ C2 C3 X < ε :=
    ht.eventually (Iio_mem_nhds hε)
  rw [Filter.eventually_atTop] at hEvent
  rcases hEvent with ⟨X₀, hX₀⟩
  exact ⟨X₀, fun {X} hX => le_of_lt (hX₀ X hX)⟩

end

end Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
