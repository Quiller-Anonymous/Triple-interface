import Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
`Q0Band2ShellOrthogonalityProof` packages the Proposition 6.18 overlap story in the form that the
paper-facing asymptotic route actually needs.

Important correction:

* the current repo object `Band2ShellOrthogonality Δ_canon` is an **exact** vanishing statement;
* Proposition 6.18 is a **soft overlap bound** with a polylogarithmic loss.

So Proposition 6.18 does not honestly prove the existing exact `inner = 0` interface. What it does
prove is that the overlap factor contributes only an extra `polylogFactor(A,X)` in front of the
`sqrt(H/X)` term, and that this weighted term still tends to `0` in the polylogarithmic regime.

This file records precisely that asymptotic consequence.
-/

namespace Goldbach.Cert.MajorArcModules.Q0Band2ShellOrthogonalityProof

open scoped Topology

open Filter Asymptotics

noncomputable section

/-- Absolute overlap constant from Proposition 6.18. -/
axiom C_0 : ℝ

/-- Positivity of the Proposition 6.18 overlap constant. -/
axiom C_0_pos : 0 < C_0

/-- Abstract overlap constant for the band-2 tube family. -/
axiom tubOverlapConstant : ℕ → ℕ → ℝ

/-- Nonnegativity of the overlap constant. -/
axiom tubOverlapConstant_nonneg : ∀ A X : ℕ, 0 ≤ tubOverlapConstant A X

/-- Polylogarithmic window `H(X) = (log X)^A`, specialized to natural scales. -/
def logPow (A X : ℕ) : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A X

/--
A nonnegative polylogarithmic envelope for the Proposition 6.18 overlap factor.

We use `max 1 (1 + log H)` instead of bare `1 + log H` so the envelope is globally nonnegative.
This is asymptotically equivalent and avoids fake sign issues at small `X`.
-/
def polylogFactor (A X : ℕ) : ℝ :=
  max 1 (1 + Real.log (logPow A X))

/-- Square-function constant extracted from the overlap constant. -/
def squareFunctionConst (_K A X : ℕ) : ℝ :=
  Real.sqrt (tubOverlapConstant A X)

/--
Proposition 6.18 (`§6.5`): the overlap constant is bounded by an absolute shape constant times a
polylogarithmic factor.

This is the one genuine paper-facing analytic citation in this file.
-/
axiom prop618_overlap_bound (A : ℕ) (hA : 10 ≤ A) (X : ℕ) :
    tubOverlapConstant A X ≤ C_0 * polylogFactor A X

lemma squareFunction_K3_bound (A : ℕ) (hA : 10 ≤ A) (X : ℕ) :
    squareFunctionConst 3 A X ≤ Real.sqrt (C_0 * polylogFactor A X) := by
  unfold squareFunctionConst
  exact Real.sqrt_le_sqrt (prop618_overlap_bound A hA X)

lemma band2_enters_asymptoticC2 (A : ℕ) (γ : ℝ) (hA : 10 ≤ A) (hγ : 0 < γ ∧ γ < 1 / 2) :
    ∃ C_2 : ℝ, C_2 > 0 ∧
    ∀ X : ℕ, squareFunctionConst 3 A X ≤ C_2 * polylogFactor A X := by
  let C_2 : ℝ := max C_0 1
  refine ⟨C_2, ?_, ?_⟩
  · dsimp [C_2]
    positivity
  · intro X
    have hpf_one : (1 : ℝ) ≤ polylogFactor A X := by
      unfold polylogFactor
      exact le_max_left _ _
    have hpf_nonneg : 0 ≤ polylogFactor A X := le_trans (by norm_num) hpf_one
    have hsq := squareFunction_K3_bound A hA X
    have hC0_le : C_0 ≤ C_2 := by
      dsimp [C_2]
      exact le_max_left _ _
    have hsqrt_mono :
        Real.sqrt (C_0 * polylogFactor A X) ≤ Real.sqrt (C_2 * polylogFactor A X) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right hC0_le hpf_nonneg
    have hC2_nonneg : 0 ≤ C_2 := by
      dsimp [C_2]
      positivity
    have hbig_nonneg : 0 ≤ C_2 * polylogFactor A X := mul_nonneg hC2_nonneg hpf_nonneg
    have hbig_ge_one : (1 : ℝ) ≤ C_2 * polylogFactor A X := by
      have hC2_ge_one : (1 : ℝ) ≤ C_2 := by
        dsimp [C_2]
        exact le_max_right _ _
      have := mul_le_mul hC2_ge_one hpf_one (by positivity : 0 ≤ (1 : ℝ)) (by positivity)
      simpa using this
    have hsqrt_self : Real.sqrt (C_2 * polylogFactor A X) ≤ C_2 * polylogFactor A X := by
      nlinarith [Real.sq_sqrt hbig_nonneg, hbig_ge_one]
    exact le_trans hsq (le_trans hsqrt_mono hsqrt_self)

private lemma logPow_nonneg_of_two_le {A X : ℕ} (hX : 2 ≤ X) :
    0 ≤ logPow A X := by
  unfold logPow Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH
  have hlog_nonneg : 0 ≤ Real.log X := by
    have hX1 : 1 ≤ X := le_trans (by norm_num) hX
    exact Real.log_nonneg (by exact_mod_cast hX1)
  exact pow_nonneg hlog_nonneg A

private lemma polylogFactor_le_one_add_logPow {A X : ℕ} (hX : 2 ≤ X) :
    polylogFactor A X ≤ 1 + logPow A X := by
  unfold polylogFactor
  apply max_le
  · have hnonneg : 0 ≤ logPow A X := logPow_nonneg_of_two_le hX
    linarith
  · have hnonneg : 0 ≤ logPow A X := logPow_nonneg_of_two_le hX
    have hlog_le : Real.log (logPow A X) ≤ logPow A X := Real.log_le_self hnonneg
    linarith

private theorem tendsto_logPow_over_id_atTop_zero (A : ℕ) :
    Tendsto (fun x : ℝ => Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x / x)
      atTop (𝓝 0) := by
  simpa [Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH] using
    (Real.isLittleO_pow_log_id_atTop (n := A)).tendsto_div_nhds_zero

private theorem tendsto_logPow_cubed_over_id_atTop_zero (A : ℕ) :
    Tendsto
      (fun x : ℝ =>
        (Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x) ^ 3 / x)
      atTop (𝓝 0) := by
  simpa [Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH, ← pow_mul, Nat.mul_comm] using
    (Real.isLittleO_pow_log_id_atTop (n := 3 * A)).tendsto_div_nhds_zero

private theorem tendsto_sqrt_logPow_over_id_atTop_zero (A : ℕ) :
    Tendsto
      (fun x : ℝ =>
        Real.sqrt (Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x / x))
      atTop (𝓝 0) := by
  simpa using
    (Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_logPow_over_id_atTop_zero A))

private theorem tendsto_sqrt_logPow_cubed_over_id_atTop_zero (A : ℕ) :
    Tendsto
      (fun x : ℝ =>
        Real.sqrt
          ((Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x) ^ 3 / x))
      atTop (𝓝 0) := by
  simpa using
    (Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_logPow_cubed_over_id_atTop_zero A))

private theorem tendsto_polylogFactor_mul_sqrt_logPow_over_id_atTop_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ =>
        polylogFactor A x *
          Real.sqrt (logPow A x / x))
      atTop (𝓝 0) := by
  have hmain1 :
      Tendsto
        (fun x : ℕ =>
          Real.sqrt
            (Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x / x))
        atTop (𝓝 0) :=
    (tendsto_sqrt_logPow_over_id_atTop_zero A).comp tendsto_natCast_atTop_atTop
  have hmain2 :
      Tendsto
        (fun x : ℕ =>
          Real.sqrt
            ((Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A x) ^ 3 / x))
        atTop (𝓝 0) :=
    (tendsto_sqrt_logPow_cubed_over_id_atTop_zero A).comp tendsto_natCast_atTop_atTop
  have hupper :
      ∀ᶠ x : ℕ in atTop,
        polylogFactor A x * Real.sqrt (logPow A x / x)
          ≤ Real.sqrt (logPow A x / x) + Real.sqrt ((logPow A x) ^ 3 / x) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hlogpow_nonneg : 0 ≤ logPow A X := logPow_nonneg_of_two_le hX
    have hratio_nonneg : 0 ≤ logPow A X / X := by
      positivity
    have hfac :
        polylogFactor A X ≤ 1 + logPow A X :=
      polylogFactor_le_one_add_logPow hX
    have hmul :
        polylogFactor A X * Real.sqrt (logPow A X / X)
          ≤ (1 + logPow A X) * Real.sqrt (logPow A X / X) := by
      exact mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg _)
    have hsecond :
        logPow A X * Real.sqrt (logPow A X / X)
          = Real.sqrt ((logPow A X) ^ 3 / X) := by
      calc
        logPow A X * Real.sqrt (logPow A X / X)
            = Real.sqrt ((logPow A X) ^ 2) * Real.sqrt (logPow A X / X) := by
                rw [Real.sqrt_sq hlogpow_nonneg]
        _ = Real.sqrt (((logPow A X) ^ 2) * (logPow A X / X)) := by
              rw [← Real.sqrt_mul (by positivity : 0 ≤ (logPow A X) ^ 2)]
        _ = Real.sqrt ((logPow A X) ^ 3 / X) := by
              ring_nf
    calc
      polylogFactor A X * Real.sqrt (logPow A X / X)
          ≤ (1 + logPow A X) * Real.sqrt (logPow A X / X) := hmul
      _ = Real.sqrt (logPow A X / X) + logPow A X * Real.sqrt (logPow A X / X) := by ring
      _ = Real.sqrt (logPow A X / X) + Real.sqrt ((logPow A X) ^ 3 / X) := by rw [hsecond]
  have hnonneg :
      ∀ᶠ x : ℕ in atTop,
        0 ≤ polylogFactor A x * Real.sqrt (logPow A x / x) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hpf_nonneg : 0 ≤ polylogFactor A X := by
      unfold polylogFactor
      positivity
    exact mul_nonneg hpf_nonneg (Real.sqrt_nonneg _)
  have hsum :
      Tendsto
        (fun x : ℕ => Real.sqrt (logPow A x / x) + Real.sqrt ((logPow A x) ^ 3 / x))
        atTop (𝓝 0) := by
    simpa [logPow] using hmain1.add hmain2
  exact squeeze_zero' hnonneg hupper hsum

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

/-- Proposition-6.18-weighted asymptotic minor envelope. -/
def prop618AsymptoticEnvelope (A : ℕ) (γ C2 C3 : ℝ) (X : ℝ) : ℝ :=
  C2 * (1 + Real.log (Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A X)) *
      Real.sqrt (Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH A X / X) +
    C3 / (Real.log X) ^ ((A : ℝ) * (1 + 2 * γ))

/-- Natural-input version of the Proposition-6.18-weighted asymptotic envelope. -/
def prop618AsymptoticEnvelopeNat (A : ℕ) (γ C2 C3 : ℝ) (X : ℕ) : ℝ :=
  prop618AsymptoticEnvelope A γ C2 C3 X

/-- Eventual-`X₀` calibration target with the Proposition 6.18 overlap factor built in. -/
def Prop618AsymptoticCalibrationTarget (A : ℕ) (γ C2 C3 ε : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X → prop618AsymptoticEnvelopeNat A γ C2 C3 X ≤ ε

theorem tendsto_prop618AsymptoticEnvelopeNat_atTop_zero
    {A : ℕ} {γ C2 C3 : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (_hC2 : 0 ≤ C2)
    (_hC3 : 0 ≤ C3) :
    Tendsto (fun X : ℕ => prop618AsymptoticEnvelopeNat A γ C2 C3 X) atTop (𝓝 0) := by
  let _ := hA
  let _ := hγhalf
  have hfirst :
      Tendsto
        (fun X : ℕ =>
          C2 * (1 + Real.log (logPow A X)) * Real.sqrt (logPow A X / X))
        atTop (𝓝 0) := by
    have hpoly :
        Tendsto
          (fun X : ℕ =>
            C2 * (polylogFactor A X * Real.sqrt (logPow A X / X)))
          atTop (𝓝 0) := by
      simpa using Tendsto.const_mul C2 (tendsto_polylogFactor_mul_sqrt_logPow_over_id_atTop_zero A)
    have hcongr :
        (fun X : ℕ =>
          C2 * (1 + Real.log (logPow A X)) * Real.sqrt (logPow A X / X))
          =ᶠ[atTop]
        (fun X : ℕ =>
          C2 * (polylogFactor A X * Real.sqrt (logPow A X / X))) := by
      filter_upwards [eventually_ge_atTop 3] with X hX
      have hmax :
          polylogFactor A X = 1 + Real.log (logPow A X) := by
        unfold polylogFactor
        have hbound : 1 ≤ 1 + Real.log (logPow A X) := by
          have hlogpow_ge_one : 1 ≤ logPow A X := by
            have hlogX_ge_one : (1 : ℝ) ≤ Real.log X := by
              have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast (lt_trans (by norm_num) hX)
              have hX_ge_three : (3 : ℝ) ≤ X := by exact_mod_cast hX
              rw [Real.le_log_iff_exp_le hX_real_pos]
              exact le_trans (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) hX_ge_three
            have : (1 : ℝ) ≤ (Real.log X) ^ A := by
              exact one_le_pow₀ hlogX_ge_one
            simpa [logPow, Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.polylogH] using this
          have hlog_nonneg : 0 ≤ Real.log (logPow A X) := Real.log_nonneg hlogpow_ge_one
          linarith
        rw [max_eq_right hbound]
      rw [hmax]
      ring
    exact hpoly.congr' hcongr.symm
  have hexpo : 0 < (A : ℝ) * (1 + 2 * γ) := by
    have hApos : 0 < (A : ℝ) := by
      have : 0 < A := by omega
      exact_mod_cast this
    have hfac : 0 < 1 + 2 * γ := by linarith
    nlinarith
  have hsecond :
      Tendsto
        (fun X : ℕ => C3 / (Real.log X) ^ ((A : ℝ) * (1 + 2 * γ)))
        atTop (𝓝 0) := by
    exact (tendsto_div_log_rpow_atTop_zero (s := (A : ℝ) * (1 + 2 * γ)) (C3 := C3) hexpo).comp
      tendsto_natCast_atTop_atTop
  simpa [prop618AsymptoticEnvelopeNat, prop618AsymptoticEnvelope, logPow]
    using hfirst.add hsecond

theorem prop618AsymptoticCalibrationTarget_of_polylog_regime
    {A : ℕ} {γ C2 C3 ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hε : 0 < ε) :
    Prop618AsymptoticCalibrationTarget A γ C2 C3 ε := by
  have ht :
      Tendsto (fun X : ℕ => prop618AsymptoticEnvelopeNat A γ C2 C3 X) atTop (𝓝 0) :=
    tendsto_prop618AsymptoticEnvelopeNat_atTop_zero hA hγ0 hγhalf hC2 hC3
  have hEvent :
      ∀ᶠ X : ℕ in atTop, prop618AsymptoticEnvelopeNat A γ C2 C3 X < ε :=
    ht.eventually (Iio_mem_nhds hε)
  rw [Filter.eventually_atTop] at hEvent
  rcases hEvent with ⟨X₀, hX₀⟩
  exact ⟨X₀, fun {X} hX => le_of_lt (hX₀ X hX)⟩

/--
Asymptotic band-2/square-function input extracted from Proposition 6.18.

This is the honest replacement for the earlier idea of proving the exact proposition
`Band2ShellOrthogonality Δ_canon` from overlap geometry alone.
-/
theorem prop618_supplies_asymptotic_band2_square
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε) :
    ∃ C_2 : ℝ, C_2 > 0 ∧
      Prop618AsymptoticCalibrationTarget A γ C_2 1 ε := by
  rcases band2_enters_asymptoticC2 A γ hA ⟨hγ0, hγhalf⟩ with ⟨C₂, hC₂pos, _⟩
  refine ⟨C₂, hC₂pos, ?_⟩
  exact
    prop618AsymptoticCalibrationTarget_of_polylog_regime
      (A := A) (γ := γ) (C2 := C₂) (C3 := 1) (ε := ε)
      hA hγ0 hγhalf (le_of_lt hC₂pos) (by norm_num) hε

end

end Goldbach.Cert.MajorArcModules.Q0Band2ShellOrthogonalityProof
